import asyncio
import json
import os
import logging
import re
import time
import shutil
import humanize
import math
import spotipy
from spotipy.oauth2 import SpotifyClientCredentials
from pathlib import Path
from datetime import datetime, timedelta
from concurrent.futures import ThreadPoolExecutor
import yt_dlp
from pyrogram import Client, filters, enums
from pyrogram.types import InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo, CallbackQuery, InputMediaVideo, InputMediaPhoto, Message
import aiohttp
from collections import deque, defaultdict
from functools import partial
from typing import Dict, Optional, Tuple, List, Any
import cv2
from PIL import Image
from urllib.parse import unquote
from dataclasses import dataclass
from youtubesearchpython.__future__ import VideosSearch
from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram.types import Message, InlineKeyboardMarkup
from pyrogram.errors import FloodWait, InputUserDeactivated, UserIsBlocked, PeerIdInvalid
import asyncio

# Setup logging
logging.basicConfig(
    level=logging.ERROR,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)
yt_dlp.utils.bug_reports_message = lambda: ''
logging.getLogger('yt_dlp').setLevel(logging.CRITICAL)

# Configure your API credentials
API_ID = "Your_API_ID"
API_HASH = "API_HASH"
BOT_TOKEN = "BOT TOKEN"
LOG_GROUP_ID = -1001806351030  # Replace with your logging group ID
OWNER_USERNAME = "@Hmm_Smokie"
SPOTIFY_CLIENT_ID = 'SPOTIFY CLIENT ID'
SPOTIFY_CLIENT_SECRET = 'SPOTIFY CLIENT SECRET'
GENIUS_TOKEN = 'GENIUS TOKEN FOR LYRICS'
RAPID_API_KEY = 'fOR INSTA SCRAP NEED KEY'
RAPID_API_URL = "FOR INSTA SCRAP NEED URL"

# MongoDB Configuration
MONGO_URI = "MONGO URL"
DB_NAME = "Downloader"
USERS_COLLECTION = "users"

# Terabox Configuration
WEBAPP_URL = "MINI APP URL"
TERABOX_IMAGE = "https://cdn.glitch.global/37127bbb-2499-443c-9bec-47899afdad04/photo_2024-12-20_23-41-03.jpg?v=1734718281072"
NONVEG_IMAGE = "https://cdn.glitch.global/37127bbb-2499-443c-9bec-47899afdad04/photo_2024-12-21_00-00-51.jpg?v=1734719485408"
TERABOX_API_URL = "API NEED FOR TERABOX"
RAPIDAPI_KEY = "TERABOX API"
RAPIDAPI_HOST = "HOST FOR TERABOX"


# Constants
MAX_CONCURRENT_DOWNLOADS = 1000
MAX_CONCURRENT_UPLOADS = 1000
TEMP_DIR = Path("temp")
RATE_LIMIT_MESSAGES = 500
RATE_LIMIT_WINDOW = 1
YT_COOKIES_PATH = "cookies.txt"

PINTEREST_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
    'Accept-Language': 'en-US,en;q=0.5',
    'Connection': 'keep-alive',
    'Referer': 'https://www.pinterest.com/',
}
PINTEREST_DOWNLOAD_TIMEOUT = 60
PINTEREST_MAX_RETRIES = 3

class TelegramLogger:
    def __init__(self, bot_client, log_group_id):
        self.bot = bot_client
        self.log_group_id = log_group_id
        
    async def log_bot_start(self, user_id, username, first_name):
        """Log when a user starts the bot"""
        user_mention = f"[{first_name}](tg://user?id={user_id})"
        log_text = (
            f"👤 {user_mention} ᴊᴜsᴛ sᴛᴀʀᴛᴇᴅ ᴛʜᴇ ʙᴏᴛ\n\n"
            f"🆔 ᴜsᴇʀ ɪᴅ : `{user_id}`\n"
            f"👾 ᴜsᴇʀɴᴀᴍᴇ : @{username}" if username else "None"
        )
        await self.bot.send_message(self.log_group_id, log_text)
        
    async def log_user_action(self, user_id, username, first_name, action_type, query=""):
        """Log user actions (downloads, searches, etc.)"""
        user_mention = f"[{first_name}](tg://user?id={user_id})"
        action_types = {
            "spotify": "🎵 Spotify Download",
            "spotify_list": "🎼 Spotify Artist List",
            "facebook": "📘 Facebook Download",
            "twitter": "🐦 Twitter Download",
            "youtube": "📺 YouTube Download",
            "youtube_audio": "🎧 YouTube Audio Download",
            "instagram": "📸 Instagram Download",
            "terabox": "📦 TeraBox Download",
            "pinterest": "📌 Pinterest Download",
            "nonveg_reels": "🎬 Special Reels",
            "audio": "🎧 Audio Download"
        }
        
        action_name = action_types.get(action_type, "🔍 Unknown Action")
        log_text = (
            f"⚡️ **New Request**\n\n"
            f"👤 **User:** {user_mention}\n"
            f"🎯 **Action:** {action_name}\n"
            f"🔍 **Query:** `{query}`\n"
            f"🆔 **User ID:** `{user_id}`\n"
            f"👾 **Username:** @{username}" if username else "None"
        )
        await self.bot.send_message(self.log_group_id, log_text)

@dataclass
class PinterestMedia:
    url: str
    media_type: str
    width: int = 0
    height: int = 0
    fallback_urls: list = None

    def __post_init__(self):
        if self.fallback_urls is None:
            self.fallback_urls = []

class AsyncPool:
    def __init__(self, max_workers):
        self.semaphore = asyncio.Semaphore(max_workers)
        self.tasks = set()

    async def spawn(self, coro):
        async with self.semaphore:
            task = asyncio.create_task(coro)
            self.tasks.add(task)
            try:
                return await task
            finally:
                self.tasks.remove(task)

class PinterestDownloader:
    def __init__(self):
        self.session = None
        self.pin_patterns = [r'/pin/(\d+)', r'pin/(\d+)', r'pin_id=(\d+)']
        self.download_pool = AsyncPool(MAX_CONCURRENT_DOWNLOADS)
        self.file_pool = ThreadPoolExecutor(max_workers=MAX_CONCURRENT_DOWNLOADS)

    async def init_session(self):
        if not self.session:
            timeout = aiohttp.ClientTimeout(total=PINTEREST_DOWNLOAD_TIMEOUT)
            self.session = aiohttp.ClientSession(headers=PINTEREST_HEADERS, timeout=timeout)

    async def close(self):
        if self.session:
            await self.session.close()
            self.session = None
        self.file_pool.shutdown(wait=True)

    async def extract_pin_id(self, url: str) -> Optional[str]:
        """Extract Pinterest pin ID from URL with retry logic"""
        await self.init_session()
        
        for attempt in range(PINTEREST_MAX_RETRIES):
            try:
                if 'pin.it' in url:
                    async with self.session.head(url, allow_redirects=True) as response:
                        url = str(response.url)
                
                for pattern in self.pin_patterns:
                    if match := re.search(pattern, url):
                        return match.group(1)
                return None
            except Exception as e:
                if attempt == PINTEREST_MAX_RETRIES - 1:
                    logger.error(f"Failed to extract pin ID after {PINTEREST_MAX_RETRIES} attempts: {e}")
                    raise
                await asyncio.sleep(1)

    async def download_file(self, url: str, file_path: Path) -> bool:
        """Download file with retry logic"""
        for attempt in range(PINTEREST_MAX_RETRIES):
            try:
                async with self.session.get(url) as response:
                    if response.status == 200:
                        # Use ThreadPoolExecutor for file I/O
                        content = await response.read()
                        await asyncio.get_event_loop().run_in_executor(
                            self.file_pool,
                            self._write_file,
                            file_path,
                            content
                        )
                        return True
            except Exception as e:
                if attempt == PINTEREST_MAX_RETRIES - 1:
                    logger.error(f"Failed to download file after {PINTEREST_MAX_RETRIES} attempts: {e}")
                    return False
                await asyncio.sleep(1)
        return False
    
    @staticmethod
    def _write_file(file_path: Path, content: bytes):
        """Write file to disk (runs in thread pool)"""
        with open(file_path, 'wb') as f:
            f.write(content)

    def get_highest_quality_image(self, image_url: str) -> str:
        """Convert image URL to highest quality version"""
        url = re.sub(r'/\d+x/|/\d+x\d+/', '/originals/', image_url)
        url = re.sub(r'\?.+$', '', url)
        return url

    async def get_pin_data(self, pin_id: str) -> Optional[PinterestMedia]:
        """Get pin data using webpage method"""
        try:
            return await self.get_data_from_webpage(pin_id)
        except Exception as e:
            logger.error(f"Error getting pin data: {e}")
            return None

    async def get_data_from_api(self, pin_id: str) -> Optional[PinterestMedia]:
        """Get highest quality image data from Pinterest's API"""
        api_url = f"https://api.pinterest.com/v3/pidgets/pins/info/?pin_ids={pin_id}"
        
        async with self.session.get(api_url) as response:
            if response.status == 200:
                data = await response.json()
                if pin_data := data.get('data', [{}])[0].get('pin'):
                    if videos := pin_data.get('videos', {}).get('video_list', {}):
                        video_formats = list(videos.values())
                        if video_formats:
                            best_video = max(video_formats, key=lambda x: x.get('width', 0) * x.get('height', 0))
                            return PinterestMedia(
                                url=best_video.get('url'),
                                media_type='video',
                                width=best_video.get('width', 0),
                                height=best_video.get('height', 0)
                            )
                    
                    if images := pin_data.get('images', {}):
                        if orig_image := images.get('orig'):
                            image_url = self.get_highest_quality_image(orig_image.get('url'))
                            return PinterestMedia(
                                url=image_url,
                                media_type='image',
                                width=orig_image.get('width', 0),
                                height=orig_image.get('height', 0)
                            )
        return None

    async def get_data_from_webpage(self, pin_id: str) -> Optional[PinterestMedia]:
        """Get media data from webpage with enhanced parsing"""
        url = f"https://www.pinterest.com/pin/{pin_id}/"
        
        async with self.session.get(url) as response:
            if response.status == 200:
                text = await response.text()
                
                video_matches = re.findall(r'"url":"([^"]*?\.mp4[^"]*)"', text)
                if video_matches:
                    video_url = unquote(video_matches[0].replace('\\/', '/'))
                    return PinterestMedia(
                        url=video_url,
                        media_type='video'
                    )

                image_patterns = [
                    r'<meta property="og:image" content="([^"]+)"',
                    r'"originImageUrl":"([^"]+)"',
                    r'"image_url":"([^"]+)"',
                ]
                
                for pattern in image_patterns:
                    if matches := re.findall(pattern, text):
                        for match in matches:
                            image_url = unquote(match.replace('\\/', '/'))
                            if any(ext in image_url.lower() for ext in ['.jpg', '.jpeg', '.png', '.webp']):
                                return PinterestMedia(
                                    url=self.get_highest_quality_image(image_url),
                                    media_type='image'
                                )
                
                json_pattern = r'<script[^>]*?>\s*?({.+?})\s*?</script>'
                for json_match in re.finditer(json_pattern, text):
                    try:
                        data = json.loads(json_match.group(1))
                        if isinstance(data, dict):
                            def find_image_url(d):
                                if isinstance(d, dict):
                                    for k, v in d.items():
                                        if isinstance(v, str) and any(ext in v.lower() for ext in ['.jpg', '.jpeg', '.png', '.webp']):
                                            return v
                                        elif isinstance(v, (dict, list)):
                                            result = find_image_url(v)
                                            if result:
                                                return result
                                elif isinstance(d, list):
                                    for item in d:
                                        result = find_image_url(item)
                                        if result:
                                            return result
                                return None

                            if image_url := find_image_url(data):
                                return PinterestMedia(
                                    url=self.get_highest_quality_image(image_url),
                                    media_type='image'
                                )
                    except json.JSONDecodeError:
                        continue

        return None

    async def get_data_from_mobile_api(self, pin_id: str) -> Optional[PinterestMedia]:
        """Get highest quality media from mobile API"""
        mobile_api_url = f"https://www.pinterest.com/_ngapi/pins/{pin_id}"
        
        headers = {**PINTEREST_HEADERS, 'Accept': 'application/json'}
        async with self.session.get(mobile_api_url, headers=headers) as response:
            if response.status == 200:
                try:
                    data = await response.json()
                    
                    if video_data := data.get('videos', {}).get('video_list', {}):
                        best_video = max(
                            video_data.values(),
                            key=lambda x: x.get('width', 0) * x.get('height', 0)
                        )
                        if 'url' in best_video:
                            return PinterestMedia(
                                url=best_video['url'],
                                media_type='video',
                                width=best_video.get('width', 0),
                                height=best_video.get('height', 0)
                            )
                    
                    if image_data := data.get('images', {}):
                        if orig_image := image_data.get('orig'):
                            image_url = self.get_highest_quality_image(orig_image.get('url'))
                            return PinterestMedia(
                                url=image_url,
                                media_type='image',
                                width=orig_image.get('width', 0),
                                height=orig_image.get('height', 0)
                            )
                except json.JSONDecodeError:
                    pass
        
        return None

class MediaProcessor:
    def __init__(self, session):
        self.session = session
        self.active_downloads = defaultdict(set)
        self.active_uploads = defaultdict(set)

    @staticmethod
    async def run_in_thread(func, *args):
        loop = asyncio.get_event_loop()
        return await loop.run_in_executor(ThreadPoolExecutor(max_workers=10), func, *args)

    async def download_file(self, url, filename):
        async with asyncio.Semaphore(MAX_CONCURRENT_DOWNLOADS):
            try:
                async with self.session.get(url) as response:
                    if response.status != 200:
                        return None
                    
                    with open(filename, 'wb') as f:
                        async for chunk in response.content.iter_chunked(8192):
                            f.write(chunk)
                return filename
            except Exception as e:
                logger.error(f"Download error: {e}")
                return None

    async def validate_and_process_media(self, media_info, default_caption='📸 Instagram Media', prefix='temp'):
        try:
            media_type = media_info.get('type')
            download_url = media_info.get('download_url')
            
            ext = {'video': 'mp4', 'image': 'jpg'}.get(media_type, 'media')
            temp_filename = os.path.join(TEMP_DIR, f"{prefix}.{ext}")
            
            if not await self.download_file(download_url, temp_filename):
                return None

            if media_type == 'video':
                return await self._validate_video(temp_filename, media_info, default_caption)
            elif media_type == 'image':
                return await self._validate_image(temp_filename, media_info, default_caption)
            
        except Exception as e:
            logger.error(f"Media processing error: {e}")
            return None

    async def _validate_video(self, filename, media_info, default_caption):
        def _check_video(filename):
            video = cv2.VideoCapture(filename)
            width = int(video.get(cv2.CAP_PROP_FRAME_WIDTH))
            height = int(video.get(cv2.CAP_PROP_FRAME_HEIGHT))
            fps = video.get(cv2.CAP_PROP_FPS)
            duration = video.get(cv2.CAP_PROP_FRAME_COUNT) / fps if fps > 0 else 0
            video.release()
            return width, height, duration

        width, height, duration = await self.run_in_thread(_check_video, filename)
        
        if width == 0 or height == 0 or duration == 0:
            os.remove(filename)
            return None

        return {
            'filename': filename,
            'type': 'video',
            'caption': media_info.get('caption', default_caption),
            'duration': int(duration)
        }

    async def _validate_image(self, filename, media_info, default_caption):
        def _check_image(filename):
            try:
                img = Image.open(filename)
                img.verify()
                return img.size
            except:
                return (0, 0)

        width, height = await self.run_in_thread(_check_image, filename)
        
        if width == 0 or height == 0:
            os.remove(filename)
            return None

        return {
            'filename': filename,
            'type': 'image',
            'caption': media_info.get('caption', default_caption)
        }

class CombinedDownloaderBot:
    def __init__(self):
        # Initialize Pyrogram client
        self.app = Client(
            "media_downloader_bot",
            api_id=API_ID,
            api_hash=API_HASH,
            bot_token=BOT_TOKEN,
            workers=1000
        )

        self.logger = TelegramLogger(self.app, LOG_GROUP_ID)

        # Initialize Spotify client
        self.spotify = spotipy.Spotify(auth_manager=SpotifyClientCredentials(
            client_id=SPOTIFY_CLIENT_ID,
            client_secret=SPOTIFY_CLIENT_SECRET
        ))

        # Genius API settings
        self.genius_token = GENIUS_TOKEN
        self.genius_base_url = "https://api.genius.com"

        # Instagram API settings
        self.rapid_api_headers = {
            "x-rapidapi-key": RAPID_API_KEY,
            "x-rapidapi-host": "instagram-scraper-api-stories-reels-va-post.p.rapidapi.com"
        }

        # Concurrency control
        self.download_semaphore = asyncio.Semaphore(MAX_CONCURRENT_DOWNLOADS)
        self.upload_semaphore = asyncio.Semaphore(MAX_CONCURRENT_UPLOADS)
        self.thread_pool = ThreadPoolExecutor(max_workers=MAX_CONCURRENT_DOWNLOADS)
        self.rate_limit_queue = deque(maxlen=RATE_LIMIT_MESSAGES)

        self.pinterest_downloader = PinterestDownloader()

        # Initialize MongoDB
        self.mongo_client = AsyncIOMotorClient(MONGO_URI)
        self.db = self.mongo_client[DB_NAME]
        self.users_collection = self.db[USERS_COLLECTION]

        self.CHANNEL_USERNAME = "@SmokieOfficial"  # Replace with your channel username
        self.OWNER_USERNAME = "@Hmm_Smokie"  # Replace with your username

        # Session and state management
        self.session = None
        self.media_processor = None
        self.download_tasks = set()
        self.user_download_dirs = {}
        self.active_downloads = {}
        self.user_tasks = defaultdict(set)
        self.callback_query_handlers = {}

        # Ensure temp directory exists and is clean
        TEMP_DIR.mkdir(parents=True, exist_ok=True)
        self.cleanup_temp_directory()

    async def initialize(self):
        """Initialize aiohttp session and media processor"""
        self.session = aiohttp.ClientSession()
        self.media_processor = MediaProcessor(self.session)
        return self

    async def cleanup(self):
        """Cleanup resources"""
        if self.session:
            await self.session.close()
        self.thread_pool.shutdown(wait=True)

    def cleanup_temp_directory(self):
        """Clean up the entire temp directory"""
        try:
            if TEMP_DIR.exists():
                shutil.rmtree(TEMP_DIR)
                TEMP_DIR.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            logger.error(f"Error cleaning temp directory: {e}")

    def get_user_temp_dir(self, user_id):
        """Get or create user-specific temporary directory"""
        if user_id not in self.user_download_dirs:
            user_dir = TEMP_DIR / str(user_id)
            user_dir.mkdir(parents=True, exist_ok=True)
            self.user_download_dirs[user_id] = user_dir
        return self.user_download_dirs[user_id]

    def cleanup_user_directory(self, user_id):
        """Clean up a specific user's directory"""
        try:
            user_dir = self.get_user_temp_dir(user_id)
            if user_dir.exists():
                shutil.rmtree(user_dir)
                del self.user_download_dirs[user_id]
            if user_id in self.active_downloads:
                del self.active_downloads[user_id]
        except Exception as e:
            logger.error(f"Error cleaning user directory {user_id}: {e}")

    async def store_user(self, user_id: int, username: str):
        """Store user information in MongoDB"""
        try:
            await self.users_collection.update_one(
                {'user_id': user_id},
                {
                    '$set': {
                        'user_id': user_id,
                        'username': username
                    }
                },
                upsert=True
            )
        except Exception as e:
            logger.error(f"Error storing user data: {e}")

    def get_welcome_keyboard(self):
        """Create the welcome message inline keyboard"""
        return InlineKeyboardMarkup([
            [
                InlineKeyboardButton(
                    "🔔 Join Channel", url=f"https://t.me/{self.CHANNEL_USERNAME.replace('@', '')}"
                )
            ],
           [
                InlineKeyboardButton("👨‍💻 Owner", url=f"https://t.me/{self.OWNER_USERNAME.replace('@', '')}"),
                InlineKeyboardButton("➕ Add to Group", url=f"https://t.me/{self.app.me.username}?startgroup=true")
           ]
        ])
    
    async def check_membership(self, client, user_id: int) -> bool:
        """Check if user is a member of the required channel"""
        try:
            member = await client.get_chat_member(
                chat_id=self.CHANNEL_USERNAME,
                user_id=user_id
            )
            return member.status in [enums.ChatMemberStatus.MEMBER, 
                                   enums.ChatMemberStatus.OWNER, 
                                   enums.ChatMemberStatus.ADMINISTRATOR]
        except (KeyError, IndexError):
            return False
        except Exception as e:
            if "USER_NOT_PARTICIPANT" in str(e):
                return False
            # Only log unexpected errors
            if "USER_NOT_PARTICIPANT" not in str(e):
                logger.error(f"Unexpected error checking membership: {e}")
            return False

    def get_membership_keyboard(self):
        """Create the membership check inline keyboard"""
        return InlineKeyboardMarkup([
            [
                InlineKeyboardButton(
                    "✅ Join Channel",
                    url=f"https://t.me/{self.CHANNEL_USERNAME.replace('@', '')}"
                )
            ],
            [
                InlineKeyboardButton(
                    "🔍 Check Membership",
                    callback_data="check_membership"
                )
            ]
        ])

    async def send_membership_message(self, message):
        """Send the membership required message"""
        text = (
            f"🔒 **𝗖𝗵𝗮𝗻𝗻𝗲𝗹 𝗠𝗲𝗺𝗯𝗲𝗿𝘀𝗵𝗶𝗽 𝗥𝗲𝗾𝘂𝗶𝗿𝗲𝗱**\n\n"
            f"- ᴊᴏɪɴ {self.CHANNEL_USERNAME} ᴛᴏ ᴜꜱᴇ ᴛʜᴇ ʙᴏᴛ\n"
            "- ᴄʟɪᴄᴋ \"✅ ᴊᴏɪɴ ᴄʜᴀɴɴᴇʟ\" ʙᴜᴛᴛᴏɴ ʙᴇʟᴏᴡ ᴛᴏ ᴊᴏɪɴ ᴄʜᴀɴɴᴇʟ\n"
            "- ᴀꜰᴛᴇʀ ᴊᴏɪɴɪɴɢ, ᴄʟɪᴄᴋ ᴏɴ \"🔍 ᴄʜᴇᴄᴋ ᴍᴇᴍʙᴇʀꜱʜɪᴘ\" ʙᴜᴛᴛᴏɴ"
        )
        await message.reply_text(
            text,
            reply_markup=self.get_membership_keyboard()
        )

    @staticmethod
    def create_progress_bar(current, total, length=20):
        """Create a progress bar"""
        filled_length = int(length * current // total)
        return '▓' * filled_length + '░' * (length - filled_length)

    @staticmethod
    def format_size(size):
        """Format size in bytes to human readable format"""
        return humanize.naturalsize(size, binary=True)

    @staticmethod
    def format_speed(speed):
        """Format speed in bytes/second"""
        return f"{humanize.naturalsize(speed, binary=True)}/s"

    async def update_progress(self, current, total, msg, start_time):
        """Handle upload progress updates"""
        try:
            now = time.time()
            elapsed_time = now - start_time
            speed = current / elapsed_time if elapsed_time > 0 else 0
            progress = (current / total) * 100 if total > 0 else 0
            
            progress_bar = self.create_progress_bar(current, total)
            
            status_text = (
                "📤 Upload Progress\n"
                f"{progress_bar}\n"
                f"🚧 Progress: {progress:.1f}%\n"
                f"⚡️ Speed: {self.format_speed(speed)}\n"
                f"📶 {self.format_size(current)} of {self.format_size(total)}"
            )
            
            if math.floor(elapsed_time) % 2 == 0:
                await msg.edit_text(status_text)
        except Exception as e:
            logger.error(f"Progress update error: {e}")

    # Spotify-related methods
    async def search_spotify(self, query: str) -> Optional[dict]:
        """Async wrapper for Spotify search"""
        try:
            return await asyncio.get_event_loop().run_in_executor(
                self.thread_pool,
                partial(self.spotify.search, q=query, type='track', limit=1)
            )
        except Exception as e:
            logger.error(f"Spotify API error: {e}")
            return None

    async def get_artist_songs(self, artist_name: str) -> Tuple[Optional[List[str]], Optional[str]]:
        """Async wrapper for fetching artist songs"""
        try:
            results = await asyncio.get_event_loop().run_in_executor(
                self.thread_pool,
                partial(self.spotify.search, q=f"artist:{artist_name}", type="artist", limit=1)
            )

            if not results['artists']['items']:
                return None, "Artist not found."

            artist = results['artists']['items'][0]
            artist_id = artist['id']
            artist_name = artist['name']

            top_tracks = await asyncio.get_event_loop().run_in_executor(
                self.thread_pool,
                partial(self.spotify.artist_top_tracks, artist_id, country='US')
            )

            if not top_tracks['tracks']:
                return None, f"No top tracks found for {artist_name}."

            tracks = [
                f"{idx + 1}. {track['name']} ({track['album']['name']})  🔗 [Spotify Link]({track['external_urls']['spotify']})\n" 
                for idx, track in enumerate(top_tracks['tracks'])
            ]

            return tracks, None
        except Exception as e:
            logger.error(f"Error fetching artist songs: {e}")
            return None, str(e)

    async def fetch_lyrics(self, track_name: str, artist_name: str) -> str:
        """Async implementation of lyrics fetching"""
        try:
            if not self.session:
                await self.initialize()

            headers = {"Authorization": f"Bearer {self.genius_token}"}
            params = {"q": f"{track_name} {artist_name}"}
            
            async with self.session.get(
                f"{self.genius_base_url}/search",
                headers=headers,
                params=params
            ) as response:
                if response.status == 200:
                    data = await response.json()
                    hits = data.get("response", {}).get("hits", [])
                    if hits:
                        return f"Lyrics available here: [Genius Lyrics]({hits[0]['result']['url']})"
                return "Lyrics not found."
        except Exception as e:
            logger.error(f"Genius API error: {e}")
            return "Error fetching lyrics."

    async def download_spotify_song(self, query: str, message_id: int) -> Optional[str]:
        """Download song using yt-dlp"""
        async with self.download_semaphore:
            try:
                ydl_opts = {
                    'format': 'bestaudio/best',
                    'outtmpl': str(TEMP_DIR / f'{message_id}_%(title)s.%(ext)s'),
                    'postprocessors': [{
                        'key': 'FFmpegExtractAudio',
                        'preferredcodec': 'mp3',
                        'preferredquality': '192',
                    }],
                    'cookiefile': YT_COOKIES_PATH,
                    'quiet': True,
                    'no_warnings': True
                }

                def _download():
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = ydl.extract_info(f"ytsearch:{query}", download=True)
                        return ydl.prepare_filename(info['entries'][0])

                output_file = await asyncio.get_event_loop().run_in_executor(
                    self.thread_pool,
                    _download
                )

                mp3_file = Path(output_file).with_suffix('.mp3')
                return str(mp3_file) if mp3_file.exists() else None

            except Exception as e:
                logger.error(f"Download error for message {message_id}: {e}")
                return None

    # Social media download methods
    async def download_social_media(self, url, msg, user_id):
        """Download media from Facebook or Twitter"""
        try:
            user_temp_dir = self.get_user_temp_dir(user_id)
            unique_filename = f"download_{user_id}_{int(time.time() * 1000)}"
            
            ydl_opts = {
                'format': 'best',
                'outtmpl': f'{user_temp_dir}/{unique_filename}.%(ext)s',
                'quiet': True,
                'no_warnings': True,
                'no_color': True,
                'restrictfilenames': True,
                'writesubtitles': True,
                'writeinfojson': True,
                'postprocessors': [{
                    'key': 'FFmpegVideoConvertor',
                    'preferedformat': 'mp4',
                }],
                'http_headers': {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
                    'Accept-Language': 'en-US,en;q=0.9',
                }
            }

            await msg.edit_text("⏳ Processing media...")
            
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = await self.app.loop.run_in_executor(
                    self.thread_pool,
                    lambda: ydl.extract_info(url, download=True)
                )
                
                entries = info.get('entries', [info])
                downloaded_files = []
                captions = []
                
                for entry in entries:
                    media_file = ydl.prepare_filename(entry)
                    downloaded_files.append(media_file)
                    
                    raw_caption = entry.get('description', '') or entry.get('title', '')
                    if raw_caption:
                        caption = re.sub(r'https?://\S+', '', raw_caption).strip()
                        captions.append(caption)
                    else:
                        captions.append('')

                return downloaded_files, captions

        except Exception as e:
            logger.error(f"Download error: {e}")
            await msg.edit_text("❌ Download failed")
            return [], []

    # Message handlers
    async def handle_social_media_link(self, client, message):
        """Handle incoming social media links"""
        user_id = message.from_user.id
        
        if user_id in self.active_downloads:
            await message.reply_text("⚠️ Please wait for your current download to finish.")
            return
        
        self.active_downloads[user_id] = True
        status_msg = await message.reply_text("🔍 Processing your request...")
        url = message.text.strip()

        try:
            async with self.download_semaphore:
                media_files, captions = await self.download_social_media(url, status_msg, user_id)

            if not media_files:
                await status_msg.edit_text("❌ No media found in the link.")
                self.cleanup_user_directory(user_id)
                return

            await status_msg.edit_text("📤 Preparing to upload...")

            try:
                for file_path, caption in zip(media_files, captions):
                    async with self.upload_semaphore:
                        start_time = time.time()

                        if file_path.lower().endswith(('.mp4', '.avi', '.mov', '.mkv', '.webm')):
                            await message.reply_video(
                                video=file_path,
                                caption=caption,
                                progress=self.update_progress,
                                progress_args=(status_msg, start_time)
                            )
                        else:
                            await message.reply_document(
                                document=file_path,
                                caption=caption,
                                progress=self.update_progress,
                                progress_args=(status_msg, start_time)
                            )

                await status_msg.delete()

            except Exception as e:
                logger.error(f"Upload error: {e}")
                await status_msg.edit_text("❌ Upload failed")

        except Exception as e:
            logger.error(f"Processing error: {e}")
            await status_msg.edit_text(f"❌ An error occurred: {str(e)}")

        finally:
            self.cleanup_user_directory(user_id)

    async def process_spotify_download(self, client, message, query: str):
        """Handle Spotify download requests"""
        if not await self.rate_limit_check():
            await message.reply_text("Too many requests. Please try again later.")
            return

        try:
            status_message = await message.reply_text("🔍 Searching...")

            # Search Spotify
            spotify_results = await self.search_spotify(query)
            if not spotify_results or not spotify_results['tracks']['items']:
                await status_message.edit_text("Track not found on Spotify.")
                return

            track = spotify_results['tracks']['items'][0]
            metadata = {
                'name': track['name'],
                'artists': ', '.join(artist['name'] for artist in track['artists']),
                'album': track['album']['name'],
                'url': track['external_urls']['spotify']
            }

            await status_message.edit_text("⏬ Downloading...")
            
            download_task = asyncio.create_task(
                self.download_spotify_song(
                    f"{metadata['name']} {metadata['artists']}", 
                    message.id
                )
            )
            self.active_downloads[message.id] = download_task
            
            song_file = await download_task
            if not song_file:
                await status_message.edit_text("Download failed.")
                return

            lyrics_task = asyncio.create_task(
                self.fetch_lyrics(metadata['name'], metadata['artists'])
            )

            async with self.upload_semaphore:
                await status_message.edit_text("⏫ Uploading...")
                lyrics = await lyrics_task
                
                track_info = (
                    f"🎵 **Track:** {metadata['name']}\n"
                    f"👤 **Artists:** {metadata['artists']}\n"
                    f"💽 **Album:** {metadata['album']}\n"
                    f"🔗 [Spotify Link]({metadata['url']})\n\n"
                    f"🎶 **Lyrics:**\n{lyrics}"
                )

                await message.reply_audio(
                    audio=song_file,
                    caption=track_info,
                    disable_notification=False
                )

            await status_message.delete()
            if os.path.exists(song_file):
                os.remove(song_file)

        except Exception as e:
            logger.error(f"Error processing request: {e}")
            await message.reply_text("An error occurred while processing your request.")
        finally:
            if message.id in self.active_downloads:
                del self.active_downloads[message.id]

    async def process_artist_request(self, client, message, artist_name: str):
        """Handle artist list requests"""
        if not await self.rate_limit_check():
            await message.reply_text("Too many requests. Please try again later.")
            return

        try:
            status_message = await message.reply_text(f"🔍 Searching for songs by **{artist_name}**...")

            tracks, error = await self.get_artist_songs(artist_name)
            
            if error:
                await status_message.edit_text(f"Error: {error}")
                return

            track_list = "\n".join(tracks)
            
            if len(track_list) > 4000:
                chunks = [tracks[i:i + 10] for i in range(0, len(tracks), 10)]
                for i, chunk in enumerate(chunks):
                    chunk_text = f"**Top Tracks by {artist_name} (Part {i+1}/{len(chunks)}):**\n\n"
                    chunk_text += "\n".join(chunk)
                    if i == 0:
                        await status_message.edit_text(chunk_text)
                    else:
                        await message.reply_text(chunk_text)
            else:
                await status_message.edit_text(f"**Top Tracks by {artist_name}:**\n\n{track_list}")

        except Exception as e:
            logger.error(f"Error processing artist request: {e}")
            await message.reply_text("An error occurred while processing your request.")

    async def rate_limit_check(self) -> bool:
        """Check if we're within rate limits"""
        current_time = asyncio.get_event_loop().time()
        while self.rate_limit_queue and current_time - self.rate_limit_queue[0] > RATE_LIMIT_WINDOW:
            self.rate_limit_queue.popleft()
        
        if len(self.rate_limit_queue) < RATE_LIMIT_MESSAGES:
            self.rate_limit_queue.append(current_time)
            return True
        return False

    async def fetch_terabox_api(self, link: str) -> Dict[str, Any]:
        """Async function to fetch data from Terabox API"""
        headers = {
            "x-rapidapi-key": RAPIDAPI_KEY,
            "x-rapidapi-host": RAPIDAPI_HOST,
        }
        params = {"link": link}
        
        async with self.download_semaphore:
            try:
                async with self.session.get(TERABOX_API_URL, headers=headers, params=params) as response:
                    return await response.json()
            except Exception as e:
                logger.error(f"API request failed: {e}")
                raise

    def create_terabox_markup(self, video_id: str, download_link: str) -> InlineKeyboardMarkup:
        """Create inline keyboard markup for Terabox links"""
        return InlineKeyboardMarkup([
            [
                InlineKeyboardButton(
                    "▶️ Watch Online", 
                    web_app=WebAppInfo(url=f"{WEBAPP_URL}?id={video_id}")
                ),
                InlineKeyboardButton("📥 Download", url=download_link)
            ]
        ])

    async def handle_terabox_link(self, client, message):
        """Handle incoming Terabox links"""
        terabox_link = message.text.strip()

        try:
            status_message = await message.reply_text("Processing your request...")
            data = await self.fetch_terabox_api(terabox_link)

            if "url" in data:
                download_link = data["url"].replace("\\/", "/")
                video_id = download_link.split("id=")[-1]
                reply_markup = self.create_terabox_markup(video_id, download_link)

                await status_message.delete()
                await message.reply_photo(
                    photo=TERABOX_IMAGE,
                    caption="Boom! Your File Link is Good to Go!\n\nＰＯＷＥＲＥＤ ＢＹ ＰＯＲＮＨＵＢ Ｘ ＴＥＲＡＢＯＸ",
                    reply_markup=reply_markup
                )

            elif "data" in data:
                details = data.get("data", {})
                file_name = details.get("file_name", "Unknown")
                file_size = details.get("file_size", "Unknown")
                download_link = details.get("download_link", "Unavailable")

                reply_markup = InlineKeyboardMarkup([
                    [
                        InlineKeyboardButton(
                            "📱 View in Mini App",
                            web_app=WebAppInfo(url=f"{WEBAPP_URL}?filename={file_name}")
                        ),
                        InlineKeyboardButton("📥 Direct Download", url=download_link)
                    ]
                ])

                reply_text = (
                    f"**Terabox File Details:**\n"
                    f"**Name:** {file_name}\n"
                    f"**Size:** {file_size}"
                )

                await status_message.delete()
                await message.reply_photo(
                    photo=TERABOX_IMAGE,
                    caption=reply_text,
                    reply_markup=reply_markup
                )

            else:
                await status_message.edit_text("Unexpected response format. Please check the link.")

        except Exception as e:
            logger.error(f"Error processing link: {str(e)}", exc_info=True)
            await message.reply_text(
                "An error occurred while processing your request. Please try again later."
            )

    async def handle_nonveg_reel(self, client, message):
        """Handle the nonveg_reel command"""
        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton(
                    text="Non Veg Reels",
                    web_app=WebAppInfo(url="NON VEG MINI URL")#CHANGE WITH YOUR NON VEG REEL URL
                )
            ]
        ])

        await client.send_photo(
            chat_id=message.chat.id,
            photo=NONVEG_IMAGE,
            caption="💥 Unlock your Mini App now! Just tap the button below!\n\nＰＯＷＥＲＥＤ ＢＹ ＰＯＲＮＨＵＢ Ｘ ＭＩＮＩ ＡＰＰ",
            reply_markup=keyboard
        )

    async def download_instagram_media(self, url, prefix='temp'):
        async with self.session.get(RAPID_API_URL, headers=self.rapid_api_headers, params={"url": url}) as response:
            if response.status != 200:
                return "Unable to download media"
            
            data = await response.json()
            if data.get('error', True):
                return "Unable to download media"

            media_type = 'carousel' if data.get('type') == 'album' else 'single'
            if media_type == 'single':
                return await self.media_processor.validate_and_process_media(data, prefix=prefix)
            else:
                return await self._process_multiple_media(data, prefix)

    async def _process_multiple_media(self, data, prefix):
        tasks = []
        for index, media_info in enumerate(data.get('medias', [])):
            unique_prefix = f"{prefix}_{index}"
            task = asyncio.create_task(
                self.media_processor.validate_and_process_media(media_info, prefix=unique_prefix)
            )
            tasks.append(task)
        
        results = await asyncio.gather(*tasks)
        return [result for result in results if result]

    async def handle_instagram_url(self, client, message):
        user_id = message.from_user.id
        
        if len(self.user_tasks[user_id]) >= 5:
            await message.reply_text("Please wait for your previous downloads to complete.")
            return

        url = message.text
        unique_prefix = f"{message.chat.id}_{message.id}"
        processing_msg = await message.reply_text("🔄 Downloading Media...")

        try:
            task = asyncio.create_task(self._process_instagram_url(
                client, message, url, unique_prefix, processing_msg
            ))
            self.user_tasks[user_id].add(task)
            await task
        except Exception as e:
            logger.error(f"Task error: {e}")
            await processing_msg.edit_text(f"❌ Error: {str(e)}")
        finally:
            self.user_tasks[user_id].remove(task)
            if os.path.exists(os.path.join(TEMP_DIR, unique_prefix)):
                os.remove(os.path.join(TEMP_DIR, unique_prefix))

    async def _process_instagram_url(self, client, message, url, unique_prefix, processing_msg):
        try:
            result = await self.download_instagram_media(url, prefix=unique_prefix)
            
            if isinstance(result, str):
                await processing_msg.edit_text(result)
                return

            if processing_msg.text != "📤 Uploading Media...":
                await processing_msg.edit_text("📤 Uploading Media...")

            if isinstance(result, dict):
                await self._send_single_media(client, message, result)
            elif isinstance(result, list):
                await self._send_multiple_media_group(client, message, result)

            await processing_msg.delete()

        except Exception as e:
            logger.error(f"Processing error: {e}")
            await processing_msg.edit_text(f"❌ Error: {str(e)}")

    async def _send_single_media(self, client, message, media_info):
        try:
            if media_info['type'] == 'video':
                await client.send_video(
                    chat_id=message.chat.id,
                    video=media_info['filename'],
                    caption=media_info['caption']
                )
            elif media_info['type'] == 'image':
                await client.send_photo(
                    chat_id=message.chat.id,
                    photo=media_info['filename'],
                    caption=media_info['caption']
                )
        finally:
            if os.path.exists(media_info['filename']):
                os.remove(media_info['filename'])

    async def _send_multiple_media_group(self, client, message, media_items):
        media_group = []
        try:
            for item in media_items:
                if item['type'] == 'video':
                    media_group.append(
                        InputMediaVideo(
                            media=item['filename'],
                            caption=item['caption'] if len(media_group) == 0 else None
                        )
                    )
                elif item['type'] == 'image':
                    media_group.append(
                        InputMediaPhoto(
                            media=item['filename'],
                            caption=item['caption'] if len(media_group) == 0 else None
                        )
                    )

            if media_group:
                await client.send_media_group(chat_id=message.chat.id, media=media_group)
        finally:
            for item in media_items:
                if os.path.exists(item['filename']):
                    os.remove(item['filename'])
    async def handle_pinterest_link(self, client, message):
        """Handle Pinterest link downloads"""
        url = message.text.strip()
        status_msg = await message.reply_text("⏳ Processing your Pinterest media...")
        
        try:
            pin_id = await self.pinterest_downloader.extract_pin_id(url)
            if not pin_id:
                await status_msg.edit_text('Invalid Pinterest URL. Please send a valid pin URL.')
                return

            media_data = await self.pinterest_downloader.download_pool.spawn(
                self.pinterest_downloader.get_pin_data(pin_id)
            )

            if not media_data:
                await status_msg.edit_text('Could not find media in this Pinterest link.')
                return

            file_path = self.get_user_temp_dir(message.from_user.id) / f"pin_{pin_id}"
            file_path = file_path.with_suffix('.mp4' if media_data.media_type == 'video' else '.jpg')

            success = await self.pinterest_downloader.download_pool.spawn(
                self.pinterest_downloader.download_file(media_data.url, file_path)
            )

            if not success:
                await status_msg.edit_text('Failed to download media. Please try again later.')
                return

            start_time = time.time()
            if media_data.media_type == "video":
                await message.reply_video(
                    video=str(file_path),
                    progress=self.update_progress,
                    progress_args=(status_msg, start_time)
                )
            else:
                await message.reply_photo(
                    photo=str(file_path),
                    progress=self.update_progress,
                    progress_args=(status_msg, start_time)
                )

            await status_msg.delete()

        except Exception as e:
            logger.error(f"Error processing Pinterest link: {e}")
            await status_msg.edit_text("An error occurred while processing your request.")
        finally:
            self.cleanup_user_directory(message.from_user.id) 

    async def sanitize_filename(self, title: str) -> str:
        """Sanitize file name by removing invalid characters."""
        title = re.sub(r'[<>:"/\\|?*]', '', title)
        title = title.replace(' ', '_')
        return f"{title[:50]}_{int(time.time())}"

    async def validate_youtube_url(self, url: str) -> bool:
        """Validate if the provided URL is a valid YouTube link."""
        return url.startswith(('https://www.youtube.com/', 'https://youtube.com/', 'https://youtu.be/'))

    async def get_youtube_dl_opts(self, output_filename: str, is_audio: bool = False) -> dict:
        """Return yt-dlp options based on type."""
        if is_audio:
            return {
                'format': 'bestaudio/best',
                'outtmpl': f'{output_filename}.%(ext)s',
                'cookiefile': YT_COOKIES_PATH,
                'quiet': True,
                'noprogress': True,
                'no_warnings': True,
                'nocheckcertificate': True,
                'postprocessors': [{
                    'key': 'FFmpegExtractAudio',
                    'preferredcodec': 'mp3',
                    'preferredquality': '192',
                }]
            }
        else:
            return {
                'format': 'bestvideo[height<=720][ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]',
                'outtmpl': output_filename,
                'cookiefile': YT_COOKIES_PATH,
                'quiet': True,
                'noprogress': True,
                'no_warnings': True,
                'nocheckcertificate': True,
                'postprocessors': [{'key': 'FFmpegVideoConvertor', 'preferedformat': 'mp4'}]
            }

    async def prepare_thumbnail(self, thumbnail_url: str, output_path: str) -> Optional[str]:
        """Download and prepare the thumbnail image."""
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(thumbnail_url) as response:
                    if response.status == 200:
                        thumbnail_temp_path = f"{output_path}_thumbnail.jpg"
                        thumbnail_data = await response.read()
                        
                        with open(thumbnail_temp_path, 'wb') as f:
                            f.write(thumbnail_data)

                        thumbnail_resized_path = f"{output_path}_thumb.jpg"
                        with Image.open(thumbnail_temp_path) as img:
                            img = img.convert('RGB')
                            img.thumbnail((320, 320), Image.Resampling.LANCZOS)
                            background = Image.new('RGB', (320, 320), (255, 255, 255))
                            offset = ((320 - img.width) // 2, (320 - img.height) // 2)
                            background.paste(img, offset)
                            background.save(thumbnail_resized_path, "JPEG", quality=85)

                        os.remove(thumbnail_temp_path)
                        return thumbnail_resized_path
        except Exception as e:
            logger.error(f"Error preparing thumbnail: {e}")
        return None

    async def handle_youtube_download(self, client, message, url: str, is_audio: bool = False):
        """Handle YouTube video/audio download requests."""
        if not await self.validate_youtube_url(url):
            await message.reply_text("❌ Please send a valid YouTube link.")
            return

        user_id = message.from_user.id
        if user_id in self.active_downloads:
            await message.reply_text("⚠️ Please wait for your current download to finish.")
            return

        status_message = await message.reply_text("⏳ Processing your request...")
        self.active_downloads[user_id] = True

        try:
            with yt_dlp.YoutubeDL({'quiet': True, 'cookiefile': YT_COOKIES_PATH}) as ydl:
                info = await self.app.loop.run_in_executor(
                    self.thread_pool,
                    lambda: ydl.extract_info(url, download=False)
                )

            if not info:
                await status_message.edit_text("Could not fetch video information")
                return

            title = info.get('title', 'Unknown Title')
            duration = info.get('duration', 0)
            thumbnail_url = info.get('thumbnail', None)

            safe_title = await self.sanitize_filename(title)
            output_path = f"temp_media/{safe_title}"
            os.makedirs("temp_media", exist_ok=True)

            opts = await self.get_youtube_dl_opts(output_path, is_audio)
            
            await status_message.edit_text("⏬ Downloading...")
            
            with yt_dlp.YoutubeDL(opts) as ydl:
                await self.app.loop.run_in_executor(
                    self.thread_pool,
                    lambda: ydl.download([url])
                )

            if is_audio:
                output_path = f"{output_path}.mp3"
            else:
                output_path = f"{output_path}.mp4"

            if not os.path.exists(output_path):
                await status_message.edit_text("Download failed: File not created")
                return

            file_size = os.path.getsize(output_path)
            if file_size > 2_000_000_000:
                await status_message.edit_text("File exceeds Telegram's 2GB limit.")
                return

            await status_message.edit_text("📤 Uploading...")

            start_time = time.time()
            last_update_time = [0]

            if is_audio:
                await client.send_audio(
                    chat_id=message.chat.id,
                    audio=output_path,
                    caption=f"🎵 **{title}**",
                    duration=duration,
                    progress=self.update_progress,
                    progress_args=(status_message, start_time)
                )
            else:
                thumbnail_path = await self.prepare_thumbnail(thumbnail_url, output_path) if thumbnail_url else None
                
                await client.send_video(
                    chat_id=message.chat.id,
                    video=output_path,
                    caption=f"🎥 **{title}**",
                    duration=duration,
                    thumb=thumbnail_path,
                    supports_streaming=True,
                    progress=self.update_progress,
                    progress_args=(status_message, start_time)
                )

                if thumbnail_path and os.path.exists(thumbnail_path):
                    os.remove(thumbnail_path)

            await status_message.delete()

        except Exception as e:
            logger.error(f"YouTube download error: {e}")
            await status_message.edit_text(f"❌ An error occurred: {str(e)}")
        
        finally:
            if os.path.exists(output_path):
                os.remove(output_path)
            if user_id in self.active_downloads:
                del self.active_downloads[user_id]

    async def search_youtube(self, query: str) -> Optional[str]:
        """Search YouTube for the first audio result matching the query."""
        try:
            videos_search = VideosSearch(query, limit=1)
            results = await videos_search.next()
            if results and results['result']:
                return results['result'][0]['link']
            return None
        except Exception as e:
            logger.error(f"YouTube search error: {e}")
            return None
        
    async def broadcast_message(self, message: Message, user_id: int) -> Tuple[bool, str]:
        """
        Broadcast a message by copying it instead of forwarding
        Returns: (success, error_message)
        """
        try:
            # Get the message type and relevant attributes
            caption = message.caption if message.caption else None
            reply_markup = message.reply_markup if message.reply_markup else None
            
            if message.text:
                # Text message
                await self.app.send_message(
                    chat_id=user_id,
                    text=message.text,
                    entities=message.entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.photo:
                # Photo message
                await self.app.send_photo(
                    chat_id=user_id,
                    photo=message.photo.file_id,
                    caption=caption,
                    caption_entities=message.caption_entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.video:
                # Video message
                await self.app.send_video(
                    chat_id=user_id,
                    video=message.video.file_id,
                    caption=caption,
                    caption_entities=message.caption_entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.audio:
                # Audio message
                await self.app.send_audio(
                    chat_id=user_id,
                    audio=message.audio.file_id,
                    caption=caption,
                    caption_entities=message.caption_entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.document:
                # Document message
                await self.app.send_document(
                    chat_id=user_id,
                    document=message.document.file_id,
                    caption=caption,
                    caption_entities=message.caption_entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.animation:
                # Animation/GIF message
                await self.app.send_animation(
                    chat_id=user_id,
                    animation=message.animation.file_id,
                    caption=caption,
                    caption_entities=message.caption_entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.sticker:
                # Sticker message
                await self.app.send_sticker(
                    chat_id=user_id,
                    sticker=message.sticker.file_id,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.voice:
                # Voice message
                await self.app.send_voice(
                    chat_id=user_id,
                    voice=message.voice.file_id,
                    caption=caption,
                    caption_entities=message.caption_entities,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            elif message.video_note:
                # Video note message
                await self.app.send_video_note(
                    chat_id=user_id,
                    video_note=message.video_note.file_id,
                    reply_markup=reply_markup,
                    disable_notification=True
                )
            
            return True, ""
            
        except FloodWait as e:
            await asyncio.sleep(e.value)
            return await self.broadcast_message(message, user_id)
        except InputUserDeactivated:
            return False, "deactivated"
        except UserIsBlocked:
            return False, "blocked"
        except PeerIdInvalid:
            return False, "invalid_id"
        except Exception as e:
            return False, f"other:{str(e)}"

    async def broadcast_handler(self, client, message: Message):
        """Handle the broadcast command"""
        # Check if the user is the owner by comparing username or ID
        if (message.from_user.username != self.OWNER_USERNAME.replace("@", "") and 
            str(message.from_user.id) != "1949883614"):  # Replace with your user ID
            await message.reply_text("⛔️ This command is only for the bot owner.")
            return

        # Check if the command is a reply to a message
        if not message.reply_to_message:
            await message.reply_text(
                "❗️ Please reply to a message to broadcast it to all users."
            )
            return

        # Initial broadcast status message
        status_msg = await message.reply_text("🚀 Starting broadcast...")
        
        total_users = await self.users_collection.count_documents({})
        done = 0
        success = 0
        failed = 0
        blocked = 0
        deleted = 0
        invalid = 0
        failed_users = []
        
        async for user in self.users_collection.find({}, {'user_id': 1}):
            done += 1
            success_status, error = await self.broadcast_message(
                message.reply_to_message,
                user['user_id']
            )
            
            if success_status:
                success += 1
            else:
                failed += 1
                failed_users.append((user['user_id'], error))
                if error == "blocked":
                    blocked += 1
                elif error == "deactivated":
                    deleted += 1
                elif error == "invalid_id":
                    invalid += 1

            if done % 20 == 0:
                try:
                    await status_msg.edit_text(
                        f"🚀 Broadcast in Progress...\n\n"
                        f"👥 Total Users: {total_users}\n"
                        f"✅ Completed: {done} / {total_users}\n"
                        f"✨ Success: {success}\n"
                        f"❌ Failed: {failed}\n\n"
                        f"🚫 Blocked: {blocked}\n"
                        f"❗️ Deleted: {deleted}\n"
                        f"📛 Invalid: {invalid}"
                    )
                except FloodWait as e:
                    await asyncio.sleep(e.value)
                except Exception:
                    pass

        # Final broadcast status
        completion_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        await status_msg.edit_text(
            f"✅ Broadcast Completed!\n"
            f"Completed at: {completion_time}\n\n"
            f"👥 Total Users: {total_users}\n"
            f"✨ Success: {success}\n"
            f"❌ Failed: {failed}\n\n"
            f"Success Rate: {(success/total_users)*100:.2f}%\n\n"
            f"🚫 Blocked: {blocked}\n"
            f"❗️ Deleted: {deleted}\n"
            f"📛 Invalid: {invalid}"
        )

        # Clean up invalid users from database
        if failed_users:
            clean_msg = await message.reply_text(
                "🧹 Cleaning database...\n"
                "Removing blocked and deleted users."
            )
            # Extract user IDs from failed_users list
            invalid_user_ids = [user_id for user_id, _ in failed_users]
            # Delete invalid users from database
            delete_result = await self.users_collection.delete_many(
                {"user_id": {"$in": invalid_user_ids}}
            )
            await clean_msg.edit_text(
                f"🧹 Database cleaned!\n"
                f"Removed {delete_result.deleted_count} invalid users."
            )

    def start(self):
        """Start the bot with all command handlers"""
        # Social media URL pattern
        social_media_pattern = r'(facebook\.com|fb\.watch|(?:www\.)?(twitter|x)\.com/\w+/status/\d+)'
        instagram_pattern = r'(instagram\.com/(reel/|p/|stories/|s/aGlnaGxpZ2h0).*?)'
        pinterest_pattern = r'(pinterest\.com/pin/|pin\.it/)'

        # For TeraBox handler
        @self.app.on_message(filters.regex(r"terasharelink\.com|1024terabox\.com|teraboxlink\.com|terafileshare\.com|teraboxapp\.com|teraboxshare\.com"))
        async def on_terabox_link(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            # Log the action
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "terabox",
                message.text
            )
            
            # Store user data and continue with existing handler
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            await self.handle_terabox_link(client, message)

        @self.app.on_message(filters.regex(social_media_pattern))
        async def on_media_link(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            platform = "facebook" if "facebook" in message.text or "fb.watch" in message.text else "twitter"
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                platform,
                message.text
            )
            
            # Store user data
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            task = asyncio.create_task(self.handle_social_media_link(client, message))
            self.download_tasks.add(task)
            task.add_done_callback(self.download_tasks.discard)

        @self.app.on_message(filters.regex(instagram_pattern))
        async def on_instagram_link(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            # Log the action
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "instagram",
                message.text
            )
            
            # Store user data and continue with existing handler
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            await self.handle_instagram_url(client, message)

        @self.app.on_message(filters.regex(pinterest_pattern))
        async def on_pinterest_link(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            # Log the action
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "pinterest",
                message.text
            )
            
            # Store user data and continue with existing handler
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            task = asyncio.create_task(self.handle_pinterest_link(client, message))
            self.download_tasks.add(task)
            task.add_done_callback(self.download_tasks.discard)

        @self.app.on_message(filters.regex(r"^(https?://)?(www\.)?(youtube\.com|youtu\.be)/.+$"))
        async def youtube_link_handler(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "youtube",
                message.text
            )
                        
            # Store user data
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            await self.handle_youtube_download(client, message, message.text.strip())

        @self.app.on_message(filters.command("audio"))
        async def audio_command(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return

            query = message.text.split(maxsplit=1)[1] if len(message.text.split()) > 1 else None
            if not query:
                await message.reply_text("❌ Please provide a YouTube video link or song name.")
                return
            
            # Log the action
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "audio",
                query
            )
            
            # Store user data and continue with existing handler
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )

            if await self.validate_youtube_url(query):
                await self.handle_youtube_download(client, message, query, is_audio=True)
            else:
                status_message = await message.reply_text("🔍 Searching...")
                video_url = await self.search_youtube(query)
                if not video_url:
                    await status_message.edit_text("❌ No matching videos found.")
                    return
                await status_message.delete()
                await self.handle_youtube_download(client, message, video_url, is_audio=True)

        @self.app.on_message(filters.command("spotify"))
        async def spotify_handler(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return

            # Get the query first
            query = ' '.join(message.command[1:]).strip()
             
            # Log the action regardless of whether query is empty
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "spotify",
                query if query else "No query provided"
            )

            # Store user data
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )

            # Check if query is empty after logging
            if not query:
                await message.reply_text(
                    "Please provide a song name. Usage: /spotify <Song Name>"
                )
                return
            
            await self.process_spotify_download(client, message, query)

        @self.app.on_message(filters.command("sptfylist"))
        async def sptfylist_handler(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return

            artist_name = ' '.join(message.command[1:]).strip()
            if not artist_name:
                await message.reply_text(
                    "Please provide an artist name. Usage: /sptfylist <Artist Name>"
                )
                return
            
            # Log the action
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "spotify_list",
                artist_name
            )
            
            # Store user data and continue with existing handler
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            await self.process_artist_request(client, message, artist_name)

        @self.app.on_message(filters.command("nonveg_reel"))
        async def on_nonveg_reel(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            # Log the action
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "nonveg_reels",
                "Requested non-veg reels"
            )
            
            # Store user data and continue with existing handler
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            
            await self.handle_nonveg_reel(client, message)

        @self.app.on_message(filters.command("broadcast") & filters.user(OWNER_USERNAME))
        async def broadcast_cmd(client, message):
            await self.broadcast_handler(client, message)

        @self.app.on_message(filters.command("users") & filters.user(OWNER_USERNAME))
        async def user_count(client, message: Message):
            total_users = await bot.db[USERS_COLLECTION].count_documents({})
            active_past_week = await bot.db[USERS_COLLECTION].count_documents({
                "last_active": {"$gte": datetime.now() - timedelta(days=7)}
            })
            
            await message.reply_text(
                f"📊 **Bot Statistics**\n\n"
                f"Total Users: `{total_users:,}`\n"
                f"Active Past Week: `{active_past_week:,}`"
            )

        @self.app.on_callback_query()
        async def callback_query_handler(client, callback_query: CallbackQuery):
            if callback_query.data == "check_membership":
                is_member = await self.check_membership(client, callback_query.from_user.id)
                if is_member:
                    # Store user data
                    await self.store_user(
                        callback_query.from_user.id,
                        callback_query.from_user.username or "No username"
                    )

                    await callback_query.message.delete()
                    # Send welcome message
                    welcome_text = (
                        "🎉 **Welcome to the Ultimate Media Downloader Bot!**\n\n"
                        "I can help you download your favorite content:\n\n"
                        "📥 **Features:**\n"
                        "• Download YouTube videos & shorts\n"
                        "• Download Facebook videos\n"
                        "• Download Public Instagram reels, story, highlights, post, igtv\n"
                        "• Download Twitter/X videos\n"
                        "• Download Spotify songs\n"
                        "• Download & Watch Terabox Content\n"
                        "• Download Pinterest images & videos\n"
                        "• Watch Non-Veg Content\n"
                        "• Get artist's top tracks\n\n"
                        "🎯 **How to Use:**\n"
                        "• Simply send a Facebook, Twitter/X, Terabox/Non-Veg video link\n"
                        "▫️ /audio [YouTube URL] - Download audio from a video URL\n"
                        "▫️ /audio [song name] - Search and download audio by name\n\n"
                        "▫️ Use /spotify <song name> to download music\n"
                        "▫️ Use /sptfylist <artist name> for top tracks\n"
                        "▫️ Use /nonveg_reel for top non-veg reels\n\n"
                        "✨ Join our channel for updates and support!"
                    )
                    await callback_query.message.reply_animation(
                        animation="https://cdn.glitch.global/8165267b-e8d9-4a47-a5f2-bc40cef0b65f/loading-15146_512.gif?v=1733936190678",
                        caption=welcome_text,
                        reply_markup=self.get_welcome_keyboard()
                    )
                else:
                    await callback_query.answer(
                        "❌ You haven't joined the channel yet. Please join first!",
                        show_alert=True
                    )

        @self.app.on_message(filters.command("start"))
        async def start_handler(client, message):
            is_member = await self.check_membership(client, message.from_user.id)
            if not is_member:
                await self.send_membership_message(message)
                return
            
            await self.logger.log_bot_start(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name
            )

            # Store user data
            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )
            # Send welcome GIF with message
            welcome_text = (
                        "🎉 **Welcome to the Ultimate Media Downloader Bot!**\n\n"
                        "I can help you download your favorite content:\n\n"
                        "📥 **Features:**\n"
                        "• Download YouTube videos & shorts\n"
                        "• Download Facebook videos\n"
                        "• Download Public Instagram reels, story, highlights, post, igtv\n"
                        "• Download Twitter/X videos\n"
                        "• Download Spotify songs\n"
                        "• Download & Watch Terabox Content\n"
                        "• Download Pinterest images & videos\n"
                        "• Watch Non-Veg Content\n"
                        "• Get artist's top tracks\n\n"
                        "🎯 **How to Use:**\n"
                        "• Simply send a Facebook, Twitter/X, Terabox/Non-Veg video link\n"
                        "▫️ /audio [YouTube URL] - Download audio from a video URL\n"
                        "▫️ /audio [song name] - Search and download audio by name\n\n"
                        "▫️ Use /spotify <song name> to download music\n"
                        "▫️ Use /sptfylist <artist name> for top tracks\n"
                        "▫️ Use /nonveg_reel for top non-veg reels\n\n"
                        "✨ Join our channel for updates and support!"
                    )
            try:
                await message.reply_animation(
                    animation="https://cdn.glitch.global/8165267b-e8d9-4a47-a5f2-bc40cef0b65f/loading-15146_512.gif?v=1733936190678",
                    caption=welcome_text,
                    reply_markup=self.get_welcome_keyboard()
                )
            except Exception as e:
                # Fallback to regular message if animation fails
                logger.error(f"Error sending welcome animation: {e}")
                await message.reply_text(
                    welcome_text,
                    reply_markup=self.get_welcome_keyboard()
                )

        # Initialize aiohttp session and start the bot
        loop = asyncio.get_event_loop()
        loop.create_task(self.initialize())
        
        try:
            self.app.run()
        finally:
            loop.run_until_complete(self.cleanup())
            self.cleanup_temp_directory()

if __name__ == "__main__":
    bot = CombinedDownloaderBot()
    bot.start()
