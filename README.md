# ᴘᴏᴡᴇʀᴇᴅ ʙʏ ＳＳ 🇬​​🇷​​🇴​​🇺​​🇵

# Media Downloader Bot

## Overview
The Media Downloader Bot allows you to seamlessly download media from various popular platforms directly to your Telegram. It supports platforms like Instagram, YouTube, Pinterest, Facebook, and Twitter. This bot is perfect for users looking for an easy way to save content from social media sites.

## Features
- **Instagram Media Downloader**  
- **YouTube Video Downloader**
- **Pinterest Image & Video Downloader**
- **Facebook & Twitter Media Downloader**
- **Multiple Download Formats Supported** (Images, Videos, Audio)
- **Fast Downloading**  
- **User-Friendly Interface**  
- **Simple Commands for Easy Use**

## Prerequisites
- Python 3.7+
- Requests Library
- Telethon or Pyrogram (for Telegram bot)
- Telegram Bot Token
- API Credentials for platforms (if required)

## Installation

1. Clone the repository:
    ```bash
    https://github.com/HmmSmokieOfficial/Media-Downloader.git
    ```

2. Install required dependencies:
    ```bash
    pip install -r requirements.txt

3. Sudo Cammand To Install:
    ```bash
    sudo apt install libgl1
    sudo apt install ffmpeg
    ```

4. Set up required variables:
    ```bash
    TELEGRAM_API_ID=your_api_id
    TELEGRAM_API_HASH=your_api_hash
    TELEGRAM_BOT_TOKEN=your_bot_token
    MONGO_URL=your_mongo_url
    LOG_GROUP_ID=log channel id
    OWNER_USERNAME=username of owner
    SPOTIFY_CLIENT_ID=spotify client id
    SPOTIFY_CLIENT_SECRET=spotify client secret
    GENIUS_TOKEN=genius token for lyrics
    RAPID_API_KEY= api key for instagram
    RAPID_API_URL= api url for instagram
    WEBAPP_URL= mini app url for terabox
    TERABOX_API_URL= api url for terabox
    RAPIDAPI_KEY= api key for terabox
    RAPIDAPI_HOST= host for terabox
    ```
5. Need 3 Directory:
  - temp
  - temp_media

## Configuration
- Ensure the necessary API credentials are provided for each supported platform.
- Update any support channel links and contact information.

## Main Functions

- **/start**: Initialize the bot and get the welcome message
- **/broadcast**: Broadcast to user
- **/spotify**: Get The Track Of Song
- **/audio**: Search and Download The Youtube Video In audio format
- **/sptfylist**: Search top track of the artist
- **/nonveg-reel**: get the top notch non veg reels

## Supported Platforms
- **Instagram**
- **YouTube**
- **Pinterest**
- **Facebook**
- **Twitter**
- **Terabox**

## Security and Permissions
- The bot ensures secure download links and access.
- All download requests are logged for monitoring purposes.
- Commands are restricted to authorized users, ensuring safety.

## Logging
The bot logs all activities to help track usage and error handling, including:
- **Timestamp**
- **Log level**
- **Error messages**

## Error Handling
Robust error management is in place, including:
- **Platform errors** (e.g., invalid link)
- **Rate limiting** (on certain platforms)
- **Download failure detection**

## Customization
The bot is easily customizable:
- Change welcome messages
- Update platform support
- Adjust download formats

## Contributions
To contribute:
1. Fork the repository
2. Create a feature branch
3. Commit your changes
4. Push to the branch
5. Open a pull request

## License
[Specify your license, e.g., MIT License]

## Contact
- Telegram: [https://t.me/hmm_Smokie](https://t.me/hmm_Smokie)
- GitHub: [https://github.com/thefinegraphicsroom](https://github.com/thefinegraphicsroom)

**Note:** Always keep your API credentials and bot token confidential.
