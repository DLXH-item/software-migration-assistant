# -*- coding: utf-8 -*-
"""
软件迁移助手 SoftMigrator v3.2
把本机已安装的软件（程序文件 + 注册表 + 用户配置 + 存档 + 快捷方式）打包成一个 .zip 迁移包，
在另一台电脑上选目标路径一键还原，自动生成桌面快捷方式，点开即用。

"""

import os
import sys
import string
import json
import html as _html
import re
import base64
import shutil
import zipfile
import tempfile
import subprocess
import threading
import queue
import ctypes
import time
import hashlib
from datetime import datetime
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_NAME = "软件迁移助手"
APP_VER = "3.3"
PKG_EXT = ".zip"
MANIFEST_NAME = "manifest.json"

COMPRESS_LEVEL = 1
NO_COMPRESS_EXT = {
    ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".ico", ".heic",
    ".mp4", ".mkv", ".avi", ".mov", ".webm", ".flv", ".mp3", ".aac", ".flac", ".m4a", ".wav",
    ".zip", ".7z", ".rar", ".gz", ".xz", ".bz2", ".cab", ".msi", ".apk", ".jar",
    ".pak", ".bin", ".woff", ".woff2", ".ttf", ".otf",
}
CACHE_DIR_NAMES = {
    "cache", "cache2", "code cache", "gpucache", "shadercache", "grshadercache",
    "dawnwebgpubasedcache", "dawnwebgpucache", "dawngraphitecache",
    "crashpad", "crashreports", "crashdumps", "logs", "log", "temp", "tmp",
    "service worker", "scriptcache", "cachestorage", "webcache", "cacheddata",
    "cache_data", "updatecache", "updates", "缓存", "临时", "临时文件", "日志",
}
CACHE_FILE_EXT = {".log", ".tmp", ".dmp", ".etl"}


class PackAbort(Exception):
    """用户点了『取消打包』"""
    pass


def _aborted(flag):
    return bool(flag and flag.get("v"))

# ---------------- 基础工具 ----------------


def human_size(n):
    try:
        n = float(n)
    except Exception:
        return "-"
    for u in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or u == "TB":
            return ("%d %s" % (n, u)) if u == "B" else ("%.1f %s" % (n, u))
        n /= 1024
    return "-"


def norm(s):
    return re.sub(r"[^0-9a-z\u4e00-\u9fa5]", "", (s or "").lower())


def lp(p):
    if not p:
        return p
    p = os.path.abspath(p)
    if p.startswith("\\\\?\\"):
        return p
    if len(p) > 240:
        if p.startswith("\\\\"):
            return "\\\\?\\UNC\\" + p[2:]
        return "\\\\?\\" + p
    return p


def known_folder(csidl):
    buf = ctypes.create_unicode_buffer(512)
    try:
        ctypes.windll.shell32.SHGetFolderPathW(None, csidl, None, 0, buf)
    except Exception:
        return ""
    return buf.value


def is_admin():
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def computer_name():
    try:
        return os.environ.get("COMPUTERNAME", "")
    except Exception:
        return ""


def safe_name(s):
    s = re.sub(r'[\\/:*?"<>|]', "_", s or "").strip()
    return s or "package"


def arc_rel(d):
    """数据目录在包内的相对路径：保留 aha_doctor\\Doubao 这类层级，避免同名目录互相覆盖。"""
    rel = d.get("rel") or d.get("name") or ""
    return "/".join(safe_name(s) for s in re.split(r"[\\/]+", str(rel)) if s)


def dst_rel(d):
    """还原时相对根目录的本地路径（保持原来的层级）。"""
    rel = d.get("rel") or d.get("name") or ""
    return os.path.join(*[s for s in re.split(r"[\\/]+", str(rel)) if s]) if rel else ""


LOCK_SUFFIX = (".lock", ".lck", ".lockfile", ".pid")
LOCK_NAMES = {"singletonlock", "singletoncookie", "lockfile", "lock", "locks"}


def is_lockish(path):
    """锁文件 / 锁目录：正在运行的软件会一直占着，还原时跳过是正常的，不该报错。"""
    low = str(path or "").lower()
    b = os.path.basename(low.rstrip("\\"))
    return b.endswith(LOCK_SUFFIX) or b in LOCK_NAMES or "\\locks\\" in low or "\\lock\\" in low


def is_busy_error(e):
    """被占用 / 没权限这类错误：文件正被运行中的程序锁着，跳过即可。"""
    msg = str(e).lower()
    return (isinstance(e, PermissionError) or "errno 13" in msg or "winerror 32" in msg
            or "winerror 5" in msg or "being used by another process" in msg or "拒绝访问" in str(e))


def _make_writable(path):
    """覆盖前先去掉只读属性，否则老配置文件的 'wb' 写入会失败。"""
    try:
        if path and os.path.exists(path):
            os.chmod(path, 0o666)
    except Exception:
        pass


def dir_size(path, skip_cache=False):
    total = 0
    count = 0
    for root, dirs, files in os.walk(lp(path)):
        if skip_cache:
            dirs[:] = [d for d in dirs if d.lower() not in CACHE_DIR_NAMES]
        for f in files:
            if skip_cache and os.path.splitext(f)[1].lower() in CACHE_FILE_EXT:
                continue
            try:
                total += os.stat(os.path.join(root, f)).st_size
                count += 1
            except Exception:
                pass
    return total, count


def is_reparse(path):
    try:
        st = os.stat(path)
        return bool(getattr(st, "st_file_attributes", 0) & 0x400)
    except Exception:
        return False



DB_EXT = {".db", ".sqlite", ".sqlite3", ".db3", ".ldb", ".idx", ".mdb", ".edb", ".sqlitedb"}
IMG_EXT = {".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".ico", ".heic", ".svg", ".tga"}
VID_EXT = {".mp4", ".mov", ".avi", ".mkv", ".webm", ".flv", ".m4v", ".wmv", ".ts"}
CFG_EXT = {".json", ".ini", ".cfg", ".conf", ".config", ".xml", ".yaml", ".yml", ".toml", ".properties", ".plist"}
LOG_EXT = {".log", ".dmp", ".etl", ".tmp", ".trace", ".bak"}
PROG_EXT = {".exe", ".dll", ".pak", ".ocx", ".sys", ".node", ".asar", ".so"}
CACHE_NAME_HINT = ("cache", "gpucache", "shadercache", "code cache", "crash", "log", "logs",
                   "temp", "tmp", "update", "updater", "webdata", "backup")
GENERIC_DIR_NAMES = {
    "program files", "program files (x86)", "programdata", "users", "windows", "system32",
    "software", "apps", "programs", "common files", "app", "bin", "x64", "x86",
    "resources", "application", "applications",
}

DRIVE_ROOT_SKIP = {
    "windows", "program files", "program files (x86)", "programdata", "users",
    "$recycle.bin", "system volume information", "perflogs", "recovery", "msocache",
    "temp", "tmp", "intel", "amd", "nvidia", "documents and settings",
}

PROFILE_SKIP = {
    "appdata", "documents", "desktop", "downloads", "pictures", "music", "videos", "links",
    "favorites", "saved games", "contacts", "searches", "onedrive", "3d objects", "intelgraphicsprofiles",
    "ntuser.dat", "ntuser.ini", "application data", "local settings", "cookies", "printHood",
    "sendto", "templates", "start menu", "recent", "net hood", "netcache",
}

KIND_DESC = {
    "roaming": "用户配置（%APPDATA%）：账号、设置、界面偏好常在这里",
    "local": "本地数据（%LOCALAPPDATA%）：缓存、数据库、插件常在这里",
    "locallow": "低权限数据（%USERPROFILE%\\AppData\\LocalLow）：部分软件把配置放这",
    "programdata": "公共数据（%PROGRAMDATA%）：所有用户共用的配置、授权文件、更新包",
    "documents": "文档目录：软件导出的文件、工程、存档",
    "publicdocuments": "公共文档（Public\\Documents）：所有用户共用的软件数据",
    "public": "公共目录（%PUBLIC%）：所有用户共用的软件数据",
    "mydocuments": "「我的文档」：导出的文件与存档",
    "userprofile": "用户主目录下的同名文件夹：常见的聊天/下载/工作数据",
    "savedgames": "存档目录（Saved Games）：游戏进度",
    "desktop": "桌面：软件生成的快捷文件、临时导出",
    "sibling": "安装目录旁边的同名/相关文件夹：数据或插件",
    "drive": "磁盘根目录里的软件文件夹：自选的安装 / 数据位置",
    "registry": "注册表里记录的路径：该软件自报的数据目录",
    "manual": "手动补充的目录：扫描时没自动认出来，你确认属于这个软件，一起带走",
}


def dir_profile(path, limit=600):
    """抽样看一眼目录里都是什么文件，不遍历全盘那么慢。"""
    exts, subs, n = {}, [], 0
    try:
        for root, dirs, files in os.walk(lp(path)):
            if len(subs) < 40:
                subs.extend([d.lower() for d in dirs][:10])
            for f in files:
                e = os.path.splitext(f)[1].lower()
                exts[e] = exts.get(e, 0) + 1
                n += 1
                if n >= limit:
                    return exts, subs, n
    except Exception:
        pass
    return exts, subs, n


def describe_dir(path, kind="", name="", profile=None):
    """返回 (中文说明, 是否主要是缓存)。说明是给普通人看的：这个目录里到底存了啥。"""
    try:
        exts, subs, n = profile if profile else dir_profile(path)
    except Exception:
        exts, subs, n = {}, [], 0
    low_subs = {s.lower() for s in subs}
    cache_subs = sorted({s for s in low_subs if s in CACHE_DIR_NAMES or "cache" in s})
    total = max(1, sum(exts.values()))
    db = sum(v for k, v in exts.items() if k in DB_EXT)
    img = sum(v for k, v in exts.items() if k in IMG_EXT)
    vid = sum(v for k, v in exts.items() if k in VID_EXT)
    cfg = sum(v for k, v in exts.items() if k in CFG_EXT)
    log = sum(v for k, v in exts.items() if k in LOG_EXT)
    prog = sum(v for k, v in exts.items() if k in PROG_EXT)
    parts = []
    is_cache = False

    # 1) 先看目录结构：这类目录一看就能说清
    base = lp(path)
    has_pref = (os.path.isfile(os.path.join(base, "Local State"))
                or os.path.isfile(os.path.join(base, "Preferences")))
    if ({"local storage", "blob_storage", "indexeddb", "session storage"} & low_subs) or \
            ("default" in low_subs and has_pref):
        extra = ("；同级的 %s 等 %d 个子目录是纯缓存，照原样打包，还原后与原机一致"
                 % ("、".join(cache_subs[:3]), len(cache_subs))) if cache_subs else ""
        return ("浏览器内核（Chromium/CEF）数据目录：Default 里的 Local Storage / IndexedDB / Cookies "
                "存着登录状态、会话列表与聊天记录，必须带走" + extra), False
    if {"chats", "conversations"}.issubset(low_subs) or ("chats" in low_subs and "skills" in low_subs):
        return "会话/对话档案目录（chats、skills 等）：聊天历史、会话文件与技能配置都在这，必须带走", False

    # 2) 再看文件类型
    if db and db * 100.0 / total >= 3:
        parts.append("数据库/历史记录（%d 个 .db/.sqlite 等文件）—— 聊天记录、账号、历史数据都在里面，必须带走" % db)
    if prog and prog * 100.0 / total >= 5:
        parts.append("程序组件（%d 个 exe/dll/pak 等）—— 软件运行本体或内置资源，删了可能打不开" % prog)
    if (img + vid) and (img + vid) * 100.0 / total >= 30:
        parts.append("图片/视频资源（%d 个）—— 聊天图片、表情、封面或素材，删了通常会重新下载" % (img + vid))
        if not (db or cfg or prog):
            is_cache = True
    if cfg and cfg * 100.0 / total >= 3:
        parts.append("配置文件（%d 个 json/ini/xml 等）—— 登录状态、界面设置、快捷键" % cfg)
    if log and log * 100.0 / total >= 10:
        parts.append("日志/临时文件（%d 个）—— 只是运行记录与崩溃转储，删了不影响正常使用" % log)
        if len(parts) <= 1:
            is_cache = True
    if not parts:
        parts.append(KIND_DESC.get(kind, "该软件的用户数据目录"))
    if cache_subs and len(parts) <= 2:
        parts.append("里面含 %s 等 %d 个缓存子目录" % ("、".join(cache_subs[:3]), len(cache_subs)))
    low = (name or os.path.basename(path.rstrip("\\")) or "").lower()
    if any(k in low for k in CACHE_NAME_HINT) and ("缓存" not in "".join(parts)):
        parts.append("目录名带 Cache/Log/Update 之类，基本是纯缓存与更新包，删了不影响使用")
        is_cache = True
    return "；".join(parts), is_cache


# ---------------- 注册表 ----------------

import winreg

HIVES = {"HKLM": winreg.HKEY_LOCAL_MACHINE, "HKCU": winreg.HKEY_CURRENT_USER}

UNINSTALL_SOURCES = [
    ("HKLM", r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall", winreg.KEY_WOW64_64KEY),
    ("HKLM", r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall", winreg.KEY_WOW64_64KEY),
    ("HKCU", r"Software\Microsoft\Windows\CurrentVersion\Uninstall", 0),
    ("HKCU", r"Software\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall", 0),
]

SKIP_NAME_PAT = re.compile(
    r"(Update for|Security Update|Hotfix|^KB\d+|Microsoft Visual C\+\+.*Redistributable|"
    r"Microsoft \.NET .*(Runtime|Host|Resolver)|Windows Desktop Runtime|"
    r"Click-to-Run|Office 16 Click|Windows (SDK|Driver)|"
    r"Intel\(R\) .*Driver|Realtek|BayHubTech|NVIDIA .*Container|NVIDIA Install Application|"
    r"NVIDIA Telemetry|NVIDIA User Container|NVIDIA Session Container|NvCpl|"
    r"Microsoft Update Health|Python 3\.\d+\.\d+ .*\((64-bit|32-bit)\))",
    re.IGNORECASE,
)


def _q(key, name, default=""):
    try:
        v = winreg.QueryValueEx(key, name)[0]
        return default if v is None else v
    except OSError:
        return default


def list_programs(include_system=False):
    progs = []
    seen = set()
    for hive_name, base, wow in UNINSTALL_SOURCES:
        hive = HIVES[hive_name]
        try:
            root = winreg.OpenKey(hive, base, 0, winreg.KEY_READ | wow)
        except OSError:
            continue
        try:
            n = winreg.QueryInfoKey(root)[0]
        except OSError:
            n = 0
        for i in range(n):
            try:
                sub = winreg.EnumKey(root, i)
                k = winreg.OpenKey(root, sub, 0, winreg.KEY_READ | wow)
            except OSError:
                continue
            name = str(_q(k, "DisplayName", "")).strip()
            if not name:
                winreg.CloseKey(k)
                continue
            try:
                syscomp = int(_q(k, "SystemComponent", 0) or 0)
            except Exception:
                syscomp = 0
            parent = str(_q(k, "ParentKeyName", "")).strip()
            if not include_system and (syscomp == 1 or parent or SKIP_NAME_PAT.search(name)):
                winreg.CloseKey(k)
                continue
            version = str(_q(k, "DisplayVersion", "")).strip()
            publisher = str(_q(k, "Publisher", "")).strip()
            location = str(_q(k, "InstallLocation", "")).strip().strip('"').strip()
            uninstall = str(_q(k, "UninstallString", "")).strip()
            icon = str(_q(k, "DisplayIcon", "")).strip()
            try:
                est = int(_q(k, "EstimatedSize", 0) or 0) * 1024
            except Exception:
                est = 0
            kid = (name.lower(), version.lower())
            if kid in seen:
                winreg.CloseKey(k)
                continue
            seen.add(kid)
            winreg.CloseKey(k)
            progs.append({"name": name, "version": version, "publisher": publisher,
                          "install_location": location, "uninstall_string": uninstall,
                          "display_icon": icon, "hive": hive_name,
                          "reg_path": base + "\\" + sub, "size": est, "source": "registry"})
        winreg.CloseKey(root)
    progs = _merge_more_sources(progs, include_system)
    progs.sort(key=lambda p: p["name"].lower())
    return progs


APP_SCAN_PS = r'''
$ErrorActionPreference = "SilentlyContinue"
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$out = @{ lnk = @(); uwp = @() }
$W = New-Object -ComObject WScript.Shell
$dirs = @("$env:ProgramData\Microsoft\Windows\Start Menu\Programs",
          "$env:APPDATA\Microsoft\Windows\Start Menu\Programs",
          "$env:USERPROFILE\Desktop",
          "$env:PUBLIC\Desktop")
foreach ($d in $dirs) {
  if (-not (Test-Path -LiteralPath $d)) { continue }
  Get-ChildItem -LiteralPath $d -Recurse -Filter *.lnk | ForEach-Object {
    $s = $W.CreateShortcut($_.FullName)
    $t = $s.TargetPath
    if ($t -and $t.ToLower().EndsWith(".exe") -and (Test-Path -LiteralPath $t)) {
      $out.lnk += @{ name = $_.BaseName; target = $t; work = $s.WorkingDirectory; lnk = $_.FullName }
    }
  }
}
$out | ConvertTo-Json -Depth 4 -Compress | Set-Content -LiteralPath $args[0] -Encoding UTF8
'''


def _ps_scan_apps():
    """用 PowerShell 读开始菜单全部快捷方式目标（一次调用，约 1-3 秒）"""
    tmp = tempfile.mkdtemp(prefix="sm_scan_")
    cout = os.path.join(tmp, "out.json")
    script = os.path.join(tmp, "scan.ps1")
    try:
        with open(script, "w", encoding="utf-8-sig") as f:
            f.write(APP_SCAN_PS)
        subprocess.run([_powershell_exe(), "-NoProfile", "-NonInteractive",
                        "-ExecutionPolicy", "Bypass", "-File", script, cout],
                       capture_output=True, creationflags=0x08000000, timeout=120)
        if not os.path.isfile(cout):
            return {}
        with open(cout, "r", encoding="utf-8-sig") as f:
            txt = f.read().strip()
        return json.loads(txt) if txt else {}
    except Exception:
        return {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


APP_PATH_SOURCES = [
    (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths", winreg.KEY_WOW64_64KEY),
    (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\App Paths", winreg.KEY_WOW64_64KEY),
    (winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\App Paths", 0),
]

SKIP_EXTRA_NAME = re.compile(
    r"(^\d|uninstall|卸载|remove|help|帮助|readme|说明|update|升级|更新|crash|report|"
    r"diagnos|license|许可|website|网站|主页|homepage|support|手册|manual|changelog|"
    r"文档|sample|示例|demo|install|安装|repair|修复|feedback|反馈|配置|设置|关于|日志|"
    r"telemetry|遥测|preference|首选项|语言|快捷方式$|module docs|javaws|iediag|msoxmled|"
    r"skypeserver|^wab$|app recovery|database compare|spreadsheet compare|隐私浏览|录制管理器)",
    re.IGNORECASE,
)


def _clean_app_name(n):
    n = (n or "").strip()
    n = re.sub(r"(\s*-\s*快捷方式|\s*-\s*Shortcut)$", "", n, flags=re.IGNORECASE)
    if n.lower().endswith(".exe"):
        n = n[:-4]
    return n.strip()


def _merge_more_sources(progs, include_system=False):
    """在卸载表之外补全：开始菜单、App Paths、常见安装目录里的绿色软件"""
    known_names = {norm(p["name"]) for p in progs}
    known_dirs = set()
    for p in progs:
        loc = (p.get("install_location") or "").strip()
        if loc and os.path.isdir(loc):
            known_dirs.add(os.path.abspath(loc).lower())

    def add(name, loc, source, version="", publisher=""):
        n = _clean_app_name(name)
        if not n or len(norm(n)) < 2:
            return False
        if norm(n) in known_names:
            return False
        if SKIP_NAME_PAT.search(n) or SKIP_EXTRA_NAME.search(n):
            return False
        known_names.add(norm(n))
        progs.append({"name": n, "version": version, "publisher": publisher,
                      "install_location": loc or "", "uninstall_string": "",
                      "display_icon": "", "hive": "", "reg_path": "", "size": 0,
                      "source": source})
        return True

    # 1) 开始菜单快捷方式：显示名最友好，优先用它（绿色版、免安装版也在这里）
    data = _ps_scan_apps()
    for it in (data.get("lnk") or []):
        try:
            tgt = it.get("target") or ""
            name = it.get("name") or ""
            if not tgt or not os.path.isfile(tgt):
                continue
            low = tgt.lower()
            if "\\windows\\" in low or "\\windowsapps\\" in low:
                continue
            stem = os.path.splitext(os.path.basename(tgt))[0]
            if norm(stem) in GENERIC_EXE:
                continue
            d = os.path.dirname(tgt)
            if bad_installdir(d):
                continue
            if add(name, d, "startmenu"):
                known_dirs.add(os.path.abspath(d).lower())
        except Exception:
            continue

    # 2) App Paths：只在「这个目录还没有对应条目」时补一条，避免 Word/excel/WINWORD 这种重复
    for hive, base, wow in APP_PATH_SOURCES:
        try:
            rk = winreg.OpenKey(hive, base, 0, winreg.KEY_READ | wow)
        except OSError:
            continue
        try:
            n = winreg.QueryInfoKey(rk)[0]
        except OSError:
            n = 0
        for i in range(n):
            try:
                sub = winreg.EnumKey(rk, i)
            except OSError:
                continue
            stem = norm(os.path.splitext(sub)[0])
            if len(stem) < 2 or stem in GENERIC_EXE:
                continue
            try:
                sk = winreg.OpenKey(rk, sub, 0, winreg.KEY_READ | wow)
                v = str(_q(sk, "", "") or "").strip().strip('"')
                winreg.CloseKey(sk)
            except OSError:
                continue
            v = os.path.expandvars(_strip_icon_index(v))
            if not v or not os.path.isfile(v):
                continue
            d = os.path.dirname(v)
            if not os.path.isdir(d) or bad_installdir(d):
                continue
            if os.path.abspath(d).lower() in known_dirs:
                continue
            if add(os.path.splitext(sub)[0], d, "apppath"):
                known_dirs.add(os.path.abspath(d).lower())
        winreg.CloseKey(rk)

    # 3) 常见安装根目录 + 各盘两层目录里的绿色软件（只看文件夹里的主 exe）
    #    不写死容器名：C:\Software\Weixin、D:\play\steam、D:\工具\xxx 都在两层内
    roots = [os.environ.get("ProgramFiles", ""), os.environ.get("ProgramW6432", ""),
             os.environ.get("ProgramFiles(x86)", ""),
             os.path.join(os.environ.get("LOCALAPPDATA", ""), "Programs")]
    for drv in _drive_roots():
        for mid in _list_subdirs(drv):
            if os.path.basename(mid.rstrip("\\")).lower() in DRIVE_ROOT_SKIP:
                continue
            roots.append(mid)
            for sub in _list_subdirs(mid)[:200]:
                roots.append(sub)
            if len(roots) > 4000:
                break
    for r in roots:
        if not r or not os.path.isdir(r):
            continue
        for d in _list_subdirs(r):
            base_name = os.path.basename(d.rstrip("\\"))
            if base_name.lower() in ("windows", "windows.old", "programdata", "common files",
                                     "temp", "tmp", "$recycle.bin", "tencent", "windowsapps",
                                     "dotnet", "microsoft", "windows defender",
                                     "internet explorer", "windows media player", "windows mail",
                                     "windows photo viewer"):
                continue
            if "\\plug-ins\\" in d.lower() or "\\plugins\\" in d.lower():
                continue
            if os.path.abspath(d).lower() in known_dirs:
                continue
            try:
                exes = [f for f in os.listdir(lp(d))
                        if f.lower().endswith(".exe") and os.path.isfile(os.path.join(d, f))]
            except Exception:
                continue
            real = [f for f in exes if norm(os.path.splitext(f)[0]) not in GENERIC_EXE]
            if not real:
                continue
            biggest = max(real, key=lambda f: os.path.getsize(os.path.join(d, f)))
            if add(base_name if len(base_name) >= 2 else os.path.splitext(biggest)[0],
                   d, "portable"):
                known_dirs.add(os.path.abspath(d).lower())

    # 4) 非系统盘根目录下的一层文件夹（很多人把软件直接解压到 D:\工具\xxx）
    sys_drv = os.environ.get("SystemDrive", "C:").rstrip("\\").lower() + "\\"
    for drv in _drive_roots():
        if drv.lower() == sys_drv:
            continue
        for d in _list_subdirs(drv):
            if os.path.abspath(d).lower() in known_dirs:
                continue
            if "\\plug-ins\\" in d.lower() or "\\plugins\\" in d.lower():
                continue
            try:
                exes = [f for f in os.listdir(lp(d))
                        if f.lower().endswith(".exe") and os.path.isfile(os.path.join(d, f))]
            except Exception:
                continue
            real = [f for f in exes if norm(os.path.splitext(f)[0]) not in GENERIC_EXE]
            if not real:
                continue
            base_name = os.path.basename(d.rstrip("\\"))
            biggest = max(real, key=lambda f: os.path.getsize(os.path.join(d, f)))
            if add(base_name if len(base_name) >= 2 else os.path.splitext(biggest)[0],
                   d, "portable"):
                known_dirs.add(os.path.abspath(d).lower())
    return progs


def _strip_quotes(s):
    s = (s or "").strip()
    if s.startswith('"'):
        s = s[1:]
        i = s.find('"')
        return s[:i] if i > 0 else s
    m = re.match(r"(.+?\.exe)", s, re.IGNORECASE)
    if m:
        return m.group(1)
    return s.split(" ")[0]


def is_temp_path(p):
    """TEMP / TMP 下的目录：只是安装临时解包，不该当成软件数据带走"""
    if not p:
        return False
    low = os.path.abspath(lp(p)).lower().rstrip("\\")
    for t in (os.environ.get("TEMP"), os.environ.get("TMP"), tempfile.gettempdir()):
        if not t:
            continue
        tl = os.path.abspath(lp(t)).lower().rstrip("\\")
        if tl and (low == tl or low.startswith(tl + "\\")):
            return True
    return False


def _strip_icon_index(s):
    """去掉图标索引后缀：'C:\\a\\QQ.exe,0' → 'C:\\a\\QQ.exe'（QQ、微信这类爱这么写）"""
    s = (s or "").strip()
    m = re.match(r'^"?(.+?)"?\s*,\s*-?\d+\s*$', s)
    if m:
        return m.group(1).strip()
    return s


def _drive_roots():
    """所有可访问盘符（C:\\ D:\\ E:\\ …），用来找装在非系统盘的绿色软件"""
    out = []
    try:
        for c in "CDEFGHIJKLMNOPQRSTUVWXYZ":
            root = c + ":\\"
            if os.path.isdir(root):
                out.append(root)
    except Exception:
        pass
    return out


def _list_subdirs(root):
    try:
        return [os.path.join(root, d) for d in os.listdir(lp(root)) if os.path.isdir(os.path.join(root, d))]
    except Exception:
        return []


def _hard_bad(p):
    """绝对不能当安装目录的：MSI 包缓存、系统目录、GUID 目录、临时解包目录"""
    if not p:
        return True
    low = os.path.abspath(lp(p)).lower().rstrip("\\")
    if any(h in low for h in ("\\package cache\\", "\\windowsapps\\", "$recycle.bin",
                             "\\windows\\installer\\", "\\temp\\", "\\tmp\\")):
        return True
    b = os.path.basename(low)
    if b.startswith("{") and b.endswith("}"):
        return True
    # Windows / System32 / SysWOW64 这些系统目录里也有同名 exe，不能当安装目录
    sysroot = os.path.abspath(lp(os.environ.get("SystemRoot", "C:\\Windows"))).lower().rstrip("\\")
    if sysroot and (low == sysroot or low.startswith(sysroot + "\\")):
        return True
    if len(low) <= 3:
        return True
    return False


def resolve_install_dir(prog):
    loc = (prog.get("install_location") or "").strip().strip('"')
    if loc:
        loc = os.path.expandvars(loc)
        if os.path.isdir(loc):
            # 目录确实存在就认它（哪怕在 Common Files 里），只排除 MSI 缓存/临时/GUID
            if not _hard_bad(loc):
                return os.path.abspath(loc)
        if os.path.isfile(loc):
            d = os.path.dirname(loc)
            if os.path.isdir(d) and not _hard_bad(d):
                return os.path.abspath(d)
    # 注册表里的图标/卸载命令：去掉 ",0" 这种图标索引，路径不存在也允许用它的父目录
    for fld in ("display_icon", "uninstall_string"):
        raw = prog.get(fld) or ""
        v = _strip_quotes(_strip_icon_index(raw))
        if not v:
            continue
        v = os.path.expandvars(v)
        if os.path.isfile(v):
            d = os.path.dirname(v)
            if os.path.isdir(d) and not _hard_bad(d):
                return _unwrap_bindir(os.path.abspath(d))
        d = os.path.dirname(v.rstrip("\\"))
        if os.path.isdir(d) and not _hard_bad(d):
            # 父目录在、但文件不在（软件被挪过/改名过），只要里面有 exe 就认它
            try:
                has_exe = any(f.lower().endswith(".exe") for f in os.listdir(lp(d)))
            except Exception:
                has_exe = False
            if has_exe:
                return _unwrap_bindir(os.path.abspath(d))
    # App Paths：QQ、微信这类经常只在这里留一份真实路径
    ap = app_paths_lookup(_candidate_names(prog, ""))
    if ap:
        return ap
    # 开始菜单 / 桌面的快捷方式反查：装在任意位置都能定位（不依赖任何写死的目录名）
    sd = install_dir_from_shortcuts(prog)
    if sd:
        return sd
    # 兜底：在常见安装位置里找同名文件夹（先精确匹配，再按名字里的单词找）
    cands = _candidate_names(prog, "")
    toks = _search_tokens(prog)
    roots = [os.environ.get("ProgramFiles", ""), os.environ.get("ProgramW6432", ""),
             os.environ.get("ProgramFiles(x86)", ""),
             os.path.join(os.environ.get("LOCALAPPDATA", ""), "Programs"),
             os.environ.get("LOCALAPPDATA", ""),
             os.environ.get("USERPROFILE", "")]
    # 每个磁盘根目录 + 下面一层：C:\Software\Weixin、D:\play\steam、C:\PDF\Acrobat DC
    # 这种「自己起的容器名」都落在两层内，不需要预先知道容器叫什么
    roots.extend(_drive_roots())
    # 一次扫两层：靠打分选出最像安装目录的那个（同时兼顾「厂商\产品」结构）
    best = _scan_dirs(roots, 2, cands, toks, use_tokens=True, app_name=prog.get("name", ""))
    return _unwrap_bindir(best)


BIN_DIRS = ("bin", "bin32", "bin64", "x64", "x86", "amd64", "app", "application", "program")


def _unwrap_bindir(path):
    """装到 bin / x64 这种子目录时，退回上一层，否则会只搬走程序文件、丢掉同级资源"""
    if not path:
        return path
    p = path.rstrip("\\")
    b = os.path.basename(p).lower()
    parent = os.path.dirname(p)
    if b in BIN_DIRS and os.path.isdir(parent) and len(parent.rstrip("\\")) > 3:
        try:
            names = os.listdir(lp(parent))
        except Exception:
            return path
        if any(os.path.isdir(os.path.join(parent, x)) for x in names) or \
           any(x.lower().endswith(".exe") for x in names):
            return os.path.abspath(parent)
    return path


SHORTCUT_IDX = {"built": False, "idx": {}}


def _shortcut_index():
    """把开始菜单 / 桌面里的 .lnk 一次性解析成 {小写名字: (lnk, 目标 exe)}，全程只用一次"""
    if SHORTCUT_IDX["built"]:
        return SHORTCUT_IDX["idx"]
    SHORTCUT_IDX["built"] = True
    idx = {}
    try:
        roots = [known_folder(0x02), known_folder(0x17), known_folder(0x10), known_folder(0x19)]
        paths = []
        for root in roots:
            if not root or not os.path.isdir(root):
                continue
            for dp, dn, fns in os.walk(root):
                dn[:] = [x for x in dn if x.lower() not in ("cache", "temp", "tmp")]
                for fn in fns:
                    if fn.lower().endswith(".lnk"):
                        paths.append(os.path.join(dp, fn))
                if len(paths) >= 1500:
                    break
        paths = paths[:1500]
        if paths:
            for d in (ps_run({"items": paths}) or []):
                t = os.path.expandvars((d.get("target") or "").strip())
                lnk = d.get("lnk") or ""
                if not t or not t.lower().endswith(".exe"):
                    continue
                stem = norm(os.path.splitext(os.path.basename(lnk))[0])
                if stem and stem not in idx:
                    idx[stem] = (lnk, t)
    except Exception:
        idx = {}
    SHORTCUT_IDX["idx"] = idx
    return idx


def install_dir_from_shortcuts(prog):
    """快捷方式 → 目标 exe → 所在目录：装在 D:\\play\\steam、C:\\PDF\\Acrobat DC 这类自选位置也能找到"""
    idx = _shortcut_index()
    if not idx:
        return ""
    ident = identity(prog, "")
    best = ("", 0.0)
    for stem, (lnk, target) in idx.items():
        if not os.path.isfile(target):
            continue
        sc = _name_score(stem, ident)
        if sc < 0.85:
            sc = _name_score(os.path.splitext(os.path.basename(target))[0], ident)
            if sc < 0.85:
                continue
        d = os.path.dirname(target)
        if not os.path.isdir(d) or _hard_bad(d) or is_temp_path(d):
            continue
        if sc > best[1]:
            best = (_unwrap_bindir(os.path.abspath(d)), sc)
    return best[0]


GENERIC_TOKEN = {
    "software", "program", "programs", "suite", "tools", "tool", "utility", "utilities",
    "support", "device", "devices", "driver", "drivers", "package", "packages",
    "application", "applications", "product", "products", "system", "client", "server",
    "manager", "service", "services", "edition", "version", "studio", "runtime",
    "desktop", "classic", "preview", "reader", "viewer", "browser", "editor", "player",
    "windows", "microsoft", "files", "file", "data", "user", "users", "local", "roaming",
    "common", "installer", "install", "setup", "update", "updater", "helper", "crash",
    "config", "settings", "cache", "temp", "tmp", "public", "default", "documents",
}


def _scan_dirs(roots, depth, cands, toks, use_tokens=True, app_name=""):
    """按目录名与软件名的匹配度打分，返回得分最高的目录（找不到返回空串）"""
    best = ("", 0.0)
    probe = {"raw": set(), "strong": set(cands), "core": {_core_name(c) for c in cands},
             "words": set(toks)}
    for r in roots:
        if not r or not os.path.isdir(r):
            continue
        for mid in _list_subdirs(r):
            mbase = os.path.basename(mid.rstrip("\\"))
            if mbase.lower() in ("windows", "windows.old", "programdata", "$recycle.bin",
                                 "users", "perflogs", "system volume information",
                                 "program files", "program files (x86)"):
                continue
            cands_dirs = [(mid, mbase, 1)]
            if depth >= 2:
                for sub in _list_subdirs(mid):
                    cands_dirs.append((sub, os.path.basename(sub.rstrip("\\")), 2))
            for path, base, level in cands_dirs:
                n = norm(base)
                if not n or len(n) < 2:
                    continue
                score = 0.0
                if n in cands:
                    score = 3.0
                elif len(n) >= 5 and any(len(c) >= 5 and c in n for c in cands):
                    score = 2.0
                elif use_tokens and (n in toks or (len(n) >= 6 and any(t in n for t in toks))):
                    score = 1.0 if n in toks else 0.8
                if score <= 0 and use_tokens:
                    # 名字对不上的情况（中文名 ↔ 英文目录、中英缩写）交给通用相似度打分兜底
                    sc = _name_score(base, probe)
                    if sc >= SCORE_ROOT:
                        score = sc * 4.0
                if score <= 0:
                    continue
                try:
                    has_exe = any(f.lower().endswith(".exe") for f in os.listdir(lp(path)))
                except Exception:
                    has_exe = False
                if not has_exe:
                    continue
                # 目录里有「和软件同名的 exe」最可信（Steam 目录里的 steam.exe 胜过 Steam++ 目录）
                try:
                    stems = {norm(os.path.splitext(f)[0]) for f in os.listdir(lp(path))
                             if f.lower().endswith(".exe")}
                except Exception:
                    stems = set()
                if stems & (cands | toks):
                    score += 1.2
                # 自带数字后缀的目录（Python313）在软件名没写这个数字时降权
                if re.search(r"\d{2,}", n) and not re.search(r"\d{2,}", norm(app_name or "")):
                    score -= 0.6
                # 名字结尾的那个词命中（Python Launcher → Launcher 目录）优先
                if score < 3 and n in toks and prog_ends_with(app_name, base):
                    score += 1.0
                score += 0.4 if level == 2 else 0.0
                score -= min(len(n), 30) / 100.0
                if score > best[1]:
                    best = (os.path.abspath(path), score)
    return best[0]


def prog_ends_with(name, word):
    parts = [norm(w) for w in re.split(r"[\s\-_/\\,，。:：()（）\[\]|]+", name or "") if w.strip()]
    return bool(parts) and parts[-1] == norm(word)


def _dir_has_matching_exe(d, cands):
    """目录里有没有一个 exe，文件名（去后缀）正好是候选名（如 QQ.exe / WeChat.exe）"""
    try:
        for f in os.listdir(lp(d)):
            if not f.lower().endswith(".exe"):
                continue
            stem = norm(os.path.splitext(f)[0])
            if stem in GENERIC_EXE:
                continue
            if stem in cands:
                return True
    except Exception:
        pass
    return False


def app_paths_lookup(cands):
    try:
        import winreg
    except Exception:
        return ""
    roots = [(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths"),
             (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\App Paths"),
             (winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\App Paths")]
    for hive, root in roots:
        try:
            with winreg.OpenKey(hive, root) as rk:
                n = winreg.QueryInfoKey(rk)[0]
                for i in range(n):
                    try:
                        sub = winreg.EnumKey(rk, i)
                        stem = norm(os.path.splitext(sub)[0])
                        if stem in GENERIC_EXE:
                            continue
                        if not (stem in cands or any(c in stem for c in cands if len(c) >= 4)):
                            continue
                        with winreg.OpenKey(rk, root + "\\" + sub) as sk:
                            try:
                                v, _t = winreg.QueryValueEx(sk, "")
                            except Exception:
                                v = ""
                        v = os.path.expandvars(_strip_quotes(v or ""))
                        if v and os.path.isfile(v):
                            d = os.path.dirname(v)
                            if os.path.isdir(d) and not bad_installdir(d):
                                return os.path.abspath(d)
                    except Exception:
                        continue
        except Exception:
            continue
    return ""


GENERIC_EXE = {
    "uninstall", "unins000", "unins001", "unins002", "unwise", "setup", "install",
    "installer", "installhelper", "update", "updater", "updated", "upgrade",
    "helper", "launcher", "start", "run", "main", "app", "crashpad_handler",
    "crashreport", "report", "diagnostics", "uninst",
}


# ---------------- 通用身份识别（不写死任何软件名） ----------------
# 靠软件自己的证据认自己：显示名、注册表键名、卸载/图标里的 exe 名、安装目录名、
# 目录里所有 exe 的文件名、exe 版本资源里的官方英文产品名、发布商、快捷方式名。
# 再按相似度打分，去认 AppData / 文档 / 存档 / 盘符根目录里属于它的目录 —— 任何软件都走这套。

VER_CACHE = {}
IDENT_CACHE = {}

_GENERIC_WORD = GENERIC_TOKEN | {
    "app", "apps", "x64", "x86", "amd64", "arm64", "win", "win64", "win32", "windows",
    "setup", "install", "installer", "portable", "green", "lite", "pro", "plus", "beta",
    "stable", "new", "old", "test", "debug", "release", "uninstall", "unins000", "update",
    "updater", "launcher", "start", "main", "core", "bin", "lib", "obj", "tmp", "temp",
    "home", "root", "misc", "other", "extra", "backup", "profile", "account", "helper",
    "service", "client", "server", "edition", "runtime", "native", "host", "package",
}

_VER_RE = re.compile(r"\d+(?:\.\d+)+")
_CMP_VER_RE = re.compile(r"^(v?\d+(\.\d+)*|x64|x86|amd64|64bit|32bit)$", re.IGNORECASE)


def _core_name(n):
    """去掉版本号/位数，留下核心名字：python313 → python、v2rayn-windows-64 → v2raynwindows"""
    n = _VER_RE.sub("", n or "")
    n = re.sub(r"(x64|x86|amd64|arm64|64bit|32bit)", "", n)
    return n


def _clean_raw(s):
    """只去掉空格/下划线/横杠/点，保留 + # @ 这类符号（用来区分 Steam 与 Steam++）"""
    return re.sub(r"[\s_\-\.]+", "", (s or "").strip().lower())


def _split_words(s):
    return [w for w in re.split(r"[\s\-_\.\\/+,，。:：；;()（）\[\]|+'\"~!@#$%^&*=<>?]+", s or "") if w]


def _file_size(p):
    try:
        return os.path.getsize(p)
    except Exception:
        return 0


def _win_version_strings(path):
    """读 exe 自带的产品名/公司名（纯 ctypes，不依赖别的东西）。
    中文显示名的软件，产品名常常正是英文目录名。"""
    if not path:
        return {}
    key = path.lower()
    if key in VER_CACHE:
        return VER_CACHE[key]
    out = {}
    try:
        from ctypes import wintypes
        ver = ctypes.WinDLL("version", use_last_error=True)
        ver.GetFileVersionInfoSizeW.argtypes = [wintypes.LPCWSTR, ctypes.POINTER(wintypes.DWORD)]
        ver.GetFileVersionInfoSizeW.restype = wintypes.DWORD
        ver.GetFileVersionInfoW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD,
                                            ctypes.c_void_p]
        ver.GetFileVersionInfoW.restype = wintypes.BOOL
        ver.VerQueryValueW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR,
                                       ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(wintypes.UINT)]
        ver.VerQueryValueW.restype = wintypes.BOOL
        size = ver.GetFileVersionInfoSizeW(path, None)
        if not size:
            VER_CACHE[key] = out
            return out
        buf = ctypes.create_string_buffer(int(size))
        if not ver.GetFileVersionInfoW(path, 0, int(size), buf):
            VER_CACHE[key] = out
            return out
        handle = ctypes.cast(buf, ctypes.c_void_p)
        pv = ctypes.c_void_p()
        ln = wintypes.UINT()
        langs = []
        if ver.VerQueryValueW(handle, "\\VarFileInfo\\Translation",
                              ctypes.byref(pv), ctypes.byref(ln)) and ln.value >= 4 and pv.value:
            cnt = ln.value // 4
            pairs = ctypes.cast(pv, ctypes.POINTER(wintypes.WORD))
            for i in range(min(cnt, 8)):
                langs.append("%04x%04x" % (pairs[i * 2], pairs[i * 2 + 1]))
        if not langs:
            langs = ["040904b0", "080404b0"]
        for lang in langs:
            got = False
            for k in ("ProductName", "FileDescription", "InternalName", "OriginalFilename",
                      "CompanyName"):
                pv = ctypes.c_void_p()
                ln = wintypes.UINT()
                if ver.VerQueryValueW(handle, "\\StringFileInfo\\%s\\%s" % (lang, k),
                                      ctypes.byref(pv), ctypes.byref(ln)) and pv.value and ln.value:
                    s = ctypes.wstring_at(pv, ln.value).strip().strip("\x00").strip()
                    if s and k not in out:
                        out[k] = s
                        got = True
            if got:
                break
    except Exception:
        out = {}
    VER_CACHE[key] = out
    return out


def _exe_stems(root, depth=2, limit=40):
    """目录里的 exe 文件名（去后缀）。程序文件名通常就是软件的英文名"""
    stems = []
    try:
        top = [f for f in os.listdir(lp(root)) if f.lower().endswith(".exe")]
    except Exception:
        return stems
    top.sort(key=lambda f: -_file_size(os.path.join(root, f)))
    stems.extend(os.path.splitext(f)[0] for f in top)
    if depth >= 2 and len(stems) < limit:
        for sub in _list_subdirs(root)[:16]:
            b = os.path.basename(sub).lower()
            if b in ("resources", "locales", "plugins", "addons", "uninstall", "update",
                     "updater", "crashpad", "node_modules", "python", "jre", "runtime"):
                continue
            try:
                for f in os.listdir(lp(sub)):
                    if f.lower().endswith(".exe"):
                        stems.append(os.path.splitext(f)[0])
            except Exception:
                continue
            if len(stems) >= limit * 2:
                break
    return stems[:limit]


TEXT_HINT_EXT = {".ini", ".cfg", ".conf", ".config", ".json", ".xml", ".yaml", ".yml",
                 ".toml", ".txt", ".log", ".properties", ".plist", ".settings", ".js", ".lua"}


def _dir_mentions(dirp, needles, budget=1.2, max_files=36):
    """目录浅层的小配置文件里有没有提到 needles（安装路径 / 主程序名）。

    通用依据：软件往自己的数据目录写配置时，常把安装路径或 exe 名留在里面，
    所以「中文名软件 + 完全不像的英文目录」也能靠内容对上，不需要任何名单。
    """
    if not needles:
        return False
    t0 = time.time()
    base_depth = dirp.rstrip("\\").count("\\")
    seen = [0]

    def scan(base, depth):
        if depth > 2:
            return False
        try:
            with os.scandir(base) as it:
                for e in it:
                    if time.time() - t0 > budget:
                        return False
                    try:
                        if e.is_dir(follow_symlinks=False):
                            if scan(e.path, depth + 1):
                                return True
                            continue
                        if not e.is_file(follow_symlinks=False):
                            continue
                        if os.path.splitext(e.name)[1].lower() not in TEXT_HINT_EXT:
                            continue
                        if e.stat(follow_symlinks=False).st_size > 256 * 1024:
                            continue
                        seen[0] += 1
                        if seen[0] > max_files:
                            return False
                        blob = open(e.path, "rb").read().decode("utf-8", "ignore").lower()
                    except Exception:
                        continue
                    if any(x in blob for x in needles):
                        return True
        except Exception:
            return False
        return False

    return scan(dirp, 0)


def reg_path_hints(reg_keys, install_dir, known, limit=10):
    """软件自己写在注册表里的目录路径（如 火绒 DataPath=C:\\ProgramData\\Huorong\\Sysdiag）。
    这是软件自己交代的，不用任何名字对照表。"""
    try:
        import winreg
    except Exception:
        return []
    roots = {"HKCU": winreg.HKEY_CURRENT_USER, "HKLM": winreg.HKEY_LOCAL_MACHINE,
             "HKCR": winreg.HKEY_CLASSES_ROOT}
    ip = os.path.abspath(install_dir).lower() if install_dir else ""
    win = os.environ.get("WINDIR", r"C:\Windows").lower()
    out = []
    seen = set(known or ())

    def take(v):
        if not isinstance(v, str) or len(v) < 6:
            return
        s = v.strip().strip('"').strip()
        if s.startswith("\\\\"):
            return
        if not (re.match(r"^[A-Za-z]:[\\/]", s) or s.upper().startswith("%")):
            return
        s = os.path.expandvars(s)
        if not re.match(r"^[A-Za-z]:[\\/]", s) or not os.path.isdir(s):
            return
        p = os.path.abspath(s.rstrip("\\"))
        low = p.lower()
        if low in seen or low == ip:
            return
        if any(low.startswith(s + "\\") for s in seen if s):
            return          # 已经在某个已收录的数据目录里面（如 Local\Doubao\User Data）
        if ip and (low.startswith(ip + "\\") or ip.startswith(low + "\\")):
            return
        if low.startswith(win + "\\") or "\\windows\\" in low + "\\":
            return
        if "\\program files" in low or "\\program files (x86)" in low:
            return
        # 桌面/下载/图片这类「用户自己的地方」不进：软件里填过下载目录不代表要把它们搬走
        for bad in ("\\desktop\\", "\\downloads\\", "\\pictures\\", "\\videos\\",
                    "\\music\\", "\\onedrive\\"):
            if bad in low + "\\":
                return
        for needle in ("\\appdata\\roaming", "\\appdata\\local", "\\programdata",
                       "\\documents", "\\saved games", "\\desktop"):
            if needle in low:
                seen.add(low)
                out.append(p)
                return
        up = os.environ.get("USERPROFILE", "").lower().rstrip("\\")
        if up and low.startswith(up + "\\") and low.count("\\") >= up.count("\\") + 1:
            seen.add(low)
            out.append(p)

    def walk(hive, path, depth):
        root = roots.get(hive)
        if root is None:
            return
        try:
            k = winreg.OpenKey(root, path, 0, winreg.KEY_READ)
        except Exception:
            return
        try:
            i = 0
            while True:
                try:
                    _, data, _ = winreg.EnumValue(k, i)
                except OSError:
                    break
                i += 1
                take(data)
            if depth <= 0:
                return
            n = winreg.QueryInfoKey(k)[0]
            for j in range(min(n, 50)):
                try:
                    sub = winreg.EnumKey(k, j)
                except Exception:
                    break
                walk(hive, path + "\\" + sub, depth - 1)
        finally:
            try:
                k.Close()
            except Exception:
                pass

    for kk in (reg_keys or [])[:8]:
        walk(kk.get("hive", ""), kk.get("path", ""), 2)
        if len(out) >= limit:
            break
    return out[:limit]


def _exe_sized(root, depth=2, limit=40):
    """[(exe 名, 字节数)]，按体积降序。主程序通常是大文件；小工具 exe 不该被当成软件名。"""
    out = []
    try:
        for f in os.listdir(lp(root)):
            if f.lower().endswith(".exe"):
                out.append((os.path.splitext(f)[0], _file_size(os.path.join(root, f))))
    except Exception:
        return out
    out.sort(key=lambda x: -x[1])
    if depth >= 2 and len(out) < limit:
        for sub in _list_subdirs(root)[:16]:
            b = os.path.basename(sub).lower()
            if b in ("resources", "locales", "plugins", "addons", "uninstall", "update",
                     "updater", "crashpad", "node_modules", "python", "jre", "runtime"):
                continue
            try:
                for f in os.listdir(lp(sub)):
                    if f.lower().endswith(".exe"):
                        out.append((os.path.splitext(f)[0],
                                    _file_size(os.path.join(sub, f))))
            except Exception:
                continue
            if len(out) >= limit * 2:
                break
    return out[:limit]


def identity(prog, install_dir=""):
    """把这个软件的「名字证据」凑齐。任何软件都不靠写死的名单也能认出自己的目录。"""
    key = (prog.get("name", ""), prog.get("install_location", ""),
           prog.get("reg_path", ""), install_dir or "")
    if key in IDENT_CACHE:
        return IDENT_CACHE[key]
    ident = {"raw": set(), "clean": set(), "strong": set(), "core": set(), "words": set(),
             "exes": set(), "pub": set(), "pub_words": set()}

    def add_name(s):
        s = (s or "").strip().strip("\"'")
        s = re.sub(r"\.(exe|dll|sys)$", "", s, flags=re.IGNORECASE).strip()
        if not s or len(s) > 90:
            return
        n = norm(s)
        if len(n) < 2:
            return
        ident["raw"].add(s.lower())
        ident["clean"].add(_clean_raw(s))
        ident["strong"].add(n)
        ident["core"].add(_core_name(n))
        for w in _split_words(s):
            wl = w.lower()
            if len(wl) >= 3 and wl not in _GENERIC_WORD and not _CMP_VER_RE.match(wl):
                ident["words"].add(wl)

    def add_pub(s, words_only=False):
        n = norm(s)
        if len(n) < 3 or n in _GENERIC_WORD:
            return
        ident["pub"].add(n)
        for w in _split_words(s):
            wl = w.lower()
            if len(wl) >= 4 and wl not in _GENERIC_WORD:
                ident["pub_words"].add(wl)

    add_name(prog.get("name", ""))
    add_name(re.sub(r"\s*[\(（](x64|x86|64-bit|32-bit|64-位|32-位)[\)）]", "", prog.get("name", ""),
                    flags=re.IGNORECASE))
    add_name(re.sub(r"\s+v?\d+[\d\.]*.*$", "", prog.get("name", ""), flags=re.IGNORECASE))
    add_pub(prog.get("publisher", ""))
    # 注册表键名：英文产品名最常见的来源（MSI 的 {GUID} 键跳过）
    leaf = (prog.get("reg_path") or "").split("\\")[-1].strip()
    if leaf and not leaf.startswith("{") and len(norm(leaf)) >= 2:
        add_name(leaf)
    # 卸载命令 / 显示图标里的 exe 名
    for fld in ("uninstall_string", "display_icon"):
        v = _strip_quotes(_strip_icon_index(os.path.expandvars(prog.get(fld) or "")))
        if v.lower().endswith(".exe"):
            st = os.path.splitext(os.path.basename(v))[0]
            if norm(st) not in GENERIC_EXE:
                add_name(st)
    # 安装目录名 + 目录里所有 exe 名 + exe 的版本资源（官方英文产品名）
    if install_dir and os.path.isdir(install_dir):
        lb = os.path.basename(install_dir.rstrip("\\"))
        if norm(lb) not in GENERIC_DIR_NAMES:
            add_name(lb)
        for st, sz in _exe_sized(install_dir):
            ns = norm(st)
            if len(ns) < 2 or ns in GENERIC_EXE:
                continue
            ident["exes"].add(ns)
            # 只有像主程序的 exe（体积大 / 名字特别长）才当「软件名」，
            # 否则本机工具名会被误当成产品名（火绒的 CrashDump.exe → 误认 CrashDumps 目录）
            if sz >= 512 * 1024 or len(ns) >= 14:
                add_name(st)
        for st in list(ident["exes"])[:6]:
            vi = _win_version_strings(os.path.join(install_dir, st + ".exe"))
            for k in ("ProductName", "FileDescription", "InternalName", "OriginalFilename"):
                add_name(os.path.splitext(vi.get(k, ""))[0])
            if vi.get("CompanyName"):
                add_pub(vi.get("CompanyName"))
    IDENT_CACHE[key] = ident
    return ident


SCORE_ROOT = 0.80        # AppData / 文档 一层目录的门槛
SCORE_CONTAINER = 0.90   # 共享容器（Tencent\QQ、Adobe\Acrobat）里一层的门槛
SCORE_DRIVE = 0.95       # 磁盘根目录：只认完全一致


def _name_score(name, ident, words=None):
    """0~1：目录名与这个软件的契合度（1.0 = 就是它）。名字对不上时靠单词重叠 + 版本资源兜。"""
    raw = (name or "").strip().lower()
    n = norm(name)
    sr = _clean_raw(name)
    if not n or len(n) < 2:
        return 0.0
    if n in _GENERIC_WORD or n in GENERIC_DIR_NAMES:
        return 0.0
    if raw in ident.get("raw", ()) or sr in (ident.get("clean") or ()):
        return 1.0
    c = _core_name(sr)
    if c and c in ident["core"]:
        return 0.95
    best = 0.0
    for s in ident["strong"]:
        if len(s) < 4:
            continue
        if s in sr:
            # 目录名在软件名之外还多了「纯符号」：Steam++ / XXX++ 通常是另一个产品，不算
            rem = sr.replace(s, "", 1)
            if rem and not re.search(r"[0-9a-z\u4e00-\u9fa5]", rem):
                continue
            best = max(best, 0.86 if len(s) * 100 >= len(sr) * 55 else 0.80)
        elif sr in s and len(sr) * 100 >= len(s) * 55:
            best = max(best, 0.82)
        elif sr.startswith(s) and len(s) * 100 >= len(sr) * 50:
            best = max(best, 0.84)
        elif sr.endswith(s) and len(s) * 100 >= len(sr) * 50:
            best = max(best, 0.84)
    # 单词级重叠：Foxit Reader 目录 vs FoxitPDFReader.exe，中文名与英文目录名对不上时最有用
    wset = words if words is not None else ident["words"]
    nw = {w.lower() for w in _split_words(name) if len(w) >= 3}
    shared = {w for w in nw if w in wset}
    if len(shared) >= 2:
        best = max(best, 0.80)
    elif len(shared) == 1:
        w = next(iter(shared))
        if len(w) >= 6:
            best = max(best, 0.74)
        elif len(w) >= 5 and len(nw) <= 1:
            best = max(best, 0.70)
    # 词是目录名的一部分（PurrSoftHub ⊃ purrsoft）：只当「像」的弱线索，不当确定命中
    for w in wset:
        if len(w) >= 5 and w in sr:
            rem = sr.replace(w, "", 1)
            if rem and not re.search(r"[0-9a-z\u4e00-\u9fa5]", rem):
                continue
            best = max(best, 0.74)
    return best


def _candidate_names(prog, install_dir=""):
    """注册表 / App Paths 反查用的候选名：名字证据 + 拆出来的词（弱线索）"""
    ident = identity(prog, install_dir)
    cands = set(ident["strong"]) | set(ident["pub"])
    for w in ident["words"] | ident["pub_words"]:
        if len(w) >= 4:
            cands.add(w)
    return {c for c in cands if len(c) >= 2}


def _search_tokens(prog):
    """把显示名拆成单词当线索：'Python Launcher' → python / launcher，'v2rayN 版本 7.24.1' → v2rayn"""
    toks = set()
    for w in _split_words(prog.get("name", "")):
        n = norm(w)
        if len(n) >= 4 and n not in GENERIC_TOKEN and not re.match(r"^\d+$", n):
            toks.add(n)
    return toks


def _match(name, cands):
    n = norm(name)
    if not n or len(n) < 2:
        return False
    if n in cands:
        return True
    if len(n) >= 5:
        for c in cands:
            # 只允许「候选名是观察到名字的一部分」（如候选 adobephotoshop ⊂ Adobe Photoshop 2024）
            # 不允许反过来的包含关系，否则 Installer 会被 eaappinstaller 带进来
            if len(c) >= 5 and c in n:
                return True
    return False


BAD_DIR_HINTS = ("\\package cache\\", "\\windows\\", "\\windowsapps\\", "$recycle.bin",
                 "\\installer\\", "\\common files\\")


def bad_installdir(p):
    """明显不是真正安装目录的位置：MSI 缓存、安装器临时目录、系统目录。"""
    if not p:
        return True
    low = p.lower()
    if any(h in low for h in BAD_DIR_HINTS):
        return True
    b = os.path.basename(p.rstrip("\\"))
    if b.startswith("{") and b.endswith("}"):
        return True
    if len(p.rstrip("\\")) <= 3:
        return True
    return False


def _rel_to_base(kind, p, bases):
    """数据目录相对它所属根目录的路径（保留 aha_doctor\\Doubao 这种层级，还原才不回错地方）。"""
    base = (bases or {}).get(kind) or ""
    try:
        if base and os.path.isdir(base):
            bp = os.path.abspath(base).lower().rstrip("\\")
            key = os.path.abspath(p).lower().rstrip("\\")
            if key.startswith(bp + "\\"):
                return os.path.relpath(os.path.abspath(p), os.path.abspath(base))
    except Exception:
        pass
    return os.path.basename(os.path.abspath(p).rstrip("\\"))


def find_data_dirs(prog, install_dir):
    """找出这个软件所有可能相关的目录（宁可多带，不可漏带）。
    不靠写死的软件名：靠它自己的 exe 名、注册表键名、版本资源、发布商，按相似度认目录。"""
    ldr = os.environ.get("LOCALAPPDATA", "")
    rd = os.environ.get("APPDATA", "")
    up = os.environ.get("USERPROFILE", "")
    pd = os.environ.get("PROGRAMDATA", "")
    pub = os.environ.get("PUBLIC", os.path.join("C:\\Users", "Public"))
    docs = os.path.join(known_folder(0x05) or up, "Documents")
    roots = [
        ("roaming", rd),
        ("local", ldr),
        ("local", os.path.join(ldr, "Programs")),
        ("locallow", os.path.join(up, "AppData", "LocalLow")),
        ("programdata", pd),
        ("documents", docs),
        ("documents", os.path.join(docs, "My Games")),
        ("publicdocuments", os.path.join(pub, "Documents")),
        ("userprofile", up),
        ("userprofile", os.path.join(up, ".config")),          # Linux/跨平台应用（VS Code、Git 等）也认这一套
        ("userprofile", os.path.join(up, ".local", "share")),
        ("public", pub),                                      # 所有用户共用目录，软件常把共享数据写在这
        ("userprofile", os.path.join(up, "OneDrive", "Documents")),
        ("savedgames", os.path.join(up, "Saved Games")),
        ("mydocuments", known_folder(0x05) or ""),
        ("desktop", known_folder(0x10) or ""),
    ]
    ident = identity(prog, install_dir)
    pub_ident = {"raw": set(), "strong": ident["pub"], "core": set(), "words": ident["pub_words"]}
    app_low = norm(prog.get("name", ""))
    pub_lead = any(len(w) >= 4 and app_low.startswith(w) for w in ident["pub"])
    idir = os.path.abspath(install_dir) if install_dir else ""
    # 内容指纹：软件自己写的配置里通常留着安装路径 / 主程序名，名字对不上时靠它认
    needles = []
    if idir:
        needles.append(idir.lower().rstrip("\\") + "\\")
        for st in _exe_stems(idir, depth=1, limit=6):
            if len(st) >= 4:
                needles.append(os.path.splitext(st)[0].lower() + ".exe")
    pending = []   # 名字对不上、待看内容的候选目录
    hits = []
    seen = set()
    SKIP_ANY = PROFILE_SKIP | DRIVE_ROOT_SKIP | {
        "my pictures", "my music", "my videos", "pictures", "music", "videos", "downloads",
        "node_modules", ".git", "venv", ".venv", "__pycache__", "site-packages",
        "packages", "windowsapps", "temp", "tmp", "crashdumps", "dumps", "wer",
        "livekernelreports", "d3dscache", "dxcache", "libraries",
    }

    BASES = {
        "roaming": rd,
        "local": ldr,
        "locallow": os.path.join(up, "AppData", "LocalLow"),
        "programdata": pd,
        "documents": docs,
        "publicdocuments": os.path.join(pub, "Documents"),
        "public": pub,
        "userprofile": up,
        "savedgames": os.path.join(up, "Saved Games"),
        "mydocuments": docs,
        "desktop": known_folder(0x10) or "",
        "manual": "",
    }

    def add(kind, p, name):
        try:
            key = os.path.abspath(p).lower()
        except Exception:
            return
        if key in seen:
            return
        if any(key.startswith(s + "\\") for s in seen):
            return          # 已经在某个已收录的目录里面，别重复打包
        if is_temp_path(p):
            return
        if os.path.isdir(p):
            seen.add(key)
            hits.append({"kind": kind, "path": os.path.abspath(p), "name": name,
                         "rel": _rel_to_base(kind, p, BASES)})
        elif os.path.isfile(p) and os.path.getsize(p) < 64 * 1024 * 1024:
            seen.add(key)
            hits.append({"kind": kind, "path": os.path.abspath(p), "name": name,
                         "rel": _rel_to_base(kind, p, BASES), "is_file": True})

    def prefix_strong(name, minlen=4):
        n = norm(name)
        return any(len(c) >= minlen and n.startswith(c) for c in ident["strong"])

    for kind, root in roots:
        if not root or not os.path.isdir(root):
            continue
        try:
            entries = os.listdir(lp(root))
        except Exception:
            continue
        for e in entries:
            p = os.path.join(root, e)
            if os.path.islink(p) or is_reparse(p):
                continue
            low = e.lower()
            if low in SKIP_ANY or low.startswith("$"):
                continue
            if not os.path.isdir(p):
                # 用户主目录下的单文件配置（.gitconfig / .npmrc / .condarc 之类）
                if kind in ("userprofile", "desktop") and os.path.isfile(p) and low not in PROFILE_SKIP \
                        and not low.endswith((".exe", ".dll", ".lnk", ".msi", ".sys", ".dat")):
                    # 用户主目录里单文件很多，这里只认几乎同名的（.gitconfig / .npmrc 这类）
                    if _name_score(e.lstrip("."), ident) >= 0.95:
                        add(kind, p, e)
                continue
            sc = _name_score(e, ident)
            if sc >= SCORE_ROOT:
                add(kind, p, e)
                continue
            if sc >= 0.30:
                pending.append((kind, p, e))
            # 发布商目录本身（软件名以发布商开头：NVIDIA App → NVIDIA 目录）
            pub_dir = bool(ident["pub"]) and _name_score(e, pub_ident) >= 0.86
            if pub_lead and pub_dir:
                add(kind, p, e)
            # 共享容器里再找一层：Tencent\QQ、aha_doctor\Doubao、NetEase\CloudMusic、Adobe\Acrobat
            if kind in ("local", "locallow", "roaming", "programdata", "documents",
                        "userprofile", "publicdocuments", "mydocuments"):
                for sub in _list_subdirs(p)[:80]:
                    bn = os.path.basename(sub)
                    if bn.lower() in SKIP_ANY:
                        continue
                    if _name_score(bn, ident) >= SCORE_CONTAINER:
                        add(kind, sub, bn)
                    elif pub_dir or _name_score(bn, ident) >= 0.30:
                        # 发布商容器里的子目录名字常常完全对不上（Tencent\xwechat），
                        # 留给内容指纹那一步判断，别在这里瞎猜
                        pending.append((kind, sub, bn))
    # 微软商店 / 沙盒应用的目录：Packages\<包名>\LocalCache\Roaming\<软件名>
    pkg_root = os.path.join(ldr, "Packages")
    if os.path.isdir(pkg_root) and ident["strong"]:
        for pkg in _list_subdirs(pkg_root):
            for leaf in ("LocalCache\\Roaming", "LocalCache\\Local", "LocalCache\\LocalLow",
                         "Roaming", "Local", "LocalCache"):
                base = os.path.join(pkg, leaf)
                if not os.path.isdir(base):
                    continue
                for sub in _list_subdirs(base)[:80]:
                    bn = os.path.basename(sub)
                    if bn.lower() in SKIP_ANY:
                        continue
                    if _name_score(bn, ident) >= SCORE_ROOT:
                        add("local", sub, bn)
    # 安装目录旁边的同名/同系列文件夹（C:\Doubao 与 C:\DoubaoData）
    idir = os.path.abspath(install_dir) if install_dir else ""
    if idir:
        parent = os.path.dirname(idir.rstrip("\\"))
        pbn = norm(os.path.basename(parent))
        # 允许盘符根目录；Program Files 这类公用容器不扫，避免把隔壁软件当自己的数据
        if parent and os.path.isdir(parent) and len(parent.rstrip("\\")) >= 2 \
                and pbn not in GENERIC_DIR_NAMES and not pbn.startswith("program files") \
                and "\\program files" not in parent.lower():
            for d in _list_subdirs(parent):
                b = os.path.basename(d.rstrip("\\"))
                if os.path.abspath(d).lower() == idir.lower() or b.lower() in SKIP_ANY:
                    continue
                if prefix_strong(b, 5) or _name_score(b, ident) >= 0.88:
                    add("sibling", d, b)
    # 其它磁盘根目录里的软件文件夹（数据盘自选目录：D:\CloudMusic、C:\java、D:\DoubaoData）
    DATA_SUFFIX = {"data", "userdata", "userdatas", "files", "file", "cache", "config", "configs",
                   "backup", "profile", "profiles", "settings", "storage", "save", "saves", "db"}
    if ident["strong"]:
        for drv in string.ascii_uppercase:
            root = drv + ":\\"
            if not os.path.isdir(root):
                continue
            try:
                entries = os.listdir(lp(root))
            except Exception:
                continue
            for e in entries:
                if e.lower() in DRIVE_ROOT_SKIP:
                    continue
                p = os.path.join(root, e)
                if not os.path.isdir(p) or is_reparse(p):
                    continue
                if idir and os.path.abspath(p).lower() == idir.lower():
                    continue
                if _name_score(e, ident) >= SCORE_DRIVE:
                    add("drive", p, e)
                    continue
                ne = norm(e)
                for c in ident["strong"]:
                    if len(c) >= 5 and ne.startswith(c) and ne[len(c):] in DATA_SUFFIX:
                        add("drive", p, e)
                        break
    # 内容指纹兜底：名字完全不像的目录，看它自己的配置里有没有写本软件的安装路径/主程序名
    if needles and pending:
        t_end = time.time() + 12.0
        tried = 0
        for kind, p, nm in pending[:80]:
            if time.time() > t_end or tried > 60:
                break
            try:
                key = os.path.abspath(p).lower()
            except Exception:
                continue
            if key in seen or is_temp_path(p):
                continue
            tried += 1
            if _dir_mentions(p, needles):
                add(kind, p, nm)
    # 去掉互相嵌套的重复项（同一份数据不该被打包两次），只留最外层
    out = []
    keys = set()
    for h in sorted(hits, key=lambda d: (bool(d.get("is_file")), d["path"].count("\\"))):
        k = os.path.abspath(h["path"]).lower()
        if any(k.startswith(x + "\\") for x in keys):
            continue
        keys.add(k)
        out.append(h)
    return out


def _quick_size(path, limit=1200):
    """快速估体积：数到 limit 个文件就停，扫描漏目录时不至于卡住。返回 (字节, 文件数)"""
    total, n = 0, 0
    try:
        for root, dirs, files in os.walk(lp(path)):
            for f in files:
                total += _file_size(os.path.join(root, f))
                n += 1
                if n >= limit:
                    return total, n
    except Exception:
        pass
    return total, n


def suggest_missing_dirs(prog, install_dir, known, limit=15, min_bytes=262144):
    """识别完之后再扫一遍，把「名字接近但没被收进来」的目录列出来给用户勾。
    这是给全世界所有不认识的软件兜底：名字对不上时，用户点一下就能把它补进包。"""
    ident = identity(prog, install_dir)
    idir = os.path.abspath(install_dir).lower().rstrip("\\") if install_dir else ""
    known_low = set()
    for p in (known or []):
        try:
            known_low.add(os.path.abspath(p).lower().rstrip("\\"))
        except Exception:
            pass
    ldr = os.environ.get("LOCALAPPDATA", "")
    rd = os.environ.get("APPDATA", "")
    up = os.environ.get("USERPROFILE", "")
    pd = os.environ.get("PROGRAMDATA", "")
    docs = os.path.join(known_folder(0x05) or up, "Documents")
    roots = [("roaming", rd), ("local", ldr), ("local", os.path.join(ldr, "Programs")),
             ("locallow", os.path.join(up, "AppData", "LocalLow")), ("programdata", pd),
             ("documents", docs), ("userprofile", up),
             ("userprofile", os.path.join(up, ".config")),
             ("userprofile", os.path.join(up, ".local", "share")),
             ("public", os.environ.get("PUBLIC", "")),
             ("publicdocuments", os.path.join(os.environ.get("PUBLIC", ""), "Documents"))]
    found = []
    seen = set()
    SKIP_ANY = PROFILE_SKIP | DRIVE_ROOT_SKIP | {"packages", "windowsapps", "temp", "tmp"}
    for kind, root in roots:
        if not root or not os.path.isdir(root):
            continue
        try:
            entries = os.listdir(lp(root))
        except Exception:
            continue
        for e in entries:
            p = os.path.join(root, e)
            if not os.path.isdir(p) or is_reparse(p):
                continue
            low = os.path.abspath(p).lower().rstrip("\\")
            if low in seen or low in known_low or is_temp_path(p):
                continue
            if e.lower() in SKIP_ANY:
                continue
            if idir and (low == idir or low.startswith(idir + "\\") or idir.startswith(low + "\\")):
                continue
            sc = _name_score(e, ident)
            if sc < SCORE_ROOT and ident["pub_words"]:
                # 发布商名目录也可能是它的数据（Adobe / Tencent / PurrSoft），但只当候选
                sc = max(sc, _name_score(e, ident, words=ident["pub_words"]))
            if sc <= 0:
                # 名字不像，但目录里就有这个软件的 exe：也算候选（另一份安装副本 / 数据目录）
                try:
                    for f in os.listdir(lp(p)):
                        st = norm(os.path.splitext(f)[0])
                        if f.lower().endswith(".exe") and st in ident["exes"] and st not in GENERIC_EXE:
                            sc = 0.60
                            break
                except Exception:
                    pass
            if sc < 0.55:
                continue
            size, cnt = _quick_size(p)
            if size < min_bytes:
                continue
            seen.add(low)
            found.append({"kind": kind, "path": os.path.abspath(p), "name": e,
                          "score": sc, "size": size, "count": cnt})
    found.sort(key=lambda d: (-d["score"], -d["size"]))
    return found[:limit]


def find_reg_keys(prog, cands, limit=8, own_cands=None):
    """找这个软件自己的注册表项。own_cands = 只有它自己的名字；
    只靠发布商名命中的（Adobe / Tencent）不整包带走，只往下钻一层找自己的子项。"""
    hits = []
    seen = set()
    own = own_cands or cands

    def scan(root_path, hive_name, depth):
        if len(hits) >= limit:
            return
        try:
            k = winreg.OpenKey(HIVES[hive_name], root_path, 0, winreg.KEY_READ | winreg.KEY_WOW64_64KEY)
            n = winreg.QueryInfoKey(k)[0]
        except OSError:
            return
        children = []
        for i in range(min(n, 4000)):
            try:
                children.append(winreg.EnumKey(k, i))
            except OSError:
                break
        winreg.CloseKey(k)
        for c in children:
            if not _match(c, cands):
                continue
            p = root_path + "\\" + c
            if _match(c, own) and p.lower() not in seen:
                seen.add(p.lower())
                hits.append({"hive": hive_name, "path": p})
                if len(hits) >= limit:
                    return
            if depth > 0:
                scan(p, hive_name, depth - 1)

    for hive_name in ("HKLM", "HKCU"):
        for base in ([r"SOFTWARE", r"SOFTWARE\WOW6432Node"] if hive_name == "HKLM" else [r"Software"]):
            scan(base, hive_name, 1)
    return hits[:limit]


def find_services(install_dir):
    out = []
    if not install_dir:
        return out
    needle = install_dir.rstrip("\\").lower()
    try:
        k = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SYSTEM\CurrentControlSet\Services", 0, winreg.KEY_READ)
        n = winreg.QueryInfoKey(k)[0]
    except OSError:
        return out
    for i in range(min(n, 3000)):
        try:
            sub = winreg.EnumKey(k, i)
            sk = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                                r"SYSTEM\CurrentControlSet\Services\%s" % sub, 0, winreg.KEY_READ)
            img = str(_q(sk, "ImagePath", ""))
            disp = str(_q(sk, "DisplayName", ""))
            winreg.CloseKey(sk)
        except OSError:
            continue
        if needle and needle in img.lower():
            out.append({"name": sub, "display_name": disp, "image_path": img})
    winreg.CloseKey(k)
    return out


def running_exes(exe_names):
    hit = []
    for name in (exe_names or [])[:8]:
        try:
            r = subprocess.run(["tasklist", "/FI", "IMAGENAME eq %s" % name, "/NH"],
                               capture_output=True, timeout=12, creationflags=0x08000000)
            if name.lower() in (r.stdout or b"").decode("mbcs", "ignore").lower():
                hit.append(name)
        except Exception:
            continue
    return hit


KILL_GUARD_NAMES = {"svchost", "csrss", "wininit", "services", "lsass", "smss", "winlogon",
                    "explorer", "taskhostw", "sihost", "runtimebroker", "shellexperiencehost",
                    "startmenuexperiencehost", "applicationframehost", "backgroundtaskhost",
                    "dllhost", "cmd", "conhost", "powershell", "pwsh", "wmiprvse",
                    "securityhealthsystray", "textinputhost", "ctfmon", "searchprotocolhost",
                    "searchindexer", "registry", "dwm", "spoolsv", "audiodg"}


def _kill_allowed_dir(d):
    """系统目录里的进程不能自动结束（会连带把桌面/服务干掉）"""
    if not d:
        return False
    low = os.path.abspath(lp(d)).lower()
    return not ("\\windows\\" in low + "\\" or low.rstrip("\\").endswith("\\windows"))


def list_app_processes(install_dir):
    """列出 exe 位于该安装目录下的运行中进程：[{pid, name, path}]"""
    if not install_dir or not os.path.isdir(install_dir) or not _kill_allowed_dir(install_dir):
        return []
    tmp = tempfile.mkdtemp(prefix="sm_proc_")
    script = os.path.join(tmp, "p.ps1")
    outp = os.path.join(tmp, "out.json")
    try:
        with open(script, "w", encoding="utf-8-sig") as f:
            f.write(r'''
$ErrorActionPreference = "SilentlyContinue"
$d = ($args[0]).TrimEnd('\')
$list = @()
Get-Process | ForEach-Object {
  $p = $_.Path
  if ($p -and $p.ToLower().StartsWith($d.ToLower() + '\')) {
    $list += @{ pid = $_.Id; name = $_.ProcessName; path = $p }
  }
}
ConvertTo-Json -InputObject $list -Depth 3 -Compress | Set-Content -LiteralPath $args[1] -Encoding UTF8
''')
        subprocess.run([_powershell_exe(), "-NoProfile", "-NonInteractive", "-ExecutionPolicy",
                        "Bypass", "-File", script, os.path.abspath(install_dir), outp],
                       capture_output=True, creationflags=0x08000000, timeout=60)
        if not os.path.isfile(outp):
            return []
        with open(outp, "r", encoding="utf-8-sig") as f:
            txt = f.read().strip()
        if not txt:
            return []
        data = json.loads(txt)
        if isinstance(data, dict):
            data = [data]
        out = []
        for d in data:
            if not d.get("pid"):
                continue
            if (d.get("name") or "").lower() in KILL_GUARD_NAMES:
                continue
            out.append(d)
        return out
    except Exception:
        return []
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def kill_app_processes(procs):
    """结束这些进程（含子进程），返回成功结束的名字列表"""
    killed = []
    pids = [str(p.get("pid")) for p in (procs or []) if p.get("pid")]
    names = {}
    for p in procs or []:
        names[str(p.get("pid"))] = p.get("name") or str(p.get("pid"))
    if not pids:
        return killed
    # 一次 taskkill 批量结束，比逐个起进程快得多
    for i in range(0, len(pids), 20):
        chunk = pids[i:i + 20]
        cmd = ["taskkill"]
        for pid in chunk:
            cmd += ["/PID", pid]
        cmd += ["/T", "/F"]
        try:
            subprocess.run(cmd, capture_output=True, creationflags=0x08000000, timeout=30)
            for pid in chunk:
                killed.append(names.get(pid, pid))
        except Exception:
            continue
    return killed


def list_app_processes_multi(install_dirs):
    """一次扫全机进程，按安装目录前缀归组：[{pid, name, path}]
    （比每个软件各调一次 PowerShell 快很多，也不会把界面卡住）"""
    dirs = []
    for d in install_dirs or []:
        if not d or not _kill_allowed_dir(d):
            continue
        low = os.path.abspath(lp(d)).rstrip("\\").lower()
        if low and low not in dirs:
            dirs.append(low)
    if not dirs:
        return []
    tmp = tempfile.mkdtemp(prefix="sm_proc2_")
    script = os.path.join(tmp, "p.ps1")
    outp = os.path.join(tmp, "out.json")
    try:
        with open(script, "w", encoding="utf-8-sig") as f:
            f.write(r'''
$ErrorActionPreference = "SilentlyContinue"
$list = @()
foreach ($p in (Get-CimInstance Win32_Process -Property ProcessId,Name,ExecutablePath)) {
  $list += @{ pid = $p.ProcessId; name = $p.Name; path = $p.ExecutablePath }
}
ConvertTo-Json -InputObject $list -Depth 3 -Compress | Set-Content -LiteralPath $args[0] -Encoding UTF8
''')
        subprocess.run([_powershell_exe(), "-NoProfile", "-NonInteractive", "-ExecutionPolicy",
                        "Bypass", "-File", script, outp],
                       capture_output=True, creationflags=0x08000000, timeout=90)
        if not os.path.isfile(outp):
            return []
        with open(outp, "r", encoding="utf-8-sig") as f:
            txt = f.read().strip()
        if not txt:
            return []
        data = json.loads(txt)
        if isinstance(data, dict):
            data = [data]
        out, seen = [], set()
        for d in data:
            pid = d.get("pid")
            p = (d.get("path") or "").rstrip("\\").lower()
            if not pid or not p or pid in seen:
                continue
            nm = (d.get("name") or "")
            base = os.path.splitext(nm)[0].lower()
            if base in KILL_GUARD_NAMES:
                continue
            for pre in dirs:
                if p == pre or p.startswith(pre + "\\"):
                    seen.add(pid)
                    out.append({"pid": pid, "name": base,
                                "path": d.get("path")})
                    break
        return out
    except Exception:
        return []
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def installed_runtimes():
    out = []
    for p in list_programs(include_system=True):
        if re.search(r"Visual C\+\+|\.NET .*Runtime|Windows Desktop Runtime|DirectX", p["name"], re.IGNORECASE):
            out.append(p["name"])
    return sorted(set(out))


# ---------------- 快捷方式 ----------------

PS_SCRIPT = r'''
$ErrorActionPreference = "Stop"
$cfg = Get-Content -LiteralPath $args[0] -Encoding UTF8 -Raw | ConvertFrom-Json
$W = New-Object -ComObject WScript.Shell
$out = @()
if ($cfg.mode -eq "create") {
  foreach ($i in $cfg.items) {
    $dir = [System.IO.Path]::GetDirectoryName($i.lnk)
    if (-not (Test-Path -LiteralPath $dir)) { New-Item -ItemType Directory -Path $dir -Force | Out-Null }
    $s = $W.CreateShortcut($i.lnk)
    $s.TargetPath = $i.target
    if ($i.args) { $s.Arguments = $i.args } else { $s.Arguments = "" }
    if ($i.workdir) { $s.WorkingDirectory = $i.workdir }
    if ($i.icon) { $s.IconLocation = $i.icon }
    if ($i.desc) { $s.Description = $i.desc }
    $s.Save()
    $out += @{ lnk = $i.lnk; ok = $true }
  }
} else {
  foreach ($p in $cfg.items) {
    if (Test-Path -LiteralPath $p) {
      $s = $W.CreateShortcut($p)
      $out += @{ lnk = $p; target = $s.TargetPath; args = $s.Arguments; workdir = $s.WorkingDirectory; icon = $s.IconLocation; desc = $s.Description }
    }
  }
}
$out | ConvertTo-Json -Depth 4 -Compress | Set-Content -LiteralPath $args[1] -Encoding UTF8
'''


def _powershell_exe():
    p = os.path.join(os.environ.get("SystemRoot", r"C:\Windows"),
                     r"System32\WindowsPowerShell\v1.0\powershell.exe")
    if os.path.isfile(p):
        return p
    return "powershell"


def ps_run(cfg_obj):
    tmp = tempfile.mkdtemp(prefix="sm_ps_")
    cin = os.path.join(tmp, "in.json")
    cout = os.path.join(tmp, "out.json")
    script = os.path.join(tmp, "run.ps1")
    try:
        with open(cin, "w", encoding="utf-8") as f:
            json.dump(cfg_obj, f, ensure_ascii=False)
        with open(script, "w", encoding="utf-8-sig") as f:
            f.write(PS_SCRIPT)
        subprocess.run([_powershell_exe(), "-NoProfile", "-ExecutionPolicy", "Bypass",
                        "-File", script, cin, cout],
                       capture_output=True, creationflags=0x08000000, timeout=120)
        if not os.path.isfile(cout):
            return None
        with open(cout, "r", encoding="utf-8-sig") as f:
            txt = f.read().strip()
        if not txt:
            return []
        data = json.loads(txt)
        return [data] if isinstance(data, dict) else data
    except Exception:
        return None
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def collect_shortcuts(install_dir, display_name):
    if not install_dir:
        return []
    found = []
    dirs = [("user", "desktop", known_folder(0x10)), ("user", "programs", known_folder(0x02)),
            ("all", "desktop", known_folder(0x19)), ("all", "programs", known_folder(0x17))]
    needle = install_dir.rstrip("\\").lower()
    for scope, kind, root in dirs:
        if not root or not os.path.isdir(root):
            continue
        for dirpath, dirnames, filenames in os.walk(root):
            for fn in filenames:
                if not fn.lower().endswith(".lnk"):
                    continue
                p = os.path.join(dirpath, fn)
                try:
                    if os.path.getsize(p) > 60000:
                        continue
                    with open(lp(p), "rb") as f:
                        blob = f.read()
                except Exception:
                    continue
                hit = False
                try:
                    if needle.encode("utf-16le") in blob.lower():
                        hit = True
                except Exception:
                    pass
                if not hit:
                    try:
                        if needle.encode("mbcs", "ignore") in blob.lower():
                            hit = True
                    except Exception:
                        pass
                if hit:
                    found.append({"path": p, "scope": scope, "kind": kind, "rel": os.path.relpath(p, root)})
    if found:
        info = {}
        for x in (ps_run({"mode": "info", "items": [s["path"] for s in found]}) or []):
            info[x.get("lnk")] = x
        for s in found:
            m = info.get(s["path"]) or {}
            for k in ("target", "args", "workdir", "icon", "desc"):
                s[k] = m.get(k, "")
    return found


# ---------------- 分析 ----------------

JUNK_SKIP = {"$recycle.bin", "system volume information"}


def _looks_like_program_copy(path, install_dir, entry_exes):
    """判断某个目录是不是「同一套程序的另一份拷贝」（例如上次还原留下的目录），这种不该当数据目录再打一份。"""
    if not entry_exes or not path or not install_dir:
        return False
    for e in list(entry_exes)[:3]:
        a = os.path.join(install_dir, e)
        b = os.path.join(path, e)
        try:
            if os.path.isfile(a) and os.path.isfile(b) and os.path.getsize(a) == os.path.getsize(b):
                return True
        except Exception:
            continue
    return False


def dirs_in_registry(reg_keys, install_dir, known, cands=None, depth=2):
    """从注册表字符串值里挖出该软件自己记录的路径（最可靠的「它还用了哪些目录」线索）。"""
    out = []
    cands = cands or set()
    temp_dirs = [os.path.abspath(os.environ.get(k, "")) for k in ("TEMP", "TMP") if os.environ.get(k)]
    pf_dirs = [os.environ.get(k, "").lower().rstrip("\\") for k in ("ProgramFiles", "ProgramFiles(x86)")]
    path_re = re.compile(r"([A-Za-z]:\\[^\"'<>|\r\n\t,;]*)")
    for rk in reg_keys or []:
        hive = HIVES.get(rk.get("hive", ""))
        if hive is None or not rk.get("path"):
            continue
        found = []

        def rec(p, d):
            try:
                k = winreg.OpenKey(hive, p, 0, winreg.KEY_READ)
            except OSError:
                return
            try:
                for i in range(winreg.QueryInfoKey(k)[1]):
                    try:
                        _n, data, typ = winreg.EnumValue(k, i)
                    except OSError:
                        continue
                    if typ not in (winreg.REG_SZ, winreg.REG_EXPAND_SZ, winreg.REG_MULTI_SZ):
                        continue
                    txt = data if isinstance(data, str) else " ".join([str(x) for x in (data or [])])
                    for m in path_re.findall(txt or ""):
                        found.append(m)
                if d < depth:
                    for i in range(min(winreg.QueryInfoKey(k)[0], 200)):
                        try:
                            sub = winreg.EnumKey(k, i)
                        except OSError:
                            break
                        rec(p + "\\" + sub, d + 1)
            finally:
                winreg.CloseKey(k)

        try:
            rec(rk["path"], 0)
        except Exception:
            continue
        for raw in found:
            p = raw.strip().strip('"').rstrip("\\")
            if len(p) <= 3 or not os.path.isdir(p):
                continue
            low = p.lower()
            if low in known:
                continue
            if any(t and low.startswith(t.lower()) for t in temp_dirs):
                continue
            if "\\temp\\" in low or "\\tmp\\" in low:
                continue
            # Program Files 下的路径基本是另一处程序本体，已经由安装目录覆盖，不再重复打包
            if any(pf and (low == pf or low.startswith(pf + "\\")) for pf in pf_dirs):
                continue
            if install_dir and low.startswith(os.path.abspath(install_dir).lower()):
                continue
            if "\\windows" in low or "\\program files\\common files" in low:
                continue
            base = os.path.basename(p)
            if cands and not _match(base, cands):
                continue
            known.add(low)
            out.append(p)
    return out


def _looks_like_component(prog):
    """驱动/运行库/系统组件/安装包缓存：这类东西本来就不该「搬」，新电脑重装即可"""
    name = (prog.get("name") or "").lower()
    icon = (prog.get("display_icon") or "").lower()
    unins = (prog.get("uninstall_string") or "").lower()
    if "package cache" in icon or "package cache" in unins:
        return True
    for kw in ("driver", "chipset", "runtime", "redistributable", "visual c++", "directx",
               ".net ", "update for", "hotfix", "webview", "xna", "physx", "vcredist"):
        if kw in name:
            return True
    return False


def analyze(prog, log=None, skip_cache=False, do_reg_scan=True):
    def L(m):
        if log:
            log(m)

    info = {"program": prog, "install_dir": "", "data_dirs": [], "reg_keys": [], "shortcuts": [],
            "services": [], "warnings": [], "entry_exes": [], "size": 0, "file_count": 0,
            "data_size": 0, "data_count": 0, "install_desc": ""}
    idir = resolve_install_dir(prog)
    # 安装目录指向 app / bin 子目录时，若上一层就是软件自己的同名目录（如 C:\Doubao\app），
    # 上提一层，避免 exe/ini/uninstall 留在包外，也避免把父目录当"数据目录"重复打一遍
    if idir:
        par = os.path.dirname(idir.rstrip("\\"))
        pbn = norm(os.path.basename(par))
        if par and len(par.rstrip("\\")) > 3 and pbn and pbn not in GENERIC_DIR_NAMES:
            ident = identity(prog, idir)
            self_names = set(ident["strong"]) | _search_tokens(prog)
            self_names.add(norm(prog.get("name", "")))
            self_names.add(norm(os.path.basename(idir.rstrip("\\"))))
            hit = any(pbn == s or (len(s) >= 4 and s in pbn) for s in self_names if s)
            if hit and os.path.isdir(par):
                idir = par
    if not idir:
        if _looks_like_component(prog):
            info["component"] = True
            info["warnings"].append("这是驱动 / 运行库 / 系统组件（源电脑的安装包缓存或 MSI 组件），"
                                    "不属于可迁移的应用程序：新电脑直接装对应的驱动或运行库就行，"
                                    "不建议打包；如确认它有独立安装目录，可用『手动选 exe/文件夹』指定。")
        else:
            info["warnings"].append("没找到安装目录，请点『手动选 exe/文件夹』指定。"
                                    "（软件可能装在移动硬盘、网络盘，或目录被改过名）")
        return info
    if len(idir.rstrip("\\")) <= 3:
        info["warnings"].append("安装目录指向磁盘根目录，已忽略，请手动指定具体文件夹。")
        return info
    info["install_dir"] = idir
    L("安装目录：%s" % idir)

    try:
        exes = []
        for f in os.listdir(lp(idir)):
            fp = os.path.join(idir, f)
            if os.path.isfile(fp) and f.lower().endswith(".exe"):
                exes.append((os.path.getsize(fp), f))
        exes.sort(reverse=True)
        bad_words = ("uninst", "setup", "install", "update", "upgrader", "helper",
                     "crash", "reporter", "debug")
        pname = norm(prog.get("name", ""))
        exes.sort(key=lambda t: (any(w in t[1].lower() for w in bad_words),
                                 0 if norm(os.path.splitext(t[1])[0]) == pname else 1,
                                 -t[0]))
        info["entry_exes"] = [f for _, f in exes[:6]]
    except Exception:
        pass

    if do_reg_scan:
        cands = _candidate_names(prog, idir)
        ident = identity(prog, idir)
        own = set(ident["strong"]) | set(ident["exes"]) | {w for w in ident["words"] if len(w) >= 4}
        keys = []
        if prog.get("hive") and prog.get("reg_path"):
            keys.append({"hive": prog["hive"], "path": prog["reg_path"], "role": "uninstall"})
        for k in find_reg_keys(prog, cands, own_cands=own):
            k["role"] = "app"
            keys.append(k)
        seen = set()
        uniq = []
        for k in keys:
            key = (k["hive"] + "|" + k["path"]).lower()
            if key in seen:
                continue
            seen.add(key)
            uniq.append(k)
        info["reg_keys"] = uniq

    info["install_desc"] = "程序本体（exe / dll / 资源文件）—— 软件能不能打开全靠它，必须整份带走"

    info["data_dirs"] = find_data_dirs(prog, idir)
    known = {os.path.abspath(idir).lower()} | {os.path.abspath(d["path"]).lower() for d in info["data_dirs"]}
    if info["reg_keys"]:
        try:
            for p in dirs_in_registry(info["reg_keys"], idir, known,
                                      _candidate_names(prog, idir)):
                if _looks_like_program_copy(p, idir, info["entry_exes"]):
                    L("忽略（只是另一份程序副本，不是数据）：%s" % p)
                    continue
                # 注册表里的路径也要对得上「这个软件自己」的名字，
                # 不能因为同厂（Adobe / Tencent）就把兄弟软件的目录一起带进来
                if _name_score(os.path.basename(p.rstrip("\\")), identity(prog, idir)) < 0.86:
                    L("跳过（只是同厂另一个软件的目录）：%s" % p)
                    continue
                info["data_dirs"].append({"kind": "registry", "path": p,
                                          "name": os.path.basename(p.rstrip("\\")),
                                          "rel": os.path.basename(p.rstrip("\\"))})
        except Exception:
            pass
    if info["reg_keys"]:
        # 软件自己写在注册表里的路径（火绒的 DataPath、各种 CacheDir），跟名字像不像无关
        try:
            up = os.environ.get("USERPROFILE", "")
            bases = [("roaming", os.environ.get("APPDATA", "")),
                     ("local", os.environ.get("LOCALAPPDATA", "")),
                     ("locallow", os.path.join(up, "AppData", "LocalLow")),
                     ("programdata", os.environ.get("PROGRAMDATA", "")),
                     ("documents", os.path.join(known_folder(0x05) or up, "Documents")),
                     ("userprofile", up)]
            bases = sorted([b for b in bases if b[1]], key=lambda b: -len(b[1]))
            for p in reg_path_hints(info["reg_keys"], idir, known):
                if _looks_like_program_copy(p, idir, info["entry_exes"]):
                    L("忽略注册表路径（只是程序副本）：%s" % p)
                    continue
                for kk, base in bases:
                    low, bl = os.path.abspath(p).lower(), os.path.abspath(base).lower()
                    if low == bl or not low.startswith(bl + "\\"):
                        continue
                    rel = os.path.relpath(p, base)
                    if rel.startswith(".."):
                        break
                    if low in known:
                        break
                    known.add(low)
                    info["data_dirs"].append({"kind": "registry", "path": p,
                                              "name": os.path.basename(p.rstrip("\\")),
                                              "rel": rel})
                    L("注册表里写着的数据目录：%s" % p)
                    break
        except Exception:
            pass
    kept = []
    for d in info["data_dirs"]:
        if is_temp_path(d["path"]):
            L("跳过临时目录：%s" % d["path"])
            continue
        if d.get("is_file"):
            try:
                d["size"] = os.path.getsize(lp(d["path"]))
            except Exception:
                d["size"] = 0
            d["count"] = 1
            d["cache"] = False
            d["desc"] = "单文件配置 —— 账号、身份、工具设置（如 .gitconfig），必须带走"
            info["data_size"] += d["size"]
            info["data_count"] += 1
            kept.append(d)
            L("相关文件：%s（%s）" % (d["path"], human_size(d["size"])))
            continue
        s, c = dir_size(d["path"], skip_cache=skip_cache)
        dp = os.path.abspath(d["path"]).lower()
        ip = os.path.abspath(idir).lower()
        if dp == ip or dp.startswith(ip + "\\"):
            L("跳过（已在程序本体里，不重复打包）：%s" % d["path"])
            continue
        if ip.startswith(dp + "\\"):
            L("跳过（只是程序本体的上层目录，不重复打包）：%s" % d["path"])
            continue
        d["size"] = s
        d["count"] = c
        if c == 0:
            # 空的也要带走：软件首次运行 / 换机后才会往里写东西，路径得先存在
            d["cache"] = False
            d["desc"] = "空目录（现在还没内容，但属于这个软件；一起打包，新电脑上路径先建好）"
            kept.append(d)
            L("空目录（也打包）：%s" % d["path"])
            continue
        prof = dir_profile(d["path"])
        d["desc"], d["cache"] = describe_dir(d["path"], d.get("kind", ""), d.get("name", ""), prof)
        info["data_size"] += s
        info["data_count"] += c
        kept.append(d)
        L("相关目录：%s（%s）—— %s" % (d["path"], human_size(s), d["desc"]))
    # 同一份数据同时出现「父目录」和「子目录」时只留最外层，避免打包两次
    dedup = []
    dkeys = set()
    for d in sorted(kept, key=lambda x: (bool(x.get("is_file")), os.path.abspath(x["path"]).count("\\"))):
        k = os.path.abspath(d["path"]).lower()
        if any(k.startswith(x + "\\") for x in dkeys):
            L("跳过重复（已在更外层的数据目录里）：%s" % d["path"])
            continue
        dkeys.add(k)
        dedup.append(d)
    kept = dedup
    info["data_size"] = sum(int(d.get("size") or 0) for d in kept)
    info["data_count"] = sum(int(d.get("count") or 0) for d in kept)
    info["data_dirs"] = kept

    info["shortcuts"] = collect_shortcuts(idir, prog.get("name", ""))
    info["services"] = find_services(idir)
    for s in info["services"]:
        info["warnings"].append("检测到系统服务：%s —— 新电脑上需以管理员身份重建。" % (s["display_name"] or s["name"]))

    size, count = dir_size(idir, skip_cache=skip_cache)
    info["size"] = size
    info["file_count"] = count
    L("程序文件：%d 个，共 %s" % (count, human_size(size)))

    run = running_exes(info["entry_exes"])
    if run:
        info["warnings"].insert(0, "软件正在运行（%s），建议先退出，否则被占用的文件会跳过。" % "、".join(run))
    return info


# ---------------- 注册表导出/导入 ----------------


def _reg_value_encode(typ, data):
    if typ in (winreg.REG_SZ, winreg.REG_EXPAND_SZ):
        return str(data)
    if typ == winreg.REG_MULTI_SZ:
        return [str(x) for x in list(data)]
    if typ in (winreg.REG_DWORD, winreg.REG_QWORD):
        try:
            return int(data)
        except Exception:
            return 0
    if isinstance(data, (bytes, bytearray)):
        return {"b64": base64.b64encode(bytes(data)).decode("ascii")}
    return str(data)


def export_key_tree(hive_name, path, max_depth=6):
    hive = HIVES[hive_name]
    wow = winreg.KEY_WOW64_64KEY if hive_name == "HKLM" else 0

    def rec(p, depth):
        node = {"name": p.split("\\")[-1], "values": [], "keys": []}
        try:
            k = winreg.OpenKey(hive, p, 0, winreg.KEY_READ | wow)
        except OSError as e:
            node["error"] = str(e)
            return node
        try:
            for i in range(winreg.QueryInfoKey(k)[1]):
                try:
                    name, data, typ = winreg.EnumValue(k, i)
                except OSError:
                    continue
                node["values"].append({"name": name, "type": typ, "data": _reg_value_encode(typ, data)})
            if depth < max_depth:
                for i in range(min(winreg.QueryInfoKey(k)[0], 2000)):
                    try:
                        sub = winreg.EnumKey(k, i)
                    except OSError:
                        break
                    node["keys"].append(rec(p + "\\" + sub, depth + 1))
        finally:
            winreg.CloseKey(k)
        return node

    return rec(path, 0)


def _repl_str(s, pairs):
    if not s or not isinstance(s, str):
        return s
    for old, new in pairs:
        if old and new and old.lower() != new.lower() and old.lower() in s.lower():
            s = re.sub(re.escape(old), lambda m: new, s, flags=re.IGNORECASE)
    return s


def _reg_decode(typ, data, pairs):
    if typ in (winreg.REG_SZ, winreg.REG_EXPAND_SZ):
        return _repl_str(str(data), pairs)
    if typ == winreg.REG_MULTI_SZ:
        return [_repl_str(str(x), pairs) for x in (data or [])]
    if typ in (winreg.REG_DWORD, winreg.REG_QWORD):
        return int(data or 0)
    if isinstance(data, dict) and "b64" in data:
        return base64.b64decode(data["b64"])
    if isinstance(data, str):
        return _repl_str(data, pairs)
    return data


def _create_key_tree(hive_name, path, node, pairs, errors):
    hive = HIVES[hive_name]
    wow = winreg.KEY_WOW64_64KEY if hive_name == "HKLM" else 0
    try:
        k = winreg.CreateKeyEx(hive, path, 0, winreg.KEY_WRITE | wow)
    except OSError as e:
        errors.append("%s\\%s 创建失败：%s" % (hive_name, path, e))
        return
    try:
        for v in node.get("values", []):
            typ = int(v.get("type", 1))
            try:
                winreg.SetValueEx(k, v.get("name", ""), 0, typ, _reg_decode(typ, v.get("data"), pairs))
            except OSError as e:
                errors.append("%s\\%s 值 %s 写入失败：%s" % (hive_name, path, v.get("name"), e))
    finally:
        winreg.CloseKey(k)
    for c in node.get("keys", []):
        _create_key_tree(hive_name, path + "\\" + c["name"], c, pairs, errors)


TEXT_EXT = {".ini", ".cfg", ".conf", ".config", ".xml", ".json", ".txt", ".properties",
            ".yaml", ".yml", ".bat", ".cmd", ".ps1", ".lua", ".reg", ".toml", ".env",
            ".settings", ".prefs", ".sav"}


def rewrite_paths_in_tree(target_dir, pairs):
    changed = 0
    if not pairs:
        return 0
    for root, dirs, files in os.walk(lp(target_dir)):
        for f in files:
            if os.path.splitext(f)[1].lower() not in TEXT_EXT:
                continue
            p = os.path.join(root, f)
            try:
                if os.path.getsize(lp(p)) > 8 * 1024 * 1024:
                    continue
                with open(lp(p), "rb") as fr:
                    raw = fr.read()
            except Exception:
                continue
            if b"\x00" in raw[:2048] and raw[:2] not in (b"\xff\xfe", b"\xfe\xff"):
                continue
            enc = "utf-8"
            try:
                txt = raw.decode("utf-8")
            except UnicodeDecodeError:
                try:
                    txt = raw.decode("utf-16")
                    enc = "utf-16"
                except UnicodeDecodeError:
                    try:
                        txt = raw.decode("mbcs")
                        enc = "mbcs"
                    except Exception:
                        continue
            hit = False
            for old, new in pairs:
                if old and new and old.lower() != new.lower() and old.lower() in txt.lower():
                    txt = re.sub(re.escape(old), lambda m: new, txt, flags=re.IGNORECASE)
                    hit = True
            if hit:
                try:
                    with open(lp(p), "wb") as fw:
                        fw.write(txt.encode(enc))
                    changed += 1
                except Exception:
                    pass
    return changed


# ---------------- 导出 ----------------

def _zip_add_file(zf, src, arc, hashes, progress, total, done, fast=False, cancel=None):
    """单个文件入包：一次 stat、4MB 大块读写（比 1MB 循环快），SHA-256 边写边算。"""
    size = 0
    try:
        zi = zipfile.ZipInfo.from_file(lp(src), arc)
        size = zi.file_size
        ext = os.path.splitext(src)[1].lower()
        zi.compress_type = zipfile.ZIP_STORED if ext in NO_COMPRESS_EXT else zipfile.ZIP_DEFLATED
        zi.external_attr = 0o600 << 16
        h = hashlib.sha256() if hashes is not None else None
        with open(lp(src), "rb") as fr, zf.open(zi, "w", force_zip64=True) as fw:
            while True:
                if _aborted(cancel):
                    raise PackAbort()
                chunk = fr.read(4 * 1024 * 1024)
                if not chunk:
                    break
                fw.write(chunk)
                if h:
                    h.update(chunk)
                done[0] += len(chunk)
                if progress:
                    progress(min(done[0], total * 0.99), total)
        if hashes is not None:
            hashes[arc] = {"size": size, "sha256": h.hexdigest()}
    except PackAbort:
        raise
    except Exception as e:
        done[0] += size
        if progress:
            progress(min(done[0], total * 0.99), total)
        return str(e)
    return None


def _walk_files(base, skip_cache):
    files, dirs = [], []
    for root, dirnames, filenames in os.walk(lp(base)):
        dirnames[:] = [d for d in dirnames if d.lower() not in JUNK_SKIP and not is_reparse(os.path.join(root, d))]
        if skip_cache:
            dirnames[:] = [d for d in dirnames if d.lower() not in CACHE_DIR_NAMES]
        rel = os.path.relpath(root, base)
        dirs.append(rel)
        for f in filenames:
            if skip_cache and os.path.splitext(f)[1].lower() in CACHE_FILE_EXT:
                continue
            p = os.path.join(root, f)
            if os.path.islink(p):
                continue
            if is_lockish(p):
                # 运行中软件的锁文件（.lock / .lck）是临时状态，打包和还原都没意义
                continue
            files.append(p)
    return files, dirs


def build_readme(manifest):
    lines = []
    lines.append("=" * 64)
    lines.append("   软件迁移包 · 使用说明")
    lines.append("=" * 64)
    lines.append("")
    lines.append("打包时间：%s　源电脑：%s" % (manifest.get("created", ""), manifest.get("source_computer", "")))
    lines.append("包含软件：%d 个" % len(manifest.get("apps", [])))
    lines.append("")
    lines.append("先看这个：本文件就是安装说明。同目录还有《安装说明.html》，双击用浏览器打开排版更清楚。")
    lines.append("压缩包本身就是普通 zip，WinRAR / 7-Zip / 系统自带解压都能直接双击打开，不用本工具也能手工还原。")
    lines.append("")
    for i, a in enumerate(manifest.get("apps", []), 1):
        lines.append("%d) %s%s" % (i, a["program"]["name"],
                                   ("  " + a["program"]["version"]) if a["program"].get("version") else ""))
        lines.append("   原始路径：%s" % (a.get("original_install_dir") or "未记录"))
        lines.append("   文件：%d 个 / %s　目录：%d 处　注册表：%d 项" % (
            a["stats"]["files"], human_size(a["stats"]["bytes"]),
            len(a.get("data_dirs") or []), len(a.get("reg_keys") or [])))
        lines.append("   目录清单（每个目录里是什么）：")
        lines.append("   - [程序本体] %s" % (a.get("original_install_dir") or "未记录"))
        lines.append("      里面是：程序 exe/dll/资源文件，软件能不能打开全靠它。")
        for d in a.get("data_dirs") or []:
            lines.append("   - [%s] %s" % (d.get("kind", ""), d.get("orig_path", "")))
            lines.append("      里面是：%s" % (d.get("desc") or "该软件的用户数据"))
    lines.append("")
    cache_on = bool((manifest.get("include") or {}).get("cache", True))
    if cache_on:
        lines.append("说明：本包含该软件全部相关目录，缓存与日志也一并打包（还原后与原机完全一致）。")
    else:
        lines.append("说明：打包时取消了『缓存文件』勾选，Cache/Log 等纯缓存目录未放入本包；"
                     "其余程序文件、配置、存档齐全，配置与登录状态不受影响。")
    lines.append("")
    lines.append("")
    lines.append("【怎么放到新电脑上 · 用本工具（推荐，30 秒）】")
    lines.append("1. 把『软件迁移助手.exe』和本压缩包一起拷到新电脑（U 盘/网盘都行，放哪都随意）。")
    lines.append("2. 双击 软件迁移助手.exe —— 不用装 Python，绿色单文件。若被拦：点『更多信息 → 仍要运行』。")
    lines.append("3. 点顶部『还原安装』→『选择迁移包』→ 选中本压缩包。")
    lines.append("4. 安装位置默认就是原路径；想换盘可填统一父目录（如 D:\\Apps），工具会各自建子文件夹。")
    lines.append("5. 勾选『还原配置/存档』『写入注册表』『桌面生成启动图标』，点『开始还原』。")
    lines.append("6. 装完桌面会出现每个软件的快捷方式，双击就能用。")
    lines.append("")
    lines.append("【没有工具时的手工还原（也能用）】")
    lines.append("1. 用 WinRAR / 7-Zip / 系统自带解压直接双击打开本压缩包（它就是个 zip）。")
    lines.append("2. apps\\app1\\program 里的全部内容 → 复制到新电脑的目标文件夹（见上面『原始路径』）。")
    lines.append("3. apps\\app1\\userdata 下的各目录分别还原到（子文件夹名保持原样）：")
    lines.append("   roaming → %APPDATA%　local → %LOCALAPPDATA%　programdata → %PROGRAMDATA%")
    lines.append("   locallow → %USERPROFILE%\\AppData\\LocalLow　savedgames → %USERPROFILE%\\Saved Games")
    lines.append("   documents → 『文档』　userprofile → C:\\Users\\用户名　desktop → 桌面")
    lines.append("   sibling / registry → 直接照上面『目录清单』里写的原路径放回（子文件夹名不变）")
    lines.append("   （目录名里带 Cache/Log 的那几个是缓存，照原样放回即可；不放也不影响软件能打开，只是少了历史缓存）")
    lines.append("4. 进入目标文件夹，双击主程序 exe 即可运行（多数软件换路径也能直接跑）。")
    lines.append("")
    lines.append("【注意】")
    lines.append("- 驱动、系统服务、内核组件（杀毒/虚拟网卡/输入法）无法搬运，需在新电脑重装。")
    lines.append("- 需联网激活 / 硬件绑定的授权类软件，文件能搬，授权需重新激活。")
    lines.append("- 新电脑缺运行库（VC++ / .NET / DirectX）会提示缺 DLL，装运行库即可。")
    lines.append("- 32 位软件搬到 64 位系统可用；反向不行。")
    if manifest.get("runtimes"):
        lines.append("")
        lines.append("【源电脑装过的运行库（供参考）】")
        for r in manifest["runtimes"][:12]:
            lines.append("  - %s" % r)
    lines.append("")
    lines.append("=" * 64)
    return "\r\n".join(lines)


def build_readme_html(manifest):
    """同一份说明的网页版：双击就能在浏览器里看（不依赖本工具、不用会打开 smig）"""
    e = _html.escape
    apps = manifest.get("apps", [])

    def row(k, v):
        return "<tr><td class=k>%s</td><td>%s</td></tr>" % (e(k), v)

    parts = []
    parts.append("""<!DOCTYPE html><html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>软件迁移包 · 安装说明</title>
<style>
body{margin:0;background:#f4f6fb;color:#1d2433;font:15px/1.75 "Microsoft YaHei UI","Segoe UI",sans-serif}
.wrap{max-width:960px;margin:0 auto;padding:28px 18px 60px}
.card{background:#fff;border:1px solid #e3e8f2;border-radius:14px;padding:22px 24px;margin-bottom:16px}
h1{font-size:24px;margin:0 0 6px} h2{font-size:17px;margin:0 0 12px;color:#2b3550}
.sub{color:#6b7488;font-size:13px;margin-bottom:18px}
.k{color:#6b7488;width:96px;white-space:nowrap;vertical-align:top}
table{border-collapse:collapse;width:100%} td{padding:4px 8px;border-bottom:1px dashed #edeff5;vertical-align:top;font-size:14px}
ol,ul{margin:0;padding-left:22px} li{margin:5px 0}
.dir{background:#f7f9ff;border:1px solid #e6ecfb;border-radius:10px;padding:10px 12px;margin:8px 0}
.dir .p{font-family:Consolas,monospace;font-size:13px;color:#2b3550;word-break:break-all}
.dir .why{color:#5b6478;font-size:13px;margin-top:4px}
.tag{display:inline-block;background:#eef3ff;color:#3355cc;border-radius:6px;padding:0 7px;font-size:12px;margin-right:6px}
.tag.warn{background:#fff2ed;color:#c04a20}
.appname{font-size:16px;font-weight:600;margin:0 0 4px}
.note{color:#8a6a1f;background:#fff8e6;border:1px solid #f4e3b8;border-radius:10px;padding:10px 12px;font-size:13px}
</style></head><body><div class="wrap">""")
    parts.append("<div class=card><h1>软件迁移包 · 安装说明</h1>")
    parts.append("<div class=sub>打包时间 %s　源电脑 %s　共 %d 个软件　压缩包大小见文件名</div>" % (
        e(manifest.get("created", "")), e(manifest.get("source_computer", "")), len(apps)))
    parts.append("<table>")
    tv = "%s v%s" % (manifest.get("tool", ""), manifest.get("tool_version", ""))
    parts.append(row("工具版本", e(tv)))
    st = manifest.get("stats", {})
    parts.append(row("总文件", "%d 个 / %s" % (st.get("files", 0), human_size(st.get("bytes", 0)))))
    parts.append("</table></div>")

    parts.append("<div class=card><h2>第一步：把包拷到新电脑</h2><ol>"
                 "<li>把本压缩包（和可选的『软件迁移助手.exe』）一起拷到新电脑，U 盘、网盘、局域网都行，放哪都无所谓。</li>"
                 "<li>不用装 Python、不用装任何东西——本工具是绿色单文件 exe，双击即用。</li>"
                 "</ol></div>")

    parts.append("<div class=card><h2>第二步：一键还原（推荐）</h2><ol>"
                 "<li>双击『软件迁移助手.exe』。若 Windows 弹蓝色提示：点『更多信息 → 仍要运行』。</li>"
                 "<li>顶部切到『还原安装』→ 点『选择迁移包』→ 选中本压缩包（.zip）。</li>"
                 "<li>安装位置默认＝原路径；想换盘就在『统一父目录』填一个目录（如 D:\\Apps），工具会给每个软件各建一个文件夹。</li>"
                 "<li>勾上『还原配置/存档』『写入注册表』『桌面生成启动图标』，点『开始还原』。</li>"
                 "<li>完成后桌面会出现每个软件的快捷方式，双击就能用，登录状态、聊天记录、存档都在。</li>"
                 "</ol></div>")

    parts.append("<div class=card><h2>也可以手工还原（没有工具时）</h2><ol>"
                 "<li>本压缩包就是普通 zip：WinRAR / 7-Zip / 系统自带解压都能直接双击打开，右边文件夹就是各软件的数据。</li>"
                 "<li><b>program</b> 文件夹里的全部内容 → 复制到下表『原始路径』对应的文件夹（没有就新建）。</li>"
                 "<li><b>userdata</b> 下按子文件夹名放回："
                 "<span class=tag>roaming → %APPDATA%</span>"
                 "<span class=tag>local → %LOCALAPPDATA%</span>"
                 "<span class=tag>programdata → %PROGRAMDATA%</span>"
                 "<span class=tag>locallow → %USERPROFILE%\\AppData\\LocalLow</span>"
                 "<span class=tag>savedgames → %USERPROFILE%\\Saved Games</span>"
                 "<span class=tag>documents → 『文档』</span>"
                 "<span class=tag>userprofile → C:\\Users\\用户名</span>"
                 "<span class=tag>desktop → 桌面</span>"
                 "<span class=tag>sibling / registry → 照下表原路径放回</span>"
                 "</li>"
                 "<li>最后进目标文件夹双击主程序 exe 就能打开。想有桌面图标，右键 exe →『发送到 → 桌面快捷方式』。</li>"
                 "</ol></div>")

    for i, a in enumerate(apps, 1):
        parts.append("<div class=card><div class=appname>%d) %s %s</div>" % (
            i, e(a["program"]["name"]), e(a["program"].get("version", ""))))
        parts.append("<table>")
        parts.append(row("原始路径", "<span style='font-family:Consolas,monospace'>%s</span>" % e(a.get("original_install_dir") or "未记录")))
        parts.append(row("主程序", e(a.get("entry_exe") or "（见 program 文件夹里的 exe）")))
        parts.append(row("体积", "%d 个文件 / %s　相关目录 %d 处　注册表 %d 项" % (
            a["stats"]["files"], human_size(a["stats"]["bytes"]),
            len(a.get("data_dirs") or []), len(a.get("reg_keys") or []))))
        parts.append("</table>")
        parts.append("<div class=dir><div class=p>[程序本体] %s</div>"
                     "<div class=why>里面是：程序 exe / dll / 资源文件，软件能不能打开全靠它。</div></div>"
                     % e(a.get("original_install_dir") or "未记录"))
        for d in a.get("data_dirs") or []:
            tag = "<span class='tag warn'>缓存</span>" if d.get("cache") else "<span class=tag>%s</span>" % e(d.get("kind", ""))
            parts.append("<div class=dir><div class=p>%s%s</div><div class=why>里面是：%s</div></div>" % (
                tag, e(d.get("orig_path", "")), e(d.get("desc") or "该软件的用户数据")))
        parts.append("</div>")

    cache_on = bool((manifest.get("include") or {}).get("cache", True))
    if cache_on:
        parts.append("<div class=card><div class=note>本包含该软件全部相关目录，缓存、日志、更新包也一并打包，还原后与原机完全一致。"
                     "带『缓存』标记的目录只是加速与历史临时数据，手工还原时可放可不放，不影响软件打开。</div></div>")
    else:
        parts.append("<div class=card><div class=note>打包时取消了『缓存文件』勾选：Cache/Log 这类纯缓存目录没有放进本包，"
                     "体积更小；程序文件、配置、登录状态、存档都齐全。手工还原时跳过带『缓存』标记的目录即可。</div></div>")
    parts.append("<div class=card><h2>注意事项</h2><ul>"
                 "<li>驱动、系统服务、内核组件（杀毒 / 虚拟网卡 / 输入法）无法搬运，需要在新电脑重装。</li>"
                 "<li>要联网激活或绑定硬件的授权类软件，文件能搬，授权要重新登录/激活。</li>"
                 "<li>新电脑缺运行库（VC++ / .NET / DirectX）会提示缺 DLL，补装运行库即可。</li>"
                 "<li>32 位软件可以搬到 64 位系统；反过来不行。</li>"
                 "<li>写到 C:\\Program Files 等受保护位置需要管理员权限：右键 exe →『以管理员身份运行』。</li>"
                 "</ul></div>")
    parts.append("</div></body></html>")
    return "".join(parts)


def export_package(infos, out_file, include, extras=None, log=None, progress=None,
                   with_hash=True, skip_cache=False, fast=False, cancel=None, brief=None):
    valid = [i for i in infos if i and i.get("install_dir") and os.path.isdir(i["install_dir"])]
    if not valid:
        raise RuntimeError("没有可打包的有效目录。")

    extras = extras or []
    total = 0
    plan = []
    for idx, info in enumerate(valid, 1):
        key = "app%d" % idx
        files, ddirs = ([], [])
        if include.get("program"):
            files, ddirs = _walk_files(info["install_dir"], skip_cache)
        pbytes = 0
        for f in files:
            try:
                sz = os.path.getsize(lp(f))
                total += sz
                pbytes += sz
            except Exception:
                pass
        # 用户数据目录的体积已经在分析阶段算好，直接计入总字节，否则进度会冲过 100%
        if include.get("userdata"):
            for d in info.get("data_dirs") or []:
                if skip_cache and d.get("cache"):
                    continue
                try:
                    total += max(0, int(d.get("size") or 0))
                except Exception:
                    pass
        plan.append((key, info, files, ddirs, pbytes))

    for ex in extras:
        ex["_files"] = []
        ex["_dirs"] = []
        if os.path.isdir(ex["path"]):
            fs, ds = _walk_files(ex["path"], skip_cache)
            ex["_files"] = fs
            ex["_dirs"] = ds
            for f in fs:
                try:
                    total += os.path.getsize(lp(f))
                except Exception:
                    pass

    total = max(total, 1)
    done = [0]
    last_t = [0.0]

    def tick(prefix="进度"):
        """节流产生一行简洁滚动日志（最多 1.5 秒一行）"""
        if not brief:
            return
        now = time.time()
        if now - last_t[0] < 1.5:
            return
        last_t[0] = now
        pct = int(min(99.0, done[0] * 100.0 / total))
        brief("%s %d%% · %s / %s" % (prefix, pct, human_size(done[0]), human_size(total)))

    hashes = {} if with_hash else None
    manifest = {"tool": APP_NAME, "tool_version": APP_VER, "format": 2,
                "created": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "source_computer": computer_name(), "include": include,
                "apps": [],
                "extras": [{"path": e["path"], "arc": "extras/%d" % i} for i, e in enumerate(extras, 1)],
                "runtimes": installed_runtimes() if include.get("runtimes") else [],
                "hashes": {}, "stats": {"files": 0, "bytes": 0}}

    skipped, errors = [], []
    with zipfile.ZipFile(out_file, "w", zipfile.ZIP_DEFLATED, allowZip64=True,
                         compresslevel=COMPRESS_LEVEL) as zf:
        for key, info, files, ddirs, pbytes in plan:
            if _aborted(cancel):
                raise PackAbort()
            app = {"key": key, "program": info["program"],
                   "original_install_dir": info["install_dir"],
                   "install_desc": info.get("install_desc", ""),
                   "entry_exe": (info["entry_exes"][0] if info["entry_exes"] else ""),
                   "data_dirs": [{"kind": d["kind"], "name": d["name"], "rel": d.get("rel") or d["name"],
                                  "orig_path": d["path"],
                                  "desc": ((d.get("desc") or "").replace("照原样打包，还原后与原机一致",
                                                                         "本次已跳过（未打包缓存）")
                                           if skip_cache else d.get("desc", "")),
                                  "cache": bool(d.get("cache")),
                                  "is_file": bool(d.get("is_file")),
                                  "size": d.get("size", 0), "count": d.get("count", 0)}
                                 for d in info["data_dirs"] if not (skip_cache and d.get("cache"))],
                   "reg_keys": info["reg_keys"], "services": info["services"],
                   "warnings": info["warnings"], "stats": {"files": 0, "bytes": 0}}
            if include.get("program"):
                if brief:
                    brief("开始 %s：%d 个文件 / %s" % (
                        info["program"]["name"], len(files), human_size(pbytes)))
                for f in files:
                    rel = os.path.relpath(f, info["install_dir"])
                    err = _zip_add_file(zf, f, "%s/program/%s" % (key, rel.replace("\\", "/")),
                                        hashes, progress, total, done, False, cancel)
                    app["stats"]["files"] += 1
                    manifest["stats"]["files"] += 1
                    try:
                        app["stats"]["bytes"] += os.path.getsize(lp(f))
                    except Exception:
                        pass
                    if err:
                        skipped.append("%s（%s）" % (f, err))
                    tick("%s 程序" % info["program"]["name"][:18])
                for d in ddirs:
                    if d != ".":
                        try:
                            zf.writestr("%s/program/%s/" % (key, d.replace("\\", "/")), "")
                        except Exception:
                            pass
            if include.get("userdata"):
                for d in info["data_dirs"]:
                    if skip_cache and d.get("cache"):
                        if log:
                            log("  跳过缓存目录：%s" % d["path"])
                        continue
                    base_arc = "%s/userdata/%s/%s" % (key, d["kind"], arc_rel(d))
                    if d.get("is_file"):
                        if not os.path.isfile(d["path"]):
                            continue
                        err = _zip_add_file(zf, d["path"], base_arc, hashes, progress, total, done, False, cancel)
                        app["stats"]["files"] += 1
                        manifest["stats"]["files"] += 1
                        try:
                            app["stats"]["bytes"] += os.path.getsize(lp(d["path"]))
                        except Exception:
                            pass
                        if err:
                            skipped.append("%s（%s）" % (d["path"], err))
                        continue
                    if not os.path.isdir(d["path"]):
                        continue
                    if brief:
                        brief("数据目录 %s（%s）" % (d["name"], human_size(d.get("size") or 0)))
                    fs, subdirs = _walk_files(d["path"], skip_cache)
                    arc_base = base_arc + "/"
                    try:
                        zf.writestr(arc_base, "")
                    except Exception:
                        pass
                    for sd in subdirs:
                        if sd == ".":
                            continue
                        try:
                            zf.writestr(arc_base + sd.replace("\\", "/") + "/", "")
                        except Exception:
                            pass
                    for f in fs:
                        rel = os.path.relpath(f, d["path"])
                        err = _zip_add_file(zf, f, arc_base + rel.replace("\\", "/"),
                                            hashes, progress, total, done, False, cancel)
                        app["stats"]["files"] += 1
                        manifest["stats"]["files"] += 1
                        try:
                            app["stats"]["bytes"] += os.path.getsize(lp(f))
                        except Exception:
                            pass
                        if err:
                            skipped.append("%s（被占用/无权限）" % f)
            if include.get("shortcuts"):
                sc = []
                for i, s in enumerate(info["shortcuts"]):
                    try:
                        arc = "%s/shortcuts/%d.lnk" % (key, i)
                        with open(lp(s["path"]), "rb") as f:
                            zf.writestr(arc, f.read())
                        sc.append({"arc": arc, "scope": s["scope"], "kind": s["kind"], "rel": s["rel"],
                                   "name": os.path.basename(s["path"]), "target": s.get("target", ""),
                                   "args": s.get("args", ""), "workdir": s.get("workdir", ""),
                                   "icon": s.get("icon", ""), "desc": s.get("desc", "")})
                    except Exception as e:
                        errors.append("快捷方式 %s：%s" % (s["path"], e))
                app["shortcuts"] = sc
            if include.get("registry") and info["reg_keys"]:
                trees = []
                for k in info["reg_keys"]:
                    try:
                        trees.append({"hive": k["hive"], "path": k["path"], "role": k.get("role", "app"),
                                      "data": export_key_tree(k["hive"], k["path"])})
                    except Exception as e:
                        errors.append("注册表 %s\\%s：%s" % (k["hive"], k["path"], e))
                app["registry"] = trees
                zf.writestr("%s/registry.json" % key, json.dumps(trees, ensure_ascii=False))
            manifest["apps"].append(app)

        for i, ex in enumerate(extras, 1):
            ex_dirs = ex.get("_dirs") or []
            try:
                zf.writestr("extras/%d/" % i, "")
            except Exception:
                pass
            for sd in ex_dirs:
                if sd == ".":
                    continue
                try:
                    zf.writestr("extras/%d/%s/" % (i, sd.replace("\\", "/")), "")
                except Exception:
                    pass
            for f in ex.get("_files") or []:
                rel = os.path.relpath(f, ex["path"])
                err = _zip_add_file(zf, f, "extras/%d/%s" % (i, rel.replace("\\", "/")),
                                    hashes, progress, total, done, False, cancel)
                manifest["stats"]["files"] += 1
                if err:
                    skipped.append("%s（%s）" % (f, err))
                tick("附加目录 %d" % i)

        manifest["stats"]["bytes"] = sum(a["stats"]["bytes"] for a in manifest["apps"])
        if skipped:
            manifest["skipped"] = skipped[:300]
        if errors:
            manifest["errors"] = errors[:300]
        manifest["hashes"] = hashes or {}
        if brief:
            brief("全部写入完成，正在生成说明与校验…")
        zf.writestr(MANIFEST_NAME, json.dumps(manifest, ensure_ascii=False, indent=1))
        zf.writestr("安装说明.txt", build_readme(manifest).encode("utf-8-sig"))
        zf.writestr("安装说明.html", build_readme_html(manifest).encode("utf-8"))
    if progress:
        progress(1, 1)
    return manifest, skipped


# ---------------- 导入 ----------------

def _adapt_manifest(man):
    """兼容 v1 单应用包"""
    if man.get("apps"):
        return man
    if man.get("program"):
        app = {"key": "app1", "program": man["program"],
               "original_install_dir": man.get("original_install_dir", ""),
               "entry_exe": man.get("entry_exe", ""),
               "data_dirs": man.get("data_dirs", []), "reg_keys": man.get("reg_keys", []),
               "services": man.get("services", []), "warnings": man.get("warnings", []),
               "registry": man.get("registry", []), "shortcuts": man.get("shortcuts", []),
               "stats": man.get("stats", {"files": 0, "bytes": 0})}
        man["apps"] = [app]
        man["legacy_prefix"] = "files/"
        man["hashes"] = {("app1/program/" + k[len("files/program/"):] if k.startswith("files/program/") else k): v
                         for k, v in (man.get("hashes") or {}).items()}
    return man


def _uniq_target(base):
    if not base:
        return base
    if not os.path.isdir(base) or not os.listdir(base):
        return base
    for i in range(1, 60):
        cand = "%s_迁移" % base.rstrip("\\") if i == 1 else "%s_迁移%d" % (base.rstrip("\\"), i)
        if not os.path.isdir(cand) or not os.listdir(cand):
            return cand
    return base + "_迁移"


def import_package(pkg_path, target_dir, include, log=None, progress=None, portable=False,
                   parent_dir=""):
    result = {"ok": True, "errors": [], "notes": [], "skipped": [], "apps": [], "targets": {}, "check": []}
    with zipfile.ZipFile(pkg_path, "r") as zf:
        names = zf.namelist()
        man = _adapt_manifest(json.loads(zf.read(MANIFEST_NAME).decode("utf-8")))
        legacy = man.get("legacy_prefix") == "files/"
        apps = man["apps"]

        targets = {}
        for a in apps:
            key = a["key"]
            orig = (a.get("original_install_dir") or "").rstrip("\\")
            if parent_dir:
                tgt = os.path.join(parent_dir, safe_name(os.path.basename(orig) or a["program"]["name"]))
                tgt = _uniq_target(tgt)
            else:
                tgt = orig or os.path.join(os.environ.get("SystemDrive", "C:") + "\\", "Apps",
                                           safe_name(a["program"]["name"]))
            targets[key] = tgt

        # 只统计「本次真的会解出来」的文件，进度才不会停在半路或提前满
        prefixes = []
        for a in apps:
            pre_key = "files/" if legacy else "%s/" % a["key"]
            if include.get("program"):
                prefixes.append(pre_key + "program/")
            if include.get("userdata"):
                for d in a.get("data_dirs", []):
                    nm = arc_rel(d)
                    if legacy:
                        prefixes.append("files/userdata/%s/%s/" % (d["kind"], nm))
                    else:
                        prefixes.append("%suserdata/%s/%s/" % (pre_key, d["kind"], nm))
        total = 0
        for i in zf.infolist():
            if i.filename.endswith("/"):
                continue
            if prefixes and not any(i.filename.startswith(p) for p in prefixes):
                continue
            total += i.file_size
        total = max(total, 1)
        done = [0]
        hashes = man.get("hashes") or {}
        mismatch = []

        for a in apps:
            key = a["key"]
            tgt = targets[key]
            orig = (a.get("original_install_dir") or "").rstrip("\\")
            pairs = []
            if orig and tgt and os.path.abspath(orig).lower() != os.path.abspath(tgt).lower():
                pairs.append((orig, os.path.abspath(tgt).rstrip("\\")))
            try:
                os.makedirs(lp(tgt), exist_ok=True)
            except Exception as e:
                result["errors"].append("无法创建 %s：%s" % (tgt, e))
                continue

            if include.get("program"):
                pre = ("files/" if legacy else "%s/" % key) + "program/"
                exp_prog = [n for n in names if n.startswith(pre) and not n.endswith("/")]
                got_prog = 0
                miss_prog = []
                for n in names:
                    if not n.startswith(pre):
                        continue
                    rel = n[len(pre):]
                    if not rel:
                        continue
                    if n.endswith("/"):
                        try:
                            os.makedirs(lp(os.path.join(tgt, rel.rstrip("/"))), exist_ok=True)
                        except Exception:
                            pass
                        continue
                    dst = os.path.join(tgt, rel.replace("/", os.sep))
                    _make_writable(dst)
                    try:
                        os.makedirs(lp(os.path.dirname(dst)), exist_ok=True)
                        with zf.open(n) as fr, open(lp(dst), "wb") as fw:
                            while True:
                                chunk = fr.read(1024 * 512)
                                if not chunk:
                                    break
                                fw.write(chunk)
                                done[0] += len(chunk)
                                if progress:
                                    progress(min(done[0], total * 0.99), total)
                        got_prog += 1
                    except Exception as e:
                        miss_prog.append(rel)
                        result["errors"].append("写入 %s 失败：%s" % (dst, e))
                        continue
                    hkey = n if not legacy else n.replace("files/program/", "app1/program/", 1)
                    h = hashes.get(n) or hashes.get(hkey)
                    if h and h.get("sha256"):
                        try:
                            sha = hashlib.sha256()
                            with open(lp(dst), "rb") as f:
                                while True:
                                    c = f.read(1024 * 512)
                                    if not c:
                                        break
                                    sha.update(c)
                            if sha.hexdigest() != h["sha256"]:
                                mismatch.append(rel)
                        except Exception:
                            pass
                result["check"].append({"app": a["program"]["name"], "kind": "program",
                                        "label": "程序文件", "target": tgt,
                                        "expected": len(exp_prog), "written": got_prog,
                                        "missing": miss_prog[:12], "skipped": 0})

            if include.get("userdata"):
                for d in a.get("data_dirs", []):
                    pre = ("files/userdata/%s/%s/" % (d["kind"], arc_rel(d))) if legacy \
                        else ("%s/userdata/%s/%s/" % (key, d["kind"], arc_rel(d)))
                    pre_file = pre.rstrip("/")
                    up = os.environ.get("USERPROFILE", "")
                    k = d["kind"]
                    dstbase = ""
                    if k in ("sibling", "registry", "drive", "manual"):
                        # 这类目录就是原机上的具体路径，还原回原处
                        base = os.path.dirname((d.get("orig_path") or "").rstrip("\\"))
                    elif k == "locallow":
                        base = os.path.join(up, "AppData", "LocalLow")
                    elif k == "savedgames":
                        base = os.path.join(up, "Saved Games")
                    else:
                        base = {"roaming": os.environ.get("APPDATA", ""),
                                "local": os.environ.get("LOCALAPPDATA", ""),
                                "programdata": os.environ.get("PROGRAMDATA", ""),
                                "documents": os.path.join(known_folder(0x05) or up, "Documents"),
                                "publicdocuments": os.path.join(os.environ.get("PUBLIC", os.path.join("C:\\Users", "Public")), "Documents"),
                                "public": os.environ.get("PUBLIC", os.path.join("C:\\Users", "Public")),
                                "userprofile": up,
                                "mydocuments": known_folder(0x05) or "",
                                "desktop": known_folder(0x10) or ""}.get(k, "")
                    if not base:
                        # 不认识的类型：直接按它在原机上的绝对路径放回原处，保证任何包都还原得回去
                        op = (d.get("orig_path") or "").rstrip("\\")
                        base = os.path.dirname(op) if op else ""
                        if base:
                            dstbase = op
                            result["notes"].append("[%s] 未知目录类型 %s，按原路径还原：%s" % (
                                a["program"]["name"], k, op))
                    if not base:
                        result["notes"].append("[%s] 跳过未知目录类型 %s（%s）" % (
                            a["program"]["name"], k, d.get("orig_path", "")))
                        continue
                    if not dstbase:
                        dstbase = os.path.join(base, dst_rel(d))
                    cnt = 0
                    exp_n = 0
                    skip_n = 0
                    miss_n = []
                    if d.get("is_file"):
                        exp_n = 1 if pre_file in names else 0
                        if pre_file in names:
                            try:
                                os.makedirs(lp(os.path.dirname(dstbase)), exist_ok=True)
                                with zf.open(pre_file) as fr, open(lp(dstbase), "wb") as fw:
                                    while True:
                                        chunk = fr.read(1024 * 512)
                                        if not chunk:
                                            break
                                        fw.write(chunk)
                                        done[0] += len(chunk)
                                        if progress:
                                            progress(min(done[0], total * 0.99), total)
                                cnt = 1
                            except Exception as e:
                                if is_lockish(dstbase) or is_busy_error(e):
                                    result["skipped"].append(dstbase)
                                    skip_n = 1
                                else:
                                    result["errors"].append("还原 %s 失败：%s" % (dstbase, e))
                                    miss_n.append(d["name"])
                        if cnt:
                            result["notes"].append("[%s] 配置文件 %s（%d 个）" % (
                                a["program"]["name"], d["name"], cnt))
                        result["check"].append({"app": a["program"]["name"], "kind": "data",
                                                "label": (d.get("name") or d.get("orig_path") or ""),
                                                "target": dstbase, "expected": exp_n, "written": cnt,
                                                "missing": miss_n, "skipped": skip_n,
                                                "is_file": True})
                        continue
                    exp_n = len([n for n in names if n.startswith(pre) and not n.endswith("/")])
                    if not d.get("is_file"):
                        try:
                            os.makedirs(lp(dstbase), exist_ok=True)
                        except Exception:
                            pass
                    for n in names:
                        if not n.startswith(pre):
                            continue
                        if n.endswith("/"):
                            rel = n[len(pre):].rstrip("/")
                            if rel:
                                try:
                                    os.makedirs(lp(os.path.join(dstbase, rel.replace("/", os.sep))), exist_ok=True)
                                except Exception:
                                    pass
                            continue
                        dst = os.path.join(dstbase, n[len(pre):].replace("/", os.sep))
                        if is_lockish(dst):
                            result["skipped"].append(dst)
                            skip_n += 1
                            continue
                        _make_writable(dst)
                        try:
                            os.makedirs(lp(os.path.dirname(dst)), exist_ok=True)
                            with zf.open(n) as fr, open(lp(dst), "wb") as fw:
                                while True:
                                    chunk = fr.read(1024 * 512)
                                    if not chunk:
                                        break
                                    fw.write(chunk)
                                    done[0] += len(chunk)
                                    if progress:
                                        progress(min(done[0], total * 0.99), total)
                            cnt += 1
                        except Exception as e:
                            if is_lockish(dst) or is_busy_error(e):
                                result["skipped"].append(dst)
                                skip_n += 1
                            else:
                                result["errors"].append("还原 %s 失败：%s" % (dst, e))
                                miss_n.append(n[len(pre):])
                    if cnt:
                        result["notes"].append("[%s] 用户数据 %s（%d 个文件）" % (a["program"]["name"], d["name"], cnt))
                    result["check"].append({"app": a["program"]["name"], "kind": "data",
                                            "label": (d.get("name") or d.get("orig_path") or ""),
                                            "target": dstbase, "expected": exp_n, "written": cnt,
                                            "missing": miss_n[:12], "skipped": skip_n})

            if pairs:
                n2 = rewrite_paths_in_tree(tgt, pairs)
                if n2:
                    result["notes"].append("[%s] 已改写 %d 个配置文件里的旧路径" % (a["program"]["name"], n2))

            if include.get("registry") and not portable:
                trees = a.get("registry")
                if trees is None and legacy:
                    try:
                        trees = json.loads(zf.read("registry.json").decode("utf-8"))
                    except Exception:
                        trees = []
                if trees:
                    if not is_admin() and any(t["hive"] == "HKLM" for t in trees):
                        result["notes"].append("非管理员，[%s] 的 HKLM 注册表已跳过。" % a["program"]["name"])
                    reg_errors = []
                    written = skipped_reg = 0
                    for t in trees:
                        if t["hive"] == "HKLM" and not is_admin():
                            skipped_reg += 1
                            continue
                        try:
                            _create_key_tree(t["hive"], t["path"], t["data"], pairs, reg_errors)
                            written += 1
                        except Exception as e:
                            reg_errors.append("%s\\%s：%s" % (t["hive"], t["path"], e))
                    if written:
                        result["notes"].append("[%s] 已写入 %d 个注册表项" % (a["program"]["name"], written))
                    for e in reg_errors[:20]:
                        result["errors"].append("注册表：" + e)
                    result["check"].append({"app": a["program"]["name"], "kind": "registry",
                                            "label": "注册表", "target": "",
                                            "expected": len(trees), "written": written,
                                            "missing": ["%s\\%s" % (t["hive"], t["path"]) for t in trees[:0]],
                                            "skipped": skipped_reg, "reg_errors": len(reg_errors)})

            if include.get("shortcuts"):
                items = []
                tmp = tempfile.mkdtemp(prefix="sm_lnk_")
                for s in a.get("shortcuts", []):
                    try:
                        base = {"user": known_folder(0x10) if s["kind"] == "desktop" else known_folder(0x02),
                                "all": known_folder(0x19) if s["kind"] == "desktop" else known_folder(0x17)}.get(s["scope"], "")
                        if not base:
                            continue
                        dst = os.path.join(base, s["rel"])
                        os.makedirs(os.path.dirname(dst), exist_ok=True)
                        blob = zf.read(s["arc"])
                        with open(os.path.join(tmp, "x.lnk"), "wb") as f:
                            f.write(blob)
                        try:
                            shutil.copy2(os.path.join(tmp, "x.lnk"), dst)
                        except PermissionError:
                            base2 = known_folder(0x02) if s["kind"] == "programs" else known_folder(0x10)
                            if not base2:
                                raise
                            dst = os.path.join(base2, s["rel"])
                            os.makedirs(os.path.dirname(dst), exist_ok=True)
                            shutil.copy2(os.path.join(tmp, "x.lnk"), dst)
                        target = _repl_str(s.get("target") or "", pairs)
                        if not target or not os.path.isfile(target):
                            ent = a.get("entry_exe") or ""
                            cand = os.path.join(tgt, ent) if ent else ""
                            target = cand if cand and os.path.isfile(cand) else (s.get("target") or "")
                        items.append({"lnk": dst, "target": target,
                                      "args": _repl_str(s.get("args") or "", pairs),
                                      "workdir": _repl_str(s.get("workdir") or "", pairs) or tgt,
                                      "icon": _repl_str(s.get("icon") or "", pairs),
                                      "desc": s.get("desc") or a["program"]["name"]})
                    except Exception as e:
                        result["errors"].append("快捷方式失败：%s" % e)
                if items:
                    if ps_run({"mode": "create", "items": items}) is None:
                        result["errors"].append("[%s] 快捷方式写入失败（系统 PowerShell 不可用）" % a["program"]["name"])
                    else:
                        result["notes"].append("[%s] 已重建 %d 个快捷方式" % (a["program"]["name"], len(items)))
                shutil.rmtree(tmp, ignore_errors=True)

            if include.get("desktop"):
                entry = a.get("entry_exe") or ""
                exe = os.path.join(tgt, entry) if entry else ""
                if not exe or not os.path.isfile(exe):
                    try:
                        cands = [f for f in os.listdir(lp(tgt)) if f.lower().endswith(".exe")]
                    except Exception:
                        cands = []
                    cands.sort(key=lambda f: os.path.getsize(os.path.join(tgt, f)), reverse=True)
                    exe = os.path.join(tgt, cands[0]) if cands else ""
                if exe and os.path.isfile(exe):
                    lnk = os.path.join(known_folder(0x10), safe_name(a["program"]["name"]) + ".lnk")
                    if ps_run({"mode": "create", "items": [{"lnk": lnk, "target": exe, "args": "",
                                                              "workdir": tgt, "icon": exe + ",0",
                                                              "desc": a["program"]["name"]}]}) is None:
                        result["notes"].append("[%s] 桌面图标未生成（PowerShell 不可用），可直接双击 %s"
                                               % (a["program"]["name"], exe))
                    else:
                        result["notes"].append("[%s] 桌面已建快捷方式" % a["program"]["name"])
                    a["_launcher"] = exe

            result["apps"].append(a)
            result["targets"][key] = tgt

        for i, ex in enumerate(man.get("extras") or [], 1):
            pre = "extras/%d/" % i
            dstbase = ex["path"]
            cnt = 0
            skip_n = 0
            miss_x = []
            exp_x = len([n for n in names if n.startswith(pre) and not n.endswith("/")])
            try:
                os.makedirs(lp(dstbase), exist_ok=True)
            except Exception:
                pass
            for n in names:
                if not n.startswith(pre):
                    continue
                if n.endswith("/"):
                    rel = n[len(pre):].rstrip("/")
                    if rel:
                        try:
                            os.makedirs(lp(os.path.join(dstbase, rel.replace("/", os.sep))), exist_ok=True)
                        except Exception:
                            pass
                    continue
                dst = os.path.join(dstbase, n[len(pre):].replace("/", os.sep))
                _make_writable(dst)
                try:
                    os.makedirs(lp(os.path.dirname(dst)), exist_ok=True)
                    with zf.open(n) as fr, open(lp(dst), "wb") as fw:
                        shutil.copyfileobj(fr, fw, 1024 * 512)
                    cnt += 1
                except Exception as e:
                    if is_lockish(dst) or is_busy_error(e):
                        result["skipped"].append(dst)
                        skip_n += 1
                    else:
                        result["errors"].append("附加目录还原失败：%s" % e)
                        miss_x.append(n[len(pre):])
            if cnt:
                result["notes"].append("附加目录已还原：%s（%d 个文件）" % (dstbase, cnt))
            result["check"].append({"app": "附加目录", "kind": "extra", "label": dstbase,
                                    "target": dstbase, "expected": exp_x, "written": cnt,
                                    "missing": miss_x[:12], "skipped": skip_n})

        if mismatch:
            result["notes"].append("有 %d 个文件校验不一致（可能被占用）：%s" % (len(mismatch), "、".join(mismatch[:5])))
            result["ok"] = False
        if result["errors"]:
            result["ok"] = False
        if progress:
            progress(1, 1)
    return result


# ---------------- 还原后自检 ----------------


def _count_files_fast(path, limit=20000, budget=6.0):
    """数文件个数和总体积：超大目录（几十 GB）只数到 limit 或时间用完就返回，避免自检卡住。"""
    if os.path.isfile(path):
        try:
            return 1, os.path.getsize(path), False
        except Exception:
            return 0, 0, False
    n = 0
    size = 0
    t0 = time.time()
    stack = [path]
    while stack:
        d = stack.pop()
        try:
            with os.scandir(d) as it:
                for e in it:
                    try:
                        if e.is_dir(follow_symlinks=False):
                            stack.append(e.path)
                        elif e.is_file(follow_symlinks=False):
                            n += 1
                            size += e.stat(follow_symlinks=False).st_size
                            if n >= limit:
                                return n, size, True
                    except Exception:
                        pass
        except Exception:
            pass
        if time.time() - t0 > budget:
            return n, size, True
    return n, size, False


def _try_launch(exe, workdir, wait=5.0):
    """试启动一次（最多看 wait 秒），还在跑就关掉，只记录结果，不弹任何窗口。"""
    out = {"state": "skip", "msg": "未试启动", "secs": 0.0, "exe": exe or ""}
    if not exe or not os.path.isfile(exe):
        out.update(state="fail", msg="找不到主程序（包里没记录或没还原程序文件）")
        return out
    flags = 0x08000000 if os.name == "nt" else 0  # CREATE_NO_WINDOW
    try:
        proc = subprocess.Popen([exe], cwd=workdir or os.path.dirname(exe), close_fds=True,
                                creationflags=flags)
    except Exception as e:
        out.update(state="fail", msg="启动失败：%s" % e)
        return out
    t0 = time.time()
    code = None
    while time.time() - t0 < wait:
        code = proc.poll()
        if code is not None:
            break
        time.sleep(0.2)
    secs = time.time() - t0
    out["secs"] = secs
    if code is None:
        try:
            proc.terminate()
            try:
                proc.wait(timeout=2)
            except Exception:
                proc.kill()
        except Exception:
            pass
        out.update(state="ok", msg="能启动（运行 %.1f 秒后由自检自动关闭）" % secs)
    elif code == 0:
        out.update(state="warn", msg="启动器 %.1f 秒返回（代码 0），多半是单实例转发或商店版启动器，主界面请双击桌面图标确认" % secs)
    else:
        out.update(state="fail", msg="启动即退出，代码 %s（多半缺运行库/依赖）" % code)
    return out


def selfcheck_restore(pkg_path, res, launch=True, save_dir=""):
    """还原完成后逐项核对并写报告，返回 {"text", "path", "stat"}。"""
    now = datetime.now()
    check = res.get("check") or []
    apps = res.get("apps") or []
    targets = res.get("targets") or {}
    stat = {"apps": len(apps), "items": 0, "ok": 0, "lack": 0, "gone": 0,
            "miss_files": 0, "skip": len(res.get("skipped") or []),
            "launch_ok": 0, "launch_bad": 0}
    by_app = {}
    for c in check:
        by_app.setdefault(c["app"], []).append(c)

    launch_res = {}
    if launch:
        for a in apps:
            nm = a["program"]["name"]
            tgt = targets.get(a["key"], "")
            exe = a.get("_launcher") or ""
            if not exe:
                ent = a.get("entry_exe") or ""
                if ent and tgt:
                    exe = os.path.join(tgt, ent)
            if exe and os.path.isfile(exe):
                launch_res[nm] = _try_launch(exe, tgt)

    def fmt(n):
        return "{:,}".format(int(n or 0))

    lines = []
    lines.append("软件迁移助手 v%s · 迁移后自检报告" % APP_VER)
    lines.append("生成时间：%s" % now.strftime("%Y-%m-%d %H:%M:%S"))
    lines.append("迁移包：%s" % (pkg_path or "（未知）"))
    lines.append("=" * 66)

    for a in apps:
        nm = a["program"]["name"]
        ver = (a["program"].get("version") or "").strip()
        lines.append("")
        lines.append("■ %s%s" % (nm, ("  v" + ver) if ver else ""))
        for c in by_app.get(nm, []):
            stat["items"] += 1
            if c["kind"] == "registry":
                okn = c.get("written") or 0
                skipn = c.get("skipped") or 0
                errn = c.get("reg_errors") or 0
                if errn:
                    stat["lack"] += 1
                    mark = "⚠"
                elif okn:
                    stat["ok"] += 1
                    mark = "✔"
                elif skipn:
                    stat["lack"] += 1
                    mark = "⚠"
                else:
                    stat["lack"] += 1
                    mark = "⚠"
                txt = "已写入 %d/%d 项" % (okn, c.get("expected") or 0)
                if skipn:
                    txt += "，%d 项要管理员权限已跳过" % skipn
                if errn:
                    txt += "，%d 项失败" % errn
                lines.append("   %s 注册表 · %s" % (mark, txt))
                continue
            tgtp = c.get("target") or ""
            exists = os.path.exists(tgtp)
            cnt, size, trunc = _count_files_fast(tgtp) if exists else (0, 0, False)
            exp = c.get("expected") or 0
            miss = c.get("missing") or []
            skipn = c.get("skipped") or 0
            if not exists:
                state = "gone"
            elif miss or (exp and not trunc and cnt < exp):
                state = "lack"
            else:
                state = "ok"
            stat[state] += 1
            if state == "gone":
                mark = "✘"
                desc = "目录不存在" + ("（包里 %s 个文件）" % fmt(exp) if exp else "")
            elif state == "lack":
                mark = "⚠"
                desc = "应有 %s 个，实到 %s 个" % (fmt(exp), fmt(cnt))
                if miss:
                    desc += "，缺 %d 个" % len(miss)
                    stat["miss_files"] += len(miss)
            else:
                mark = "✔"
                desc = "%s 个文件" % fmt(cnt)
                if size:
                    desc += " / %s" % human_size(size)
                if trunc:
                    desc += "（数到上限就停了，目录很大）"
            lines.append("   %s %s · %s" % (mark, c.get("label") or "", desc))
            if tgtp:
                lines.append("      %s" % tgtp)
            if skipn:
                lines.append("      （跳过 %d 个运行中软件占用的锁文件，正常）" % skipn)
            if miss:
                lines.append("      缺：%s%s" % ("、".join(miss[:6]), " 等 %d 个" % len(miss) if len(miss) > 6 else ""))
        lr = launch_res.get(nm)
        if launch:
            if lr:
                if lr["state"] == "ok":
                    stat["launch_ok"] += 1
                    mark = "✔"
                elif lr["state"] == "warn":
                    stat["launch_ok"] += 1
                    mark = "⚠"
                else:
                    stat["launch_bad"] += 1
                    mark = "✘"
                lines.append("   %s 试启动 · %s" % (mark, lr["msg"]))
            else:
                lines.append("   · 试启动 · 跳过（没有可启动主程序）")

    if not apps:
        lines.append("")
        lines.append("（本次没有还原任何软件）")

    lines.append("")
    lines.append("=" * 66)
    lines.append("合计：%d 个软件 / %d 个目录项 · 完整 %d · 有缺 %d · 未还原 %d · 缺失文件 %d · 跳过锁文件 %d"
                 % (stat["apps"], stat["items"], stat["ok"], stat["lack"], stat["gone"],
                    stat["miss_files"], stat["skip"]))
    if launch:
        lines.append("试启动：%d 个有响应 · %d 个报错" % (stat["launch_ok"], stat["launch_bad"]))
    lines.append("")
    lines.append("【工具边界（这些不在迁移范围，换机后要自己补）】")
    lines.append("· 服务 / 驱动 / 计划任务 / 开机自启")
    lines.append("· 微软商店应用的完整程序（只带了 LocalCache 数据，程序需重装）")
    lines.append("· 机器码绑定的授权、加密狗、需要重新登录的账号态")
    lines.append("· VC++ / .NET / Java / Node 等运行库版本不一致时要另装")
    lines.append("· 注册表中的安装记录（卸载项、文件关联、协议注册）")
    if res.get("errors"):
        lines.append("")
        lines.append("【未成功的项（%d 处，详见日志）】" % len(res["errors"]))
        for e in res["errors"][:20]:
            lines.append("· " + e)

    text = "\n".join(lines) + "\n"
    if not save_dir:
        cand = known_folder(0x10) or ""
        save_dir = cand if cand and os.path.isdir(cand) else tempfile.gettempdir()
    path = ""
    try:
        os.makedirs(save_dir, exist_ok=True)
        path = os.path.join(save_dir, "迁移自检报告_%s.txt" % now.strftime("%Y%m%d_%H%M%S"))
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
    except Exception as e:
        path = ""
        text += "\n（报告保存失败：%s）\n" % e
    return {"text": text, "path": path, "stat": stat, "launch": launch_res}


# ---------------- 命令行自检 ----------------


def selftest(names, outdir):
    print("[1] 扫描已安装软件…")
    progs = list_programs(include_system=True)
    picked = []
    for n in names:
        for p in progs:
            if n.lower() in p["name"].lower():
                picked.append(p)
                break
    if not picked:
        print("没找到:", names)
        return 1
    infos = []
    for p in picked:
        print("[2] 分析:", p["name"])
        infos.append(analyze(p, log=lambda m: print("   " + m)))
    out = os.path.join(outdir, "迁移包_test.zip")
    print("[3] 导出 ->", out)
    t0 = time.time()
    inc = {"program": True, "userdata": True, "registry": True, "shortcuts": True,
           "runtimes": True, "desktop": True}
    man, skipped = export_package(infos, out, inc, [], print, None, True, False)
    print("   用时 %.1fs，包 %s，文件 %d，跳过 %d" % (time.time() - t0, human_size(os.path.getsize(out)),
                                                 man["stats"]["files"], len(skipped)))
    print("[4] 还原到临时父目录")
    res = import_package(out, "", inc, print, None, False, os.path.join(outdir, "还原"))
    print("   ok=", res["ok"], "targets=", res["targets"])
    for n in res["notes"]:
        print("   ", n)
    for e in res["errors"][:10]:
        print("   错误:", e)
    for key, tgt in res["targets"].items():
        s, c = dir_size(tgt)
        src = [i for i in infos]
        print("   %s -> %d 个文件 %s" % (tgt, c, human_size(s)))
    return 0


# ---------------- GUI ----------------

ACCENT = "#2D6BFF"
ACCENT_DARK = "#1B4FD8"
BG = "#F5F7FB"
CARD = "#FFFFFF"
TEXT = "#1B2430"
MUTED = "#7A8798"
BORDER = "#E3E8F0"


class CheckBox(tk.Frame):
    def __init__(self, parent, text, var, on_change=None, bg=CARD):
        super().__init__(parent, bg=bg)
        self.var, self.text, self.bg, self.on_change = var, text, bg, on_change
        self.cv = tk.Canvas(self, width=15, height=15, bg=bg, highlightthickness=0, cursor="hand2")
        self.cv.pack(side="left")
        self.lbl = tk.Label(self, bg=bg, font=("Microsoft YaHei UI", 10), cursor="hand2")
        self.lbl.pack(side="left", padx=(7, 0))
        self.cv.bind("<Button-1>", self.toggle)
        self.lbl.bind("<Button-1>", self.toggle)
        self.render()

    def toggle(self, event=None):
        self.var.set(not self.var.get())
        self.render()
        if self.on_change:
            self.on_change()

    def render(self):
        on = bool(self.var.get())
        self.cv.delete("all")
        if on:
            self.cv.create_rectangle(0, 0, 14, 14, fill=ACCENT, outline=ACCENT)
            self.cv.create_line(3.5, 7.5, 6.2, 10.4, 11.2, 4.2, fill="#FFFFFF", width=2)
            self.lbl.configure(text=self.text, fg=TEXT)
        else:
            self.cv.create_rectangle(0, 0, 14, 14, fill="#FFFFFF", outline="#C3CCDA")
            self.lbl.configure(text=self.text, fg="#5E6A7B")


def set_dark_title(win):
    try:
        win.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(win.winfo_id())
        for attr in (20, 19):
            v = ctypes.c_int(1)
            if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(v), ctypes.sizeof(v)) == 0:
                break
    except Exception:
        pass


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("%s v%s" % (APP_NAME, APP_VER))
        self.geometry("1160x900")
        self.minsize(1040, 760)
        self.configure(bg=BG)
        self.programs = []
        self.filtered = []
        self.analyses = {}
        self.extras = []
        self.q = queue.PriorityQueue()
        self._seq = 0
        self.packing = False
        self._cancelling = False
        self._cancel = {"v": False}
        self.pkg_manifest = None
        self._setup_style()
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
        self._build()
        self.after(300, lambda: set_dark_title(self))
        self.after(100, self._load_programs)
        self.after(120, self._poll)

    def _setup_style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        font = ("Microsoft YaHei UI", 10)
        self.option_add("*Font", font)
        style.configure(".", font=font, background=CARD, foreground=TEXT)
        style.configure("TFrame", background=BG)
        style.configure("TLabel", background=CARD, foreground=TEXT, font=font)
        style.configure("Hint.TLabel", background=CARD, foreground=MUTED, font=("Microsoft YaHei UI", 9))
        style.configure("Val.TLabel", background=CARD, foreground=TEXT, font=("Microsoft YaHei UI", 10))
        style.configure("TButton", font=font, padding=(14, 8), relief="flat")
        style.configure("Primary.TButton", background=ACCENT, foreground="#FFFFFF",
                        font=("Microsoft YaHei UI", 10, "bold"), borderwidth=0)
        style.map("Primary.TButton", background=[("active", ACCENT_DARK), ("disabled", "#A9BFEA")])
        style.configure("Ghost.TButton", background="#EEF2FB", foreground=ACCENT, borderwidth=0)
        style.map("Ghost.TButton", background=[("active", "#E1E9FB")])
        style.configure("TEntry", fieldbackground="#FFFFFF", bordercolor=BORDER, padding=6)
        style.configure("Treeview", background="#FFFFFF", fieldbackground="#FFFFFF", rowheight=30,
                        borderwidth=0, font=font)
        style.configure("Treeview.Heading", background="#F0F3F9", foreground=MUTED, relief="flat",
                        font=("Microsoft YaHei UI", 9, "bold"))
        style.map("Treeview", background=[("selected", "#E6EDFF")], foreground=[("selected", ACCENT_DARK)])
        style.configure("Slim.Horizontal.TProgressbar", background=ACCENT, troughcolor="#EDF1F8", borderwidth=0)

    def _build(self):
        header = tk.Frame(self, bg=CARD, height=86)
        header.pack(fill="x")
        header.pack_propagate(False)
        inner = tk.Frame(header, bg=CARD)
        inner.pack(fill="both", expand=True, padx=26, pady=(16, 0))
        tk.Label(inner, text=APP_NAME, bg=CARD, fg=TEXT, font=("Microsoft YaHei UI", 19, "bold")).pack(anchor="w")
        tk.Label(inner, text="已装软件连文件、注册表、配置、存档一起打包 · 支持多选批量 · 新电脑一键还原点开即用",
                 bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(anchor="w", pady=(3, 0))

        tabbar = tk.Frame(self, bg=CARD)
        tabbar.pack(fill="x")
        self.tab_pack = tk.Label(tabbar, text="  打包导出  ", bg=CARD, fg=ACCENT,
                                 font=("Microsoft YaHei UI", 11, "bold", "underline"), cursor="hand2", padx=8, pady=9)
        self.tab_pack.pack(side="left", padx=(20, 0))
        self.tab_restore = tk.Label(tabbar, text="  还原安装  ", bg=CARD, fg=MUTED,
                                    font=("Microsoft YaHei UI", 11), cursor="hand2", padx=8, pady=9)
        self.tab_restore.pack(side="left", padx=(6, 0))
        self.tab_pack.bind("<Button-1>", lambda e: self.switch("pack"))
        self.tab_restore.bind("<Button-1>", lambda e: self.switch("restore"))
        tk.Frame(self, bg=BORDER, height=1).pack(fill="x")

        self.body = ttk.Frame(self, style="TFrame")
        self.body.pack(fill="both", expand=True, padx=22, pady=(16, 6))
        self.pack_page = self._build_pack_page(self.body)
        self.restore_page = self._build_restore_page(self.body)
        self.pack_page.pack(fill="both", expand=True)
        self.page = "pack"

    def _build_pack_page(self, parent):
        wrap = ttk.Frame(parent, style="TFrame")
        wrap.columnconfigure(0, weight=1, minsize=380)
        wrap.columnconfigure(1, weight=2)
        wrap.rowconfigure(0, weight=1)

        left = tk.Frame(wrap, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 14))
        tk.Label(left, text="已安装软件（可多选）", bg=CARD, fg=TEXT,
                 font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w", padx=14, pady=(12, 6))
        sf = tk.Frame(left, bg=CARD)
        sf.pack(fill="x", padx=12)
        self.search_var = tk.StringVar()
        ttk.Entry(sf, textvariable=self.search_var).pack(side="left", fill="x", expand=True)
        self.search_var.trace_add("write", lambda *a: self._apply_filter())
        tk.Label(left, text="搜索筛选；按住 Ctrl/Shift 多选；Ctrl+A 全选", bg=CARD, fg=MUTED,
                 font=("Microsoft YaHei UI", 9)).pack(
            anchor="w", padx=14, pady=(6, 4))

        tvf = tk.Frame(left, bg=CARD)
        tvf.pack(fill="both", expand=True, padx=8)
        self.tree = ttk.Treeview(tvf, columns=("name", "size"), show="headings", selectmode="extended")
        self.tree.heading("name", text="名称")
        self.tree.heading("size", text="大小")
        self.tree.column("name", width=260, anchor="w")
        self.tree.column("size", width=90, anchor="e", stretch=False)
        sb = ttk.Scrollbar(tvf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", lambda e: self._on_select())
        self.tree.bind("<Control-a>", self._select_all)

        btnf = tk.Frame(left, bg=CARD)
        btnf.pack(fill="x", padx=12, pady=(8, 4))
        ttk.Button(btnf, text="手动选 exe/文件夹", style="Ghost.TButton", command=self._pick_manual).grid(
            row=0, column=0, sticky="w")
        ttk.Button(btnf, text="添加额外目录", style="Ghost.TButton", command=self._add_extra).grid(
            row=0, column=1, sticky="w", padx=(8, 0))
        ttk.Button(btnf, text="扫描可能漏掉的目录", style="Ghost.TButton", command=self._find_missed).grid(
            row=1, column=0, columnspan=2, sticky="w", pady=(6, 0))
        self.count_lbl = tk.Label(left, text="正在读取…", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9))
        self.count_lbl.pack(anchor="w", padx=14, pady=(2, 2))
        tk.Label(left, text="任何软件都能迁：自动认不出的目录，用『扫描可能漏掉的目录』挑，或用『添加额外目录』手动加。",
                 bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 8), wraplength=350,
                 justify="left").pack(anchor="w", padx=14, pady=(0, 8))

        right = tk.Frame(wrap, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        right.grid(row=0, column=1, sticky="nsew")

        head = tk.Frame(right, bg=CARD)
        head.pack(fill="x", padx=20, pady=(16, 0))
        self.sel_name = tk.Label(head, text="请选择左侧软件（可多选）", bg=CARD, fg=TEXT,
                                 font=("Microsoft YaHei UI", 14, "bold"))
        self.sel_name.pack(anchor="w")
        self.sel_sub = tk.Label(head, text="选中后自动分析文件、配置、注册表、存档位置", bg=CARD, fg=MUTED,
                                font=("Microsoft YaHei UI", 9))
        self.sel_sub.pack(anchor="w", pady=(4, 0))

        info_card = tk.Frame(right, bg="#FAFBFE", highlightbackground=BORDER, highlightthickness=1)
        info_card.pack(fill="x", padx=20, pady=(14, 0))
        self.info_text = tk.Text(info_card, height=5, bg="#FAFBFE", fg=TEXT, relief="flat", wrap="word",
                                 font=("Microsoft YaHei UI", 9), padx=12, pady=10, cursor="arrow")
        info_sb = ttk.Scrollbar(info_card, orient="vertical", command=self.info_text.yview)
        self.info_text.configure(yscrollcommand=info_sb.set)
        info_sb.pack(side="right", fill="y", pady=2, padx=(0, 2))
        self.info_text.pack(side="left", fill="both", expand=True)
        self.info_text.insert("1.0", "选择左侧软件后，这里会显示：\n安装目录与文件数量、用户配置/存档位置、相关注册表项、迁移风险提示。\n\n多选时会列出每个软件的目录和体积，点『开始打包』会一起打进同一个包。")
        self.info_text.configure(state="disabled")

        opt = tk.Frame(right, bg=CARD)
        opt.pack(fill="x", padx=20, pady=(14, 0))
        tk.Label(opt, text="打包内容", bg=CARD, fg=TEXT, font=("Microsoft YaHei UI", 11, "bold")).pack(anchor="w")
        row1 = tk.Frame(opt, bg=CARD)
        row1.pack(fill="x", pady=(6, 0))
        self.var_prog = tk.BooleanVar(value=True)
        self.var_data = tk.BooleanVar(value=True)
        self.var_reg = tk.BooleanVar(value=True)
        self.var_lnk = tk.BooleanVar(value=True)
        self.var_cache = tk.BooleanVar(value=True)
        self.var_kill = tk.BooleanVar(value=True)
        for i, (txt, var) in enumerate((("程序文件（全部）", self.var_prog),
                                        ("用户配置与存档（全部目录）", self.var_data),
                                        ("注册表项", self.var_reg),
                                        ("快捷方式", self.var_lnk),
                                        ("缓存文件也一起打包（推荐）", self.var_cache),
                                        ("自动退出应用占用进程（推荐）", self.var_kill))):
            CheckBox(row1, txt, var).grid(row=i // 2, column=i % 2, sticky="w", padx=(0, 26), pady=2)
        tk.Label(opt, text="默认整份带走（缓存/日志/更新包都在内）。『缓存文件』可取消；『自动退出应用占用进程』会先列出该软件的运行进程，确认后结束，避免文件被占用跳过（Word/Excel 未保存内容请先自己保存）。",
                 bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9), wraplength=560, justify="left").pack(anchor="w", pady=(4, 0))

        out_row = tk.Frame(right, bg=CARD)
        out_row.pack(fill="x", padx=20, pady=(12, 0))
        tk.Label(out_row, text="保存到", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(side="left")
        self.out_var = tk.StringVar(value=self._default_out())
        ttk.Entry(out_row, textvariable=self.out_var).pack(side="left", fill="x", expand=True, padx=8)
        ttk.Button(out_row, text="浏览", style="Ghost.TButton", command=self._browse_out).pack(side="left")

        self.pack_btn = ttk.Button(right, text="开始打包", style="Primary.TButton", command=self._do_pack)
        self.pack_btn.pack(fill="x", padx=20, pady=(12, 0))
        self.pack_bar = ttk.Progressbar(right, style="Slim.Horizontal.TProgressbar", maximum=100)
        self.pack_bar.pack(fill="x", padx=20, pady=(10, 0))
        # 简洁滚动日志：只留关键节点，自动滚到最新
        self.brief_box = tk.Text(right, height=3, bg="#F6F8FC", fg="#334155", relief="flat",
                                 wrap="word", font=("Consolas", 8), padx=8, pady=6,
                                 cursor="arrow", highlightthickness=0)
        self.brief_box.pack(fill="x", padx=20, pady=(6, 0))
        self.brief_box.insert("1.0", "开始打包后，这里会滚显示：当前在打包什么、进度百分比、已写多少。")
        self.brief_box.configure(state="disabled")
        self.pack_log = tk.Text(right, height=5, bg="#FFFFFF", fg=MUTED, relief="flat", wrap="word",
                                font=("Consolas", 9), padx=2, pady=6, cursor="arrow")
        self.pack_log.pack(fill="both", expand=True, padx=20, pady=(8, 14))
        self.pack_log.insert("1.0", "详细日志会显示在这里。选择软件 → 点『开始打包』。")
        self.pack_log.configure(state="disabled")
        return wrap

    def _build_restore_page(self, parent):
        wrap = tk.Frame(parent, bg=CARD, highlightbackground=BORDER, highlightthickness=1)
        top = tk.Frame(wrap, bg=CARD)
        top.pack(fill="x", padx=24, pady=(18, 0))
        tk.Label(top, text="还原安装", bg=CARD, fg=TEXT, font=("Microsoft YaHei UI", 14, "bold")).pack(anchor="w")
        tk.Label(top, text="选择迁移包，设置安装位置，一键还原（包里的多个软件会一起还原）",
                 bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(anchor="w", pady=(4, 0))

        pk = tk.Frame(wrap, bg=CARD)
        pk.pack(fill="x", padx=24, pady=(16, 0))
        ttk.Button(pk, text="选择迁移包", style="Ghost.TButton", command=self._pick_pkg).pack(side="left")
        self.pkg_var = tk.StringVar(value="未选择")
        ttk.Label(pk, textvariable=self.pkg_var, style="Val.TLabel").pack(side="left", padx=10)

        rwrap = tk.Frame(wrap, bg="#FAFBFE", highlightbackground=BORDER, highlightthickness=1)
        rwrap.pack(fill="both", expand=True, padx=24, pady=(14, 0))
        self.restore_info = tk.Text(rwrap, height=8, bg="#FAFBFE", fg=TEXT, relief="flat", wrap="word",
                                    font=("Microsoft YaHei UI", 9), padx=14, pady=10, cursor="arrow",
                                    highlightthickness=0)
        r_sb = ttk.Scrollbar(rwrap, orient="vertical", command=self.restore_info.yview)
        self.restore_info.configure(yscrollcommand=r_sb.set)
        r_sb.pack(side="right", fill="y", pady=2, padx=(0, 2))
        self.restore_info.pack(side="left", fill="both", expand=True)
        self.restore_info.insert("1.0", "还没有选择迁移包。\n点『选择迁移包』选中 .zip 后，这里会列出包里有哪些软件、各自装到哪里。")
        self.restore_info.configure(state="disabled")

        tg = tk.Frame(wrap, bg=CARD)
        tg.pack(fill="x", padx=24, pady=(14, 0))
        tk.Label(tg, text="统一父目录", bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(side="left")
        self.parent_var = tk.StringVar()
        ttk.Entry(tg, textvariable=self.parent_var).pack(side="left", fill="x", expand=True, padx=8)
        ttk.Button(tg, text="浏览", style="Ghost.TButton", command=self._browse_parent).pack(side="left")
        tk.Label(wrap, text="留空 = 还原到每个软件原来的路径；填了就统一装到该目录下各自的文件夹（如 D:\\Apps）",
                 bg=CARD, fg=MUTED, font=("Microsoft YaHei UI", 9)).pack(anchor="w", padx=24, pady=(6, 0))

        opt = tk.Frame(wrap, bg=CARD)
        opt.pack(fill="x", padx=24, pady=(12, 0))
        self.r_prog = tk.BooleanVar(value=True)
        self.r_data = tk.BooleanVar(value=True)
        self.r_reg = tk.BooleanVar(value=True)
        self.r_lnk = tk.BooleanVar(value=True)
        self.r_desk = tk.BooleanVar(value=True)
        self.r_port = tk.BooleanVar(value=False)
        self.r_kill = tk.BooleanVar(value=True)
        self.r_check = tk.BooleanVar(value=True)
        for i, (txt, var) in enumerate((("还原程序文件", self.r_prog), ("还原配置/存档", self.r_data),
                                        ("写入注册表", self.r_reg), ("重建快捷方式", self.r_lnk),
                                        ("桌面生成启动图标", self.r_desk), ("便携模式（不写注册表）", self.r_port),
                                        ("还原前结束占用进程（可覆盖锁定文件）", self.r_kill),
                                        ("还原后自检（核对目录 + 试启动 5 秒）", self.r_check))):
            CheckBox(opt, txt, var).grid(row=i // 3, column=i % 3, sticky="w", padx=(0, 22), pady=2)

        act = tk.Frame(wrap, bg=CARD)
        act.pack(fill="x", padx=24, pady=(14, 0))
        self.restore_btn = ttk.Button(act, text="开始还原", style="Primary.TButton", command=self._do_restore)
        self.restore_btn.pack(side="left")
        if not is_admin():
            ttk.Button(act, text="以管理员身份重启", style="Ghost.TButton", command=self._elevate).pack(side="left", padx=10)
            tk.Label(act, text="（还原 HKLM 注册表 / 装到系统目录时需要管理员）", bg=CARD, fg=MUTED,
                     font=("Microsoft YaHei UI", 9)).pack(side="left")

        self.restore_bar = ttk.Progressbar(wrap, style="Slim.Horizontal.TProgressbar", maximum=100)
        self.restore_log = tk.Text(wrap, bg="#FFFFFF", fg=MUTED, relief="flat", wrap="word",
                                   font=("Consolas", 9), padx=2, pady=6, cursor="arrow")
        self.restore_log.pack(fill="both", expand=True, padx=24, pady=(10, 18))
        self.restore_log.insert("1.0", "日志会显示在这里。选择迁移包 → 点『开始还原』。")
        self.restore_log.configure(state="disabled")
        return wrap

    # ---------- 公共 ----------
    def _default_out(self):
        p = os.path.join(os.path.expanduser("~"), "Desktop")
        return p if os.path.isdir(p) else os.path.expanduser("~")

    def switch(self, page):
        self.page = page
        if page == "pack":
            self.restore_page.pack_forget()
            self.pack_page.pack(fill="both", expand=True)
            self.tab_pack.configure(fg=ACCENT, font=("Microsoft YaHei UI", 11, "bold", "underline"))
            self.tab_restore.configure(fg=MUTED, font=("Microsoft YaHei UI", 11))
        else:
            self.pack_page.pack_forget()
            self.restore_page.pack(fill="both", expand=True)
            self.tab_restore.configure(fg=ACCENT, font=("Microsoft YaHei UI", 11, "bold", "underline"))
            self.tab_pack.configure(fg=MUTED, font=("Microsoft YaHei UI", 11))

    def push(self, kind, *args):
        self._seq += 1
        self.q.put((self._seq, (kind,) + args))

    def _poll(self):
        try:
            while True:
                _, item = self.q.get_nowait()
                kind = item[0]
                if kind == "log":
                    box = item[1]
                    box.configure(state="normal")
                    box.insert("end", item[2] + "\n")
                    box.see("end")
                    box.configure(state="disabled")
                elif kind == "prog":
                    item[1]["value"] = item[2]
                elif kind == "brief":
                    self._brief_append(item[1])
                elif kind == "brief_clear":
                    self._brief_clear(item[1])
                elif kind == "programs":
                    self._fill_tree(item[1])
                elif kind == "select":
                    self._render_selection()
                elif kind == "done_pack":
                    self._pack_done(*item[1:])
                elif kind == "done_restore":
                    self._restore_done(*item[1:])
                elif kind == "ask_kill":
                    self._ask_kill(item[1], item[2])
                elif kind == "ask_kill_restore":
                    self._ask_kill_restore(item[1], item[2])
                elif kind == "missed":
                    self._show_missed(item[1])
        except queue.Empty:
            pass
        self.after(120, self._poll)

    def _ask_kill(self, procs, holder):
        """在界面线程弹确认框，后台线程等结果（避免界面卡死）"""
        try:
            names = sorted({("%s.exe" % (p.get("name") or "?")) for p in procs})
            ans = messagebox.askyesno(
                "结束运行中的进程",
                "检测到这些进程正在运行（共 %d 个）：\n\n%s\n\n是否现在结束它们？\n"
                "选『是』= 自动结束，打包不再跳过被占用文件；\n"
                "选『否』= 保持运行，被占用的文件会跳过打包。" % (
                    len(procs), "、".join(names[:10]) + ("…" if len(names) > 10 else "")))
            holder["ans"] = bool(ans)
        except Exception:
            holder["ans"] = False
        finally:
            holder["ev"].set()

    def _ask_kill_restore(self, procs, holder):
        try:
            names = sorted({("%s.exe" % (p.get("name") or "?")) for p in procs})
            ans = messagebox.askyesno(
                "还原前结束占用进程",
                "检测到这些进程正在运行（共 %d 个）：\n\n%s\n\n是否先结束它们，再覆盖写入？\n"
                "选『是』= 结束进程 → 被锁定的配置/存档会被覆盖，还原最完整；\n"
                "选『否』= 保持运行 → 被占用的文件跳过，不报错。\n\n"
                "注意：如果要还原的正是你正在使用的，结束后当前对话会断开，还原会自动继续跑完。"
                % (len(procs), "、".join(names[:10]) + ("…" if len(names) > 10 else "")))
            holder["ans"] = bool(ans)
        except Exception:
            holder["ans"] = False
        finally:
            holder["ev"].set()

    def log(self, box, msg):
        self.push("log", box, msg)

    def brief(self, msg):
        self.push("brief", msg)

    def brief_clear(self, msg=""):
        self.push("brief_clear", msg)

    def _brief_clear(self, msg=""):
        self.brief_box.configure(state="normal")
        self.brief_box.delete("1.0", "end")
        if msg:
            self.brief_box.insert("1.0", msg + "\n")
        self.brief_box.configure(state="disabled")

    def _brief_append(self, msg):
        self.brief_box.configure(state="normal")
        self.brief_box.insert("end", "%s  %s\n" % (datetime.now().strftime("%H:%M:%S"), msg))
        lines = int(self.brief_box.index("end-1c").split(".")[0])
        if lines > 120:
            self.brief_box.delete("1.0", "%d.0" % (lines - 120))
        self.brief_box.see("end")
        self.brief_box.configure(state="disabled")

    def progress(self, box, pct):
        # 收尾（写说明书、清单、关闭压缩包）还没跑完之前，条永远不满
        try:
            pct = max(0.0, min(99.0, float(pct)))
        except Exception:
            pct = 0.0
        self.push("prog", box, pct)

    def _set_text(self, box, txt):
        box.configure(state="normal")
        box.delete("1.0", "end")
        box.insert("1.0", txt)
        box.configure(state="disabled")

    # ---------- 列表 ----------
    def _load_programs(self):
        def work():
            try:
                progs = list_programs()
            except Exception as e:
                progs = []
                self.log(self.pack_log, "读取软件列表失败：%s" % e)
            self.push("programs", progs)
        threading.Thread(target=work, daemon=True).start()

    def _fill_tree(self, progs):
        self.programs = progs
        self._apply_filter()

    def _apply_filter(self):
        kw = (self.search_var.get() or "").strip().lower()
        self.filtered = [p for p in self.programs if kw in p["name"].lower()] if kw else list(self.programs)
        self.tree.delete(*self.tree.get_children())
        for i, p in enumerate(self.filtered):
            self.tree.insert("", "end", iid=str(i), values=(p["name"], human_size(p["size"]) if p["size"] else "—"))
        self.count_lbl.configure(text="共 %d 个已安装软件" % len(self.filtered))

    def _select_all(self, event=None):
        self.tree.selection_set(self.tree.get_children())
        return "break"

    def _current_progs(self):
        sel = self.tree.selection()
        return [self.filtered[int(i)] for i in sel if int(i) < len(self.filtered)]

    def _on_select(self):
        progs = self._current_progs()
        if not progs:
            return
        # 换软件就清掉上一次打包的进度和摘要，避免"已完成的满进度条"一直挂在那
        if not getattr(self, "packing", False):
            try:
                self.pack_bar["value"] = 0
                if self.pack_bar.winfo_ismapped():
                    self.pack_bar.pack_forget()
            except Exception:
                pass
            self.brief_clear("")
            self._set_text(self.pack_log, "")
            self.brief("已选择 %s，点『开始打包』开始。" % ("、".join(p["name"] for p in progs[:3]) +
                                                     (" 等 %d 个" % len(progs) if len(progs) > 3 else "")))
        if len(progs) == 1:
            self.sel_name.configure(text=progs[0]["name"])
            self.sel_sub.configure(text="版本 %s · %s" % (progs[0]["version"] or "未知",
                                                         progs[0]["publisher"] or "未知发布者"))
        else:
            self.sel_name.configure(text="已选 %d 个软件" % len(progs))
            self.sel_sub.configure(text="将一起打进同一个迁移包")
        self._set_text(self.info_text, "正在分析…")
        if not getattr(self, "packing", False):
            self.pack_btn.configure(state="disabled")

        def work():
            for p in progs:
                if p["name"] not in self.analyses:
                    try:
                        self.analyses[p["name"]] = analyze(p)
                    except Exception:
                        self.analyses[p["name"]] = None
            self.push("select")
        threading.Thread(target=work, daemon=True).start()

    def _render_selection(self):
        progs = self._current_progs()
        if not progs:
            return
        lines = []
        tsize = tdata = 0
        tfiles = 0
        for p in progs:
            info = self.analyses.get(p["name"])
            if not info or not info["install_dir"]:
                if info and info.get("component"):
                    lines.append("· %s：驱动 / 运行库 / 系统组件，不需要迁移（新电脑直接装一次即可），可跳过。" % p["name"])
                else:
                    lines.append("· %s：没找到安装目录，请用『手动选』指定。" % p["name"])
                continue
            tsize += info["size"]
            tdata += info["data_size"]
            tfiles += info["file_count"]
            kind_cn = {"roaming": "漫游", "local": "本地", "locallow": "低权限", "programdata": "公共",
                       "documents": "文档", "userprofile": "用户目录", "mydocuments": "我的文档",
                       "publicdocuments": "公共文档", "public": "公共目录",
                       "desktop": "桌面", "savedgames": "存档", "sibling": "安装目录旁",
                       "drive": "磁盘根目录",
                       "registry": "注册表记录", "manual": "手动补充"}
            lines.append("· %s  %s" % (p["name"], info["program"].get("version") or ""))
            lines.append("   [程序本体] %s   %d 个文件 / %s" % (
                info["install_dir"], info["file_count"], human_size(info["size"])))
            lines.append("      里面是：%s" % (info.get("install_desc") or "软件本体"))
            if len(progs) == 1:
                if info["entry_exes"]:
                    lines.append("      主程序：%s" % "、".join(info["entry_exes"][:3]))
            lines.append("   相关目录 %d 处，合计 %s（全部打包）" % (
                len(info["data_dirs"]), human_size(info["data_size"])))
            for d in info["data_dirs"]:
                tag = kind_cn.get(d.get("kind", ""), d.get("kind", ""))
                lines.append("   [%s] %s   %d 个文件 / %s%s" % (
                    tag, d["path"], d.get("count", 0), human_size(d.get("size", 0)),
                    "　（缓存）" if d.get("cache") else ""))
                lines.append("      里面是：%s" % (d.get("desc") or "该软件的用户数据"))
            if len(progs) == 1:
                if info["reg_keys"]:
                    lines.append("   注册表：%s" % "、".join("%s\\%s" % (k["hive"], k["path"])
                                                              for k in info["reg_keys"][:4]))
                for w in info["warnings"][:3]:
                    lines.append("   ⚠ " + w)
        lines.append("")
        lines.append("合计：%d 个软件，程序文件 %d 个 / %s，配置存档 %s" % (
            len(progs), tfiles, human_size(tsize), human_size(tdata)))
        if self.extras:
            lines.append("附加目录：%s" % "、".join(self.extras))
        self._set_text(self.info_text, "\n".join(lines))
        # 打包/停止过程中不要把按钮抢成别的状态（否则会丢掉『取消打包』）
        if not getattr(self, "packing", False):
            self.pack_btn.configure(state="normal")

    # ---------- 手工添加 ----------
    def _pick_manual(self):
        choice = messagebox.askyesnocancel("手动选择", "是（Yes）= 选择 exe 文件\n否（No）= 选择整个文件夹")
        if choice is None:
            return
        if choice:
            p = filedialog.askopenfilename(title="选择软件主程序",
                                           filetypes=[("程序", "*.exe"), ("所有文件", "*.*")])
            if not p:
                return
            d = os.path.dirname(p)
            prog = {"name": os.path.splitext(os.path.basename(p))[0], "version": "", "publisher": "",
                    "install_location": d, "hive": "", "reg_path": "", "size": 0}
        else:
            d = filedialog.askdirectory(title="选择软件安装文件夹")
            if not d:
                return
            prog = {"name": os.path.basename(d.rstrip("\\")), "version": "", "publisher": "",
                    "install_location": d, "hive": "", "reg_path": "", "size": 0}
        self.filtered.append(prog)
        iid = str(len(self.filtered) - 1)
        self.tree.insert("", "end", iid=iid, values=(prog["name"], "—"))
        self.tree.selection_set(iid)
        self._on_select()

    def _add_extra(self):
        d = filedialog.askdirectory(title="选择要一并带走的额外目录（会还原到同样的路径）")
        if not d:
            return
        if d not in self.extras:
            self.extras.append(d)
        self._render_selection()

    def _browse_out(self):
        d = filedialog.askdirectory(title="选择保存位置", initialdir=self.out_var.get())
        if d:
            self.out_var.set(d)

    # ---------- 扫描漏掉的目录 ----------
    def _find_missed(self):
        progs = self._current_progs()
        if not progs:
            messagebox.showwarning("提示", "请先在左侧选择一个软件，再点『扫描可能漏掉的目录』。")
            return
        if getattr(self, "missed_busy", False):
            return
        self.missed_busy = True
        self.brief("正在扫描可能漏掉的目录（%d 个软件）…" % len(progs))

        def work():
            items = []
            for p in progs[:4]:
                info = self.analyses.get(p["name"])
                if not info or not info.get("install_dir"):
                    continue
                known = [d["path"] for d in info.get("data_dirs", [])] + [info["install_dir"]]
                try:
                    got = suggest_missing_dirs(p, info["install_dir"], known)
                except Exception:
                    got = []
                for g in got:
                    g["prog"] = p["name"]
                    items.append(g)
            self.push("missed", items)

        threading.Thread(target=work, daemon=True).start()

    def _show_missed(self, items):
        self.missed_busy = False
        if not items:
            messagebox.showinfo("扫描完成",
                                "没有发现可能漏掉的目录。\n\n"
                                "如果还知道别的目录，用『添加额外目录』手动加进来即可（会还原到原路径）。")
            return
        win = tk.Toplevel(self)
        win.title("可能漏掉的目录（勾选后加入本次打包）")
        win.geometry("900x500")
        win.transient(self)
        tk.Label(win, text="这些目录的名字或内容和你选的软件比较接近，但没被自动认出来。"
                           "按住 Ctrl/Shift 多选，点『加入打包』会一起带走，还原回原来的位置。",
                 font=("Microsoft YaHei UI", 9), fg=MUTED, justify="left",
                 wraplength=860).pack(anchor="w", padx=14, pady=(12, 6))
        tvf = tk.Frame(win)
        tvf.pack(fill="both", expand=True, padx=14)
        tv = ttk.Treeview(tvf, columns=("prog", "path", "score", "size"), show="headings",
                          selectmode="extended")
        tv.heading("prog", text="软件")
        tv.heading("path", text="目录")
        tv.heading("score", text="像的程度")
        tv.heading("size", text="体积")
        tv.column("prog", width=140, anchor="w", stretch=False)
        tv.column("path", width=520, anchor="w")
        tv.column("score", width=90, anchor="center", stretch=False)
        tv.column("size", width=90, anchor="e", stretch=False)
        sb = ttk.Scrollbar(tvf, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb.set)
        tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        for i, it in enumerate(items):
            tv.insert("", "end", iid=str(i), values=(it["prog"], it["path"],
                                                     "%d%%" % int(it["score"] * 100),
                                                     human_size(it["size"])))

        bar = tk.Frame(win)
        bar.pack(fill="x", padx=14, pady=(10, 12))

        def do_add():
            sel = tv.selection()
            if not sel:
                messagebox.showinfo("提示", "请先选中要加入的目录。", parent=win)
                return
            added = 0
            for i in sel:
                it = items[int(i)]
                info = self.analyses.get(it["prog"])
                if not info:
                    continue
                paths = {os.path.abspath(d["path"]).lower() for d in info.get("data_dirs", []) if d.get("path")}
                if os.path.abspath(it["path"]).lower() in paths:
                    continue
                info["data_dirs"].append({
                    "kind": "manual", "path": it["path"], "name": it["name"],
                    "rel": os.path.basename(it["path"].rstrip("\\")),
                    "size": it["size"], "count": it["count"], "cache": False,
                    "desc": "手动补充的目录（扫描没自动认出、已确认属于这个软件）—— 一起带走，还原回原位"})
                info["data_size"] = info.get("data_size", 0) + it["size"]
                info["data_count"] = info.get("data_count", 0) + it["count"]
                added += 1
            win.destroy()
            self._render_selection()
            self.brief("已补充 %d 个目录进包。" % added)

        ttk.Button(bar, text="全部选中", style="Ghost.TButton",
                   command=lambda: tv.selection_set(tv.get_children())).pack(side="left")
        ttk.Button(bar, text="加入打包", style="Primary.TButton", command=do_add).pack(side="right")
        ttk.Button(bar, text="关闭", style="Ghost.TButton", command=win.destroy).pack(side="right", padx=8)

    # ---------- 打包 ----------
    def _do_pack(self):
        if getattr(self, "packing", False):
            self._cancel_pack()
            return
        progs = self._current_progs()
        if not progs:
            messagebox.showwarning("提示", "请先在左侧选择软件。")
            return
        infos = []
        for p in progs:
            info = self.analyses.get(p["name"])
            if info and info["install_dir"]:
                infos.append(info)
        if not infos:
            messagebox.showwarning("提示",
                                    "所选软件里没有可打包的程序文件。\n\n"
                                    "如果选的是驱动 / 运行库 / 系统组件（如 Intel Chipset、.NET、VC++ 运行库），"
                                    "这类不需要迁移，新电脑直接装一次即可；\n"
                                    "如果是普通软件，请点『手动选 exe/文件夹』指定它的安装位置。")
            return
        outdir = self.out_var.get()
        if not os.path.isdir(outdir):
            messagebox.showwarning("提示", "保存位置不存在。")
            return
        name = (safe_name(infos[0]["program"]["name"]) + PKG_EXT) if len(infos) == 1 else \
            ("迁移包_%d个软件_%s.zip" % (len(infos), datetime.now().strftime("%m%d_%H%M")))
        out = os.path.join(outdir, name)
        if os.path.exists(out) and not messagebox.askyesno("已存在", "%s 已存在，是否覆盖？" % name):
            return
        include = {"program": self.var_prog.get(), "userdata": self.var_data.get(),
                   "registry": self.var_reg.get(), "shortcuts": self.var_lnk.get(),
                   "cache": self.var_cache.get(),
                   "runtimes": True, "desktop": True}
        skip_cache = not self.var_cache.get()

        # 界面先进入「打包中」状态，检测进程/结束进程/打包一起放到后台线程，避免界面假死
        self.packing = True
        self._cancelling = False
        self._cancel = {"v": False}
        self.pack_btn.configure(state="normal", text="取消打包")
        if not self.pack_bar.winfo_ismapped():
            self.pack_bar.pack(fill="x", padx=20, pady=(10, 0), before=self.pack_log)
        self.pack_bar["value"] = 0
        self._set_text(self.pack_log, "")
        self.brief_clear("")
        self.brief("开始打包：%s" % "、".join(i["program"]["name"] for i in infos))
        self.brief("缓存文件：%s" % ("一起打包" if self.var_cache.get() else "跳过纯缓存目录"))
        self.log(self.pack_log, "开始打包：%s" % "、".join(i["program"]["name"] for i in infos))
        self.log(self.pack_log, "  缓存文件：%s" % ("一起打包（完整原样）" if self.var_cache.get() else "跳过 Cache/Log 等纯缓存目录（体积更小）"))
        self.log(self.pack_log, "  提示：打包中点『取消打包』可随时中止，已生成的不完整包会自动删除。")

        extras = [{"path": e} for e in self.extras]
        kill_on = self.var_kill.get()

        def ask_kill(procs):
            holder = {"ans": False, "ev": threading.Event()}
            self.push("ask_kill", procs, holder)
            holder["ev"].wait(900)
            return holder["ans"]

        def work():
            t0 = time.time()
            try:
                if kill_on:
                    procs = list_app_processes_multi([i.get("install_dir") for i in infos])
                    if _aborted(self._cancel):
                        raise PackAbort()
                    if procs:
                        if ask_kill(procs):
                            killed = kill_app_processes(procs)
                            time.sleep(0.8)
                            self.log(self.pack_log, "  已结束进程：%s" % "、".join(sorted(set(killed))[:10]))
                        else:
                            self.log(self.pack_log, "  保持运行，被占用文件可能跳过")
                    else:
                        self.log(self.pack_log, "  没有检测到该软件的运行进程")
                else:
                    self.log(self.pack_log, "  未勾选自动退出，若软件在运行会有文件被跳过")

                def prog(cur, tot):
                    if tot:
                        self.progress(self.pack_bar, min(100, cur * 100.0 / tot))
                man, skipped = export_package(infos, out, include, extras,
                                              log=lambda m: self.log(self.pack_log, m),
                                              progress=prog, with_hash=True, skip_cache=skip_cache,
                                              fast=False, cancel=self._cancel,
                                              brief=lambda m: self.brief(m))
                self.push("done_pack", man, skipped, out, time.time() - t0, None)
            except PackAbort:
                try:
                    if os.path.isfile(out):
                        os.remove(out)
                except Exception:
                    pass
                self.push("done_pack", None, [], out, time.time() - t0, "__CANCEL__")
            except Exception as e:
                self.push("done_pack", None, [], out, time.time() - t0, str(e))
        threading.Thread(target=work, daemon=True).start()

    def _cancel_pack(self):
        if not getattr(self, "packing", False) or getattr(self, "_cancelling", False):
            return
        self._cancelling = True
        try:
            self._cancel["v"] = True
        except Exception:
            pass
        self.pack_btn.configure(state="disabled", text="正在停止…")
        self.brief("正在取消打包…")
        self.log(self.pack_log, "正在取消打包，等当前文件写完就停（大文件最多几秒）…")

    def _pack_done(self, man, skipped, out, secs, err):
        self.packing = False
        self._cancelling = False
        self.pack_btn.configure(state="normal", text="开始打包")
        if err == "__CANCEL__":
            self.pack_bar["value"] = 0
            self.brief("已取消打包（%.1f 秒），未完成的包已删除" % secs)
            self.log(self.pack_log, "已取消打包（用时 %.1f 秒），未完成的包已删除。" % secs)
            return
        if err:
            self.pack_bar["value"] = 0
            self.brief("打包失败：%s" % err)
            self.log(self.pack_log, "✗ 打包失败：%s" % err)
            messagebox.showerror("打包失败", err)
            return
        self.pack_bar["value"] = 100
        self.brief("完成：%s（%s），用时 %.1f 秒" % (os.path.basename(out), human_size(os.path.getsize(out)), secs))
        self.log(self.pack_log, "✓ 完成，用时 %.1f 秒" % secs)
        self.log(self.pack_log, "  文件：%s（%s）" % (os.path.basename(out), human_size(os.path.getsize(out))))
        self.log(self.pack_log, "  软件：%d 个 / 文件 %d 个" % (len(man["apps"]), man["stats"]["files"]))
        if skipped:
            self.log(self.pack_log, "  跳过 %d 个被占用/无权限的文件（关闭软件后重打包更完整）" % len(skipped))
        for e in (man.get("errors") or [])[:5]:
            self.log(self.pack_log, "  注意：%s" % e)
        self.log(self.pack_log, "  包内已含《安装说明.txt》与《安装说明.html》，双击 zip 就能看到，不会解压也可以直接用浏览器打开 html。")
        messagebox.showinfo("打包完成",
                            "已生成：\n%s\n\n大小 %s，%d 个软件 / %d 个文件。\n\n拷到新电脑，用本工具『还原安装』即可；没工具时双击 zip 也能看说明并手工还原。"
                            % (out, human_size(os.path.getsize(out)), len(man["apps"]), man["stats"]["files"]))

    # ---------- 还原 ----------
    def _pick_pkg(self):
        p = filedialog.askopenfilename(title="选择迁移包",
                                       filetypes=[("迁移包", "*.zip *.smig"), ("所有文件", "*.*")])
        if not p:
            return
        self.pkg_var.set(p)
        try:
            with zipfile.ZipFile(p, "r") as zf:
                man = _adapt_manifest(json.loads(zf.read(MANIFEST_NAME).decode("utf-8")))
        except Exception as e:
            self._set_text(self.restore_info, "读取失败：不是有效的迁移包（%s）" % e)
            return
        self.pkg_manifest = man
        lines = ["包内软件 %d 个　源电脑：%s　打包时间：%s" % (
            len(man["apps"]), man.get("source_computer", ""), man.get("created", "")), ""]
        for i, a in enumerate(man["apps"], 1):
            lines.append("%d) %s  %s" % (i, a["program"]["name"], a["program"].get("version") or ""))
            lines.append("   原路径：%s" % (a.get("original_install_dir") or "未记录"))
            lines.append("   文件 %d 个 / %s　目录 %d 处　注册表 %d 项" % (
                a.get("stats", {}).get("files", 0), human_size(a.get("stats", {}).get("bytes", 0)),
                len(a.get("data_dirs") or []), len(a.get("reg_keys") or [])))
            for d in (a.get("data_dirs") or []):
                lines.append("   · %s" % d.get("orig_path", ""))
                lines.append("     %s" % (d.get("desc") or "该软件的用户数据"))
            for w in (a.get("warnings") or [])[:2]:
                lines.append("   ⚠ " + w)
        if man.get("extras"):
            lines.append("")
            lines.append("额外附带目录：%s" % "、".join(e["path"] for e in man["extras"]))
        if not is_admin():
            lines.append("")
            lines.append("提示：当前不是管理员，HKLM 注册表会跳过。")
        self._set_text(self.restore_info, "\n".join(lines))
        self.restore_btn.configure(state="normal")

    def _browse_parent(self):
        d = filedialog.askdirectory(title="选择统一安装父目录")
        if d:
            self.parent_var.set(d)

    def _do_restore(self):
        pkg = self.pkg_var.get()
        if not pkg or not os.path.isfile(pkg):
            messagebox.showwarning("提示", "请先选择迁移包。")
            return
        parent = self.parent_var.get().strip()
        if parent:
            try:
                os.makedirs(parent, exist_ok=True)
                probe = os.path.join(parent, ".sm_write_test")
                with open(probe, "w") as f:
                    f.write("ok")
                os.remove(probe)
            except Exception as e:
                messagebox.showerror("无权限", "无法写入 %s：\n%s\n\n换个目录（如 D:\\Apps）或用管理员运行。" % (parent, e))
                return
        include = {"program": self.r_prog.get(), "userdata": self.r_data.get(),
                   "registry": self.r_reg.get() and not self.r_port.get(),
                   "shortcuts": self.r_lnk.get(), "desktop": self.r_desk.get()}
        self.restore_btn.configure(state="disabled", text="还原中…")
        if not self.restore_bar.winfo_ismapped():
            self.restore_bar.pack(fill="x", padx=24, pady=(12, 0), before=self.restore_log)
        self.restore_bar["value"] = 0
        self._set_text(self.restore_log, "")
        self.log(self.restore_log, "开始还原…")
        portable = self.r_port.get()
        kill_on = self.r_kill.get()
        do_check = self.r_check.get()
        dirs = []
        try:
            with zipfile.ZipFile(pkg, "r") as zf:
                man = _adapt_manifest(json.loads(zf.read(MANIFEST_NAME).decode("utf-8")))
            for a in man.get("apps", []):
                d = a.get("original_install_dir") or ""
                if d:
                    dirs.append(d)
        except Exception:
            pass

        def work():
            def prog(cur, tot):
                if tot:
                    self.progress(self.restore_bar, min(100, cur * 100.0 / tot))
            try:
                if kill_on and dirs:
                    procs = list_app_processes_multi(dirs)
                    if procs:
                        holder = {"ans": False, "ev": threading.Event()}
                        self.push("ask_kill_restore", procs, holder)
                        holder["ev"].wait(900)
                        if holder["ans"]:
                            killed = kill_app_processes(procs)
                            time.sleep(1.2)
                            self.log(self.restore_log, "已结束进程：%s（继续还原并覆盖锁定文件）"
                                     % "、".join(sorted(set(killed))[:10]))
                        else:
                            self.log(self.restore_log, "保持运行，被占用/锁定的文件会跳过")
                res = import_package(pkg, "", include, progress=prog, portable=portable, parent_dir=parent)
                rep = None
                if do_check:
                    self.log(self.restore_log, "开始自检：逐项核对目录，并各试启动一次…")
                    try:
                        rep = selfcheck_restore(pkg, res, launch=True)
                    except Exception as e:
                        self.log(self.restore_log, "自检失败（不影响已还原的文件）：%s" % e)
                self.push("done_restore", res, None, rep)
            except Exception as e:
                self.push("done_restore", None, str(e))
        threading.Thread(target=work, daemon=True).start()

    def _restore_done(self, res, err, rep=None):
        self.restore_btn.configure(state="normal", text="开始还原")
        if err:
            self.restore_bar["value"] = 0
            self.log(self.restore_log, "✗ 还原失败：%s" % err)
            messagebox.showerror("还原失败", err)
            return
        self.restore_bar["value"] = 100
        for n in res.get("notes", []):
            self.log(self.restore_log, "· " + n)
        for e in res.get("errors", [])[:40]:
            self.log(self.restore_log, "✗ " + e)
        skipped = res.get("skipped") or []
        if skipped:
            self.log(self.restore_log, "· %d 个被占用/锁定的文件已跳过（运行中的软件会锁着它们，不影响使用）"
                     % len(skipped))
        if res.get("ok"):
            self.log(self.restore_log, "✓ 还原完成，桌面已有快捷方式，双击即用。")
        else:
            self.log(self.restore_log, "⚠ 完成但有 %d 处问题，见日志。" % len(res.get("errors", [])))
        if rep:
            st = rep.get("stat") or {}
            self.log(self.restore_log, "✓ 自检：完整 %d · 有缺 %d · 未还原 %d · 缺失文件 %d → %s"
                     % (st.get("ok", 0), st.get("lack", 0), st.get("gone", 0),
                        st.get("miss_files", 0), rep.get("path") or "（报告保存失败）"))
            self._show_report(rep, res)
            return
        if res.get("ok"):
            msg = "还原完成！\n\n"
            for k, t in res.get("targets", {}).items():
                msg += "· %s\n" % t
            msg += "\n桌面已生成启动快捷方式，点开即用。"
            if skipped:
                msg += "\n\n另有 %d 个被运行中软件锁定的文件已跳过（多为 .lock 锁文件），不影响使用。" % len(skipped)
            messagebox.showinfo("还原完成", msg)
        else:
            messagebox.showwarning("部分完成", "还原基本完成，但有 %d 处问题：\n\n%s" % (
                len(res.get("errors", [])), "\n".join(res.get("errors", [])[:8])))

    def _show_report(self, rep, res=None):
        top = tk.Toplevel(self)
        top.title("迁移自检报告 v%s" % APP_VER)
        top.configure(bg=CARD)
        try:
            top.geometry("900x640")
        except Exception:
            pass
        st = rep.get("stat") or {}
        head = "完整 %d 项 · 有缺 %d 项 · 未还原 %d 项" % (st.get("ok", 0), st.get("lack", 0), st.get("gone", 0))
        if st.get("skip"):
            head += " · 跳过锁文件 %d" % st.get("skip")
        tk.Label(top, text="还原完成，已生成自检报告", bg=CARD, fg=TEXT,
                 font=("Microsoft YaHei UI", 13, "bold")).pack(anchor="w", padx=20, pady=(16, 2))
        tk.Label(top, text=head, bg=CARD, fg=MUTED,
                 font=("Microsoft YaHei UI", 9)).pack(anchor="w", padx=20)
        box = tk.Frame(top, bg="#FAFBFE", highlightbackground=BORDER, highlightthickness=1)
        box.pack(fill="both", expand=True, padx=20, pady=(10, 10))
        txt = tk.Text(box, bg="#FAFBFE", fg=TEXT, relief="flat", wrap="word",
                      font=("Consolas", 9), padx=10, pady=8, highlightthickness=0)
        sb = ttk.Scrollbar(box, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        txt.pack(side="left", fill="both", expand=True)
        txt.insert("1.0", rep.get("text") or "")
        txt.configure(state="disabled")
        bar = tk.Frame(top, bg=CARD)
        bar.pack(fill="x", padx=20, pady=(0, 16))

        def open_report():
            p = rep.get("path") or ""
            if not p or not os.path.isfile(p):
                messagebox.showwarning("提示", "报告文件没保存成功，可先『复制全文』。", parent=top)
                return
            try:
                os.startfile(p)
            except Exception as e:
                messagebox.showwarning("提示", "打不开报告：%s" % e, parent=top)

        def copy_all():
            try:
                self.clipboard_clear()
                self.clipboard_append(rep.get("text") or "")
                messagebox.showinfo("已复制", "自检报告全文已复制到剪贴板。", parent=top)
            except Exception:
                pass

        ttk.Button(bar, text="打开报告文件", style="Primary.TButton", command=open_report).pack(side="left")
        ttk.Button(bar, text="复制全文", style="Ghost.TButton", command=copy_all).pack(side="left", padx=8)
        ttk.Button(bar, text="关闭", style="Ghost.TButton", command=top.destroy).pack(side="right")
        if rep.get("path"):
            tk.Label(bar, text=rep["path"], bg=CARD, fg=MUTED,
                     font=("Microsoft YaHei UI", 8)).pack(side="left", padx=10)
        top.transient(self)
        top.lift()
        try:
            top.grab_set()
        except Exception:
            pass

    def _elevate(self):
        try:
            params = " ".join(['"%s"' % a for a in sys.argv[1:]])
            ctypes.windll.shell32.ShellExecuteW(None, "runas", sys.executable, params, None, 1)
            self.destroy()
        except Exception as e:
            messagebox.showerror("失败", "无法提升权限：%s" % e)


def main():
    if "--selftest" in sys.argv:
        idx = sys.argv.index("--selftest")
        outdir = tempfile.mkdtemp(prefix="sm_test_")
        names = []
        for a in sys.argv[idx + 1:]:
            if os.path.isdir(a):
                outdir = a
            else:
                names.append(a)
        return selftest(names or ["7-Zip"], outdir)
    app = App()
    app.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main() or 0)

