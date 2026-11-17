// ==WindhawkMod==
// @id              simple-wallpaper-switcher
// @name            Simple Wallpaper Switcher
// @description     A compact folder-based wallpaper picker with a tray icon and global hotkey
// @version         0.1.0
// @author          Hendrik Heitlager
// @include         windhawk.exe
// @compilerOptions -DWIN32_LEAN_AND_MEAN -lole32 -loleaut32 -lruntimeobject -lshell32 -lcomctl32 -lshlwapi -luuid -ldwmapi -luxtheme -lgdi32 -lmsimg32 -ld2d1 -lwindowscodecs
// @license         GPL-3.0
// ==/WindhawkMod==

// Derived from the wallpaper-switching feature in Mac Island & Dock by
// caliberda (GPL-3.0). This standalone first cut keeps folder browsing,
// sorted image selection, next/previous cycling, per-monitor targeting,
// and the separate Windhawk tool-process model. This version adds a dark
// thumbnail picker, window fade, and a standalone port of the source
// wallpaper transition renderer (WIC/Direct2D overlay and wallpaper handoff).

// ==WindhawkModReadme==
/*
# Simple Wallpaper Switcher

This is an independent Windhawk tool mod for choosing wallpapers from one
folder. Toggle the compact picker with the recorded hotkey (Ctrl+Alt+W by
default), or open it from the notification-area icon. Record the shortcut in
Windhawk settings.
Click a thumbnail to apply it; scroll over the grid to turn pages.
Click outside the picker to dismiss it. The wheel wraps between pages;
arrow keys move the highlighted image and Enter or Space applies it. The tray
menu also offers next/previous image actions.

The image is applied to the monitor under the pointer. The folder is stored
in the mod's settings and images are ordered the same way as Explorer.

The picker uses a Catppuccin Mocha palette, a paged thumbnail grid with
rounded corners, and a brief fade when opening or closing. It opens centered
on the monitor under the pointer. Wallpaper changes use Windows'
IDesktopWallpaper API with the selected transition mode, including Random,
which avoids repeating the previous effect.
The tray icon uses the Segoe Fluent Icons wallpaper glyph. The derived code
remains GPL-3.0 and credits the original feature author.
*/
// ==/WindhawkModReadme==

// ==WindhawkModSettings==
/*
- wallpaperFolder: ""
  $name: Wallpaper folder
  $description: Folder containing your wallpaper images
- wallpaperTransition: random
  $name: Wallpaper transition
  $description: Effect used when a wallpaper changes
  $options:
  - random: Random (avoid repeating the previous effect)
  - fade: Fade
  - circle: Circle
  - slide: Slide
  - zoom: Zoom
- toggleHotkey: "ctrl+alt+87"
  $name: Open picker hotkey
  $description: Click to record a shortcut. If it cannot be registered, Ctrl+Alt+W is tried as a fallback. Leave empty to disable the hotkey.
  $format: hotkey
*/
// ==/WindhawkModSettings==

#include <windows.h>
#include <commctrl.h>
#include <dwmapi.h>
#include <d2d1.h>
#include <dxgi.h>
#include <propsys.h>
#include <wincodec.h>
#include <shlobj.h>
#include <shobjidl.h>
#include <shlwapi.h>
#include <shellapi.h>
#include <uxtheme.h>
#include <windhawk_api.h>
#include <windhawk_tool_mod.h>
#include <winrt/base.h>

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <cwchar>
#include <memory>
#include <random>
#include <string>
#include <vector>

namespace {

constexpr UINT kTrayCallback = WM_APP + 1;
constexpr UINT kChooseFolder = 1003;
constexpr UINT kFolderLabelId = 3001;
constexpr UINT kPageLabelId = 3002;
constexpr UINT kTrayOpen = 2001;
constexpr UINT kTrayPrevious = 2002;
constexpr UINT kTrayNext = 2003;
constexpr UINT kTrayExit = 2004;
constexpr UINT kHotkeyId = 1;
constexpr UINT kReloadSettings = WM_APP + 10;
constexpr UINT kWallpaperChangeDone = WM_APP + 11;
constexpr UINT kFirstTileId = 4000;
constexpr size_t kImageLimit = 300;
constexpr size_t kPageSize = 12;
constexpr size_t kGridColumns = 4;
constexpr UINT kThumbnailWidth = 128;
constexpr UINT kThumbnailHeight = 76;
constexpr PCWSTR kWindowClass = L"SimpleWallpaperSwitcherWindow";

constexpr COLORREF kBackground = RGB(48, 45, 71);  // Popup #302D47
constexpr COLORREF kSurface = RGB(68, 64, 90);     // Raised surface
constexpr COLORREF kText = RGB(205, 214, 244);     // Text #CDD6F4
constexpr COLORREF kMuted = RGB(166, 173, 200);    // Subtext1 #A6ADC8
constexpr COLORREF kAccent = RGB(207, 161, 255);   // Mauve #CFA1FF
constexpr COLORREF kBorder = RGB(88, 83, 111);     // Border #58536F

HWND g_hostWindow;
HWND g_pickerWindow;
HWND g_tiles[kPageSize];
HWND g_folderLabel;
HWND g_pageLabel;
HWND g_folderButton;
HANDLE g_uiThread;
DWORD g_uiThreadId;
HANDLE g_readyEvent;
UINT g_hotkeyModifiers = MOD_CONTROL | MOD_ALT;
UINT g_hotkeyKey = 'W';
std::wstring g_folder;
std::vector<std::wstring> g_images;
HBITMAP g_thumbnails[kPageSize]{};
size_t g_page;
int g_currentImage = -1;
int g_selectedImage = -1;
HBRUSH g_backgroundBrush;
HFONT g_pickerFont;
HICON g_trayIcon;
HANDLE g_wallpaperThread;
bool g_transitionActive;
int g_transitionMode = 4;  // Random
int g_lastRandomTransition = -1;
std::wstring g_transitionPath;
std::atomic<bool> g_shuttingDown{false};

enum class WallpaperTransition { Fade, Circle, Slide, Zoom };
NOTIFYICONDATA g_notifyIcon{};

std::wstring ReadStringSetting(PCWSTR name, size_t capacity = 2048) {
    std::wstring value(capacity, L'\0');
    if (!Wh_GetStringValue(name, value.data(), (DWORD)value.size())) {
        return {};
    }
    value.resize(wcsnlen(value.c_str(), value.size()));
    return value;
}

void LoadHotkeySetting() {
    PCWSTR setting = Wh_GetStringSetting(L"toggleHotkey");
    const std::wstring value = setting ? setting : L"ctrl+alt+87";
    if (setting) {
        Wh_FreeStringSetting(setting);
    }

    g_hotkeyModifiers = 0;
    g_hotkeyKey = 0;
    bool valid = true;
    bool keySeen = false;
    size_t start = 0;
    while (start < value.size()) {
        const size_t separator = value.find(L'+', start);
        const size_t end = separator == std::wstring::npos
                               ? value.size()
                               : separator;
        const std::wstring token = value.substr(start, end - start);
        if (_wcsicmp(token.c_str(), L"ctrl") == 0 && !keySeen) {
            g_hotkeyModifiers |= MOD_CONTROL;
        } else if (_wcsicmp(token.c_str(), L"alt") == 0 && !keySeen) {
            g_hotkeyModifiers |= MOD_ALT;
        } else if (_wcsicmp(token.c_str(), L"shift") == 0 && !keySeen) {
            g_hotkeyModifiers |= MOD_SHIFT;
        } else if (_wcsicmp(token.c_str(), L"win") == 0 && !keySeen) {
            g_hotkeyModifiers |= MOD_WIN;
        } else {
            wchar_t* parsedEnd = nullptr;
            const unsigned long key = std::wcstoul(token.c_str(), &parsedEnd, 10);
            if (keySeen || token.empty() || parsedEnd == token.c_str() ||
                !parsedEnd || *parsedEnd != L'\0' || key == 0 || key > 255) {
                valid = false;
                break;
            }
            g_hotkeyKey = (UINT)key;
            keySeen = true;
        }

        if (separator == std::wstring::npos) {
            break;
        }
        start = separator + 1;
    }

    if (!valid || (!value.empty() && !keySeen)) {
        Wh_Log(L"Invalid toggleHotkey setting; using Ctrl+Alt+W");
        g_hotkeyModifiers = MOD_CONTROL | MOD_ALT;
        g_hotkeyKey = 'W';
    }
}

bool RegisterPickerHotkey(HWND hwnd) {
    UnregisterHotKey(hwnd, kHotkeyId);
    if (g_hotkeyKey == 0) {
        return true;
    }
    if (RegisterHotKey(hwnd, kHotkeyId,
                       g_hotkeyModifiers | MOD_NOREPEAT,
                       g_hotkeyKey)) {
        return true;
    }

    const DWORD error = GetLastError();
    constexpr UINT fallbackModifiers = MOD_CONTROL | MOD_ALT;
    constexpr UINT fallbackKey = 'W';
    if (g_hotkeyModifiers == fallbackModifiers &&
        g_hotkeyKey == fallbackKey) {
        return false;
    }

    Wh_Log(L"Configured hotkey registration failed (error %lu); trying Ctrl+Alt+W fallback",
           error);
    if (RegisterHotKey(hwnd, kHotkeyId,
                       fallbackModifiers | MOD_NOREPEAT,
                       fallbackKey)) {
        return true;
    }
    Wh_Log(L"Ctrl+Alt+W fallback registration also failed (error %lu)",
           GetLastError());
    return false;
}

void LoadSettings() {
    g_folder = ReadStringSetting(L"wallpaperFolder");
    LoadHotkeySetting();
    const std::wstring transition = ReadStringSetting(L"wallpaperTransition");
    if (transition.empty() || _wcsicmp(transition.c_str(), L"random") == 0) {
        g_transitionMode = 4;
    } else if (_wcsicmp(transition.c_str(), L"fade") == 0) {
        g_transitionMode = 0;
    } else if (_wcsicmp(transition.c_str(), L"circle") == 0) {
        g_transitionMode = 1;
    } else if (_wcsicmp(transition.c_str(), L"slide") == 0) {
        g_transitionMode = 2;
    } else if (_wcsicmp(transition.c_str(), L"zoom") == 0) {
        g_transitionMode = 3;
    } else {
        g_transitionMode = 4;
    }
}

bool IsImageFile(PCWSTR filename) {
    static constexpr PCWSTR extensions[] = {
        L".jpg", L".jpeg", L".jfif", L".png", L".bmp", L".webp"};
    PCWSTR extension = PathFindExtension(filename);
    for (PCWSTR candidate : extensions) {
        if (_wcsicmp(extension, candidate) == 0) {
            return true;
        }
    }
    return false;
}

void ListImages() {
    g_images.clear();
    if (g_folder.empty()) {
        return;
    }

    std::wstring pattern = g_folder;
    if (pattern.back() != L'\\' && pattern.back() != L'/') {
        pattern += L'\\';
    }
    pattern += L'*';

    WIN32_FIND_DATAW data{};
    HANDLE find = FindFirstFileExW(pattern.c_str(), FindExInfoBasic, &data,
                                   FindExSearchNameMatch, nullptr,
                                   FIND_FIRST_EX_LARGE_FETCH);
    if (find == INVALID_HANDLE_VALUE) {
        return;
    }

    const size_t prefixLength = pattern.size() - 1;
    do {
        if (!(data.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) &&
            IsImageFile(data.cFileName)) {
            g_images.emplace_back(pattern.substr(0, prefixLength) +
                                  data.cFileName);
        }
    } while (g_images.size() < kImageLimit && FindNextFileW(find, &data));
    FindClose(find);

    std::sort(g_images.begin(), g_images.end(), [](const auto& a, const auto& b) {
        return StrCmpLogicalW(PathFindFileNameW(a.c_str()),
                              PathFindFileNameW(b.c_str())) < 0;
    });
}

void PersistFolder() {
    Wh_SetStringValue(L"wallpaperFolder", g_folder.c_str());
}

void UpdateFolderLabel() {
    if (!g_folderLabel) {
        return;
    }
    std::wstring name = g_folder;
    while (name.size() > 3 &&
           (name.back() == L'\\' || name.back() == L'/')) {
        name.pop_back();
    }
    if (!name.empty()) {
        name = PathFindFileNameW(name.c_str());
    }
    const std::wstring label = g_folder.empty()
                                   ? L"Choose a wallpaper folder"
                                   : name;
    SetWindowTextW(g_folderLabel, label.c_str());
}

void UpdatePageLabel() {
    if (!g_pageLabel) {
        return;
    }
    const size_t pages = (g_images.size() + kPageSize - 1) / kPageSize;
    std::wstring label;
    if (g_images.empty()) {
        label = L"0 / 0   \x00B7   Scroll to turn pages";
    } else {
        label = std::to_wstring(g_page + 1) + L" / " +
                std::to_wstring(pages) + L"   \x00B7   Scroll to turn pages";
    }
    SetWindowTextW(g_pageLabel, label.c_str());
}

void DestroyThumbnails() {
    for (HBITMAP& bitmap : g_thumbnails) {
        if (bitmap) {
            DeleteObject(bitmap);
            bitmap = nullptr;
        }
    }
}

void RefreshList() {
    if (!g_tiles[0]) {
        return;
    }
    g_page = std::min(g_page, g_images.empty()
                                  ? size_t(0)
                                  : (g_images.size() - 1) / kPageSize);
    DestroyThumbnails();

    const size_t first = g_page * kPageSize;
    const HRESULT com = CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    for (size_t slot = 0; slot < kPageSize; ++slot) {
        const size_t i = first + slot;
        if (i < g_images.size()) {
            winrt::com_ptr<IShellItemImageFactory> factory;
            if (SUCCEEDED(SHCreateItemFromParsingName(
                    g_images[i].c_str(), nullptr,
                    IID_PPV_ARGS(factory.put())))) {
                const SIZE size{(LONG)kThumbnailWidth,
                                (LONG)kThumbnailHeight};
                factory->GetImage(size, SIIGBF_RESIZETOFIT, &g_thumbnails[slot]);
            }
        }
        if (g_tiles[slot]) {
            ShowWindow(g_tiles[slot], i < g_images.size() ? SW_SHOW : SW_HIDE);
            InvalidateRect(g_tiles[slot], nullptr, TRUE);
        }
    }
    if (SUCCEEDED(com)) {
        CoUninitialize();
    }
    UpdateFolderLabel();
    UpdatePageLabel();
}

bool PickFolder(HWND owner, std::wstring* result) {
    const HRESULT com = CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    winrt::com_ptr<IFileDialog> dialog;
    bool picked = false;
    if (SUCCEEDED(CoCreateInstance(CLSID_FileOpenDialog, nullptr,
                                   CLSCTX_INPROC_SERVER,
                                   IID_PPV_ARGS(dialog.put())))) {
        DWORD options = 0;
        dialog->GetOptions(&options);
        dialog->SetOptions(options | FOS_PICKFOLDERS | FOS_FORCEFILESYSTEM);
        dialog->SetTitle(L"Choose your wallpaper folder");
        winrt::com_ptr<IShellItem> item;
        PWSTR path = nullptr;
        if (SUCCEEDED(dialog->Show(owner)) &&
            SUCCEEDED(dialog->GetResult(item.put())) &&
            SUCCEEDED(item->GetDisplayName(SIGDN_FILESYSPATH, &path))) {
            *result = path;
            CoTaskMemFree(path);
            picked = true;
        }
    }
    dialog = nullptr;
    if (SUCCEEDED(com)) {
        CoUninitialize();
    }
    return picked;
}

WICRect WallpaperCut(UINT scaledWidth,
                     UINT scaledHeight,
                     SIZE size,
                     DESKTOP_WALLPAPER_POSITION position) {
    const UINT shownWidth = std::min<UINT>(scaledWidth, size.cx);
    const UINT shownHeight = std::min<UINT>(scaledHeight, size.cy);
    const bool fills = position == DWPOS_FILL || position == DWPOS_SPAN;
    return {(INT)(scaledWidth - shownWidth) / 2,
            (INT)std::lround((scaledHeight - shownHeight) /
                             (fills ? 3.0 : 2.0)),
            (INT)shownWidth, (INT)shownHeight};
}

// The picture as Windows will show it on a monitor of `size`, by its
// wallpaper position: cut to fill it ("Fill"; "Span" too, set for one
// monitor as here), whole inside it ("Fit"), stretched, or at its own size
// in the middle ("Center", "Tile"); turned as the photo says (its EXIF
// orientation). `place` gets where it goes on the monitor.
winrt::com_ptr<IWICBitmapSource> LoadWallpaperPicture(
    IWICImagingFactory* wic,
    PCWSTR path,
    SIZE size,
    DESKTOP_WALLPAPER_POSITION position,
    D2D1_RECT_F* place) {
    winrt::com_ptr<IWICBitmapDecoder> decoder;
    winrt::com_ptr<IWICBitmapFrameDecode> frame;
    if (FAILED(wic->CreateDecoderFromFilename(path, nullptr, GENERIC_READ,
                                              WICDecodeMetadataCacheOnDemand,
                                              decoder.put())) ||
        FAILED(decoder->GetFrame(0, frame.put()))) {
        return nullptr;
    }
    winrt::com_ptr<IWICBitmapSource> source = frame.as<IWICBitmapSource>();
    // Turned as the camera says (JPEG's EXIF orientation).
    winrt::com_ptr<IWICMetadataQueryReader> metadata;
    PROPVARIANT value;
    PropVariantInit(&value);
    if (SUCCEEDED(frame->GetMetadataQueryReader(metadata.put())) &&
        SUCCEEDED(metadata->GetMetadataByName(L"/app1/ifd/{ushort=274}",
                                              &value)) &&
        value.vt == VT_UI2) {
        const WICBitmapTransformOptions turn =
            value.uiVal == 3   ? WICBitmapTransformRotate180
            : value.uiVal == 6 ? WICBitmapTransformRotate90
            : value.uiVal == 8 ? WICBitmapTransformRotate270
                               : WICBitmapTransformRotate0;
        winrt::com_ptr<IWICBitmapFlipRotator> rotator;
        if (turn != WICBitmapTransformRotate0 &&
            SUCCEEDED(wic->CreateBitmapFlipRotator(rotator.put())) &&
            SUCCEEDED(rotator->Initialize(source.get(), turn))) {
            source = rotator.as<IWICBitmapSource>();
        }
    }
    PropVariantClear(&value);
    UINT width = 0, height = 0;
    if (FAILED(source->GetSize(&width, &height)) || !width || !height) {
        return nullptr;
    }
    const double fill = std::max((double)size.cx / width,
                                 (double)size.cy / height);
    const double fit = std::min((double)size.cx / width,
                                (double)size.cy / height);
    UINT scaledWidth = width, scaledHeight = height;
    switch (position) {
        case DWPOS_FIT:
            scaledWidth = std::max<UINT>(1, (UINT)std::lround(width * fit));
            scaledHeight = std::max<UINT>(1, (UINT)std::lround(height * fit));
            break;
        case DWPOS_STRETCH:
            scaledWidth = size.cx;
            scaledHeight = size.cy;
            break;
        case DWPOS_CENTER:
        case DWPOS_TILE:
            break;
        default:
            scaledWidth =
                std::max<UINT>(size.cx, (UINT)std::ceil(width * fill));
            scaledHeight =
                std::max<UINT>(size.cy, (UINT)std::ceil(height * fill));
            break;
    }
    const WICRect crop =
        WallpaperCut(scaledWidth, scaledHeight, size, position);
    const UINT shownWidth = crop.Width;
    const UINT shownHeight = crop.Height;
    winrt::com_ptr<IWICBitmapScaler> scaler;
    winrt::com_ptr<IWICBitmapClipper> clipper;
    winrt::com_ptr<IWICFormatConverter> converter;
    if (FAILED(wic->CreateBitmapScaler(scaler.put())) ||
        FAILED(scaler->Initialize(source.get(), scaledWidth, scaledHeight,
                                  WICBitmapInterpolationModeFant)) ||
        FAILED(wic->CreateBitmapClipper(clipper.put())) ||
        FAILED(clipper->Initialize(scaler.get(), &crop)) ||
        FAILED(wic->CreateFormatConverter(converter.put())) ||
        FAILED(converter->Initialize(clipper.get(),
                                     GUID_WICPixelFormat32bppPBGRA,
                                     WICBitmapDitherTypeNone, nullptr, 0,
                                     WICBitmapPaletteTypeMedianCut))) {
        return nullptr;
    }
    const float left = (size.cx - (float)shownWidth) / 2;
    const float top = (size.cy - (float)shownHeight) / 2;
    *place = {left, top, left + shownWidth, top + shownHeight};
    return converter.as<IWICBitmapSource>();
}

constexpr int kScreenSampleWidth = 48;
constexpr int kScreenSampleHeight = 27;

std::vector<DWORD> SampleScreen(const RECT& monitor) {
    std::vector<DWORD> pixels;
    HDC screen = GetDC(nullptr);
    HDC dc = screen ? CreateCompatibleDC(screen) : nullptr;
    BITMAPINFO info{};
    info.bmiHeader = {sizeof(BITMAPINFOHEADER), kScreenSampleWidth,
                      -kScreenSampleHeight, 1, 32, BI_RGB};
    void* bits = nullptr;
    HBITMAP bitmap = dc ? CreateDIBSection(dc, &info, DIB_RGB_COLORS, &bits,
                                           nullptr, 0)
                        : nullptr;
    if (bitmap) {
        HGDIOBJ old = SelectObject(dc, bitmap);
        SetStretchBltMode(dc, HALFTONE);
        if (StretchBlt(dc, 0, 0, kScreenSampleWidth, kScreenSampleHeight,
                       screen, monitor.left, monitor.top,
                       monitor.right - monitor.left,
                       monitor.bottom - monitor.top, SRCCOPY)) {
            GdiFlush();
            pixels.assign((const DWORD*)bits,
                          (const DWORD*)bits +
                              kScreenSampleWidth * kScreenSampleHeight);
        }
        SelectObject(dc, old);
        DeleteObject(bitmap);
    }
    if (dc) {
        DeleteDC(dc);
    }
    if (screen) {
        ReleaseDC(nullptr, screen);
    }
    return pixels;
}

// Whether two pixels differ by more than `threshold` in a color.
bool PixelDiffers(DWORD a, DWORD b, int threshold) {
    for (int shift : {0, 8, 16}) {
        if (std::abs((int)((a >> shift) & 0xFF) - (int)((b >> shift) & 0xFF)) >
            threshold) {
            return true;
        }
    }
    return false;
}

// How many of two samples' pixels differ by more than `threshold` in a
// color.
int SampleChanges(const std::vector<DWORD>& a,
                  const std::vector<DWORD>& b,
                  int threshold) {
    int changes = 0;
    for (size_t i = 0; i < a.size() && i < b.size(); i++) {
        changes += PixelDiffers(a[i], b[i], threshold);
    }
    return changes;
}

// Whether the screen (`now`) shows the new picture as the transition's
// window showed it (`wanted`), at the pixels where it differs from the old
// wallpaper (`places`): all of them but a few (a video or a moving window
// there). In between, Windows is still bringing it in (its own fade and
// zoom).
bool SampleShows(const std::vector<DWORD>& now,
                 const std::vector<DWORD>& wanted,
                 const std::vector<size_t>& places) {
    size_t off = 0;
    for (size_t i : places) {
        if (i >= now.size() || i >= wanted.size() ||
            PixelDiffers(now[i], wanted[i], 24)) {
            off++;
        }
    }
    return off * 10 <= places.size();
}


bool SetWallpaperForMonitor(const RECT& monitor, PCWSTR path) {
    const HRESULT com = CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    if (FAILED(com) && com != RPC_E_CHANGED_MODE) {
        return false;
    }
    bool result = false;
    winrt::com_ptr<IDesktopWallpaper> wallpaper;
    if (SUCCEEDED(CoCreateInstance(CLSID_DesktopWallpaper, nullptr, CLSCTX_ALL,
                                   IID_PPV_ARGS(wallpaper.put())))) {
        UINT count = 0;
        if (SUCCEEDED(wallpaper->GetMonitorDevicePathCount(&count))) {
            for (UINT i = 0; i < count; ++i) {
                PWSTR id = nullptr;
                RECT rect{};
                const HRESULT gotId = wallpaper->GetMonitorDevicePathAt(i, &id);
                const bool matched = SUCCEEDED(gotId) && id &&
                    SUCCEEDED(wallpaper->GetMonitorRECT(id, &rect)) &&
                    EqualRect(&rect, &monitor);
                if (matched) {
                    result = SUCCEEDED(wallpaper->SetWallpaper(id, path));
                    CoTaskMemFree(id);
                    break;
                }
                if (id) {
                    CoTaskMemFree(id);
                }
            }
            if (!result && count == 1) {
                result = SUCCEEDED(wallpaper->SetWallpaper(nullptr, path));
            }
        }
    }
    if (SUCCEEDED(com)) {
        CoUninitialize();
    }
    return result;
}

class WallpaperCanvas {
   public:
    bool Create(ID2D1Factory* factory) {
        const auto properties = D2D1::RenderTargetProperties(
            D2D1_RENDER_TARGET_TYPE_DEFAULT,
            D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM,
                              D2D1_ALPHA_MODE_PREMULTIPLIED),
            96, 96);
        if (FAILED(factory->CreateDCRenderTarget(&properties, target.put()))) {
            return false;
        }
        target->SetTextAntialiasMode(D2D1_TEXT_ANTIALIAS_MODE_GRAYSCALE);
        dc = CreateCompatibleDC(nullptr);
        return dc != nullptr;
    }

    bool Begin(SIZE size) {
        if (!dc || size.cx <= 0 || size.cy <= 0) {
            return false;
        }
        if (bitmap && (size.cx != bitmapSize.cx || size.cy != bitmapSize.cy)) {
            SelectObject(dc, oldBitmap);
            DeleteObject(bitmap);
            bitmap = nullptr;
            oldBitmap = nullptr;
        }
        if (!bitmap) {
            BITMAPINFO info{};
            info.bmiHeader.biSize = sizeof(info.bmiHeader);
            info.bmiHeader.biWidth = size.cx;
            info.bmiHeader.biHeight = -size.cy;
            info.bmiHeader.biPlanes = 1;
            info.bmiHeader.biBitCount = 32;
            info.bmiHeader.biCompression = BI_RGB;
            void* bits = nullptr;
            bitmap = CreateDIBSection(dc, &info, DIB_RGB_COLORS, &bits,
                                      nullptr, 0);
            if (!bitmap) {
                return false;
            }
            oldBitmap = SelectObject(dc, bitmap);
            bitmapSize = size;
        }
        drawSize = size;
        const RECT bounds{0, 0, size.cx, size.cy};
        if (FAILED(target->BindDC(dc, &bounds))) {
            return false;
        }
        target->BeginDraw();
        target->SetTransform(D2D1::Matrix3x2F::Identity());
        target->Clear(D2D1::ColorF(0, 0, 0, 0));
        return true;
    }

    bool Present(HWND window, POINT position) {
        if (FAILED(target->EndDraw())) {
            return false;
        }
        POINT source{0, 0};
        BLENDFUNCTION blend{AC_SRC_OVER, 0, 255, AC_SRC_ALPHA};
        return UpdateLayeredWindow(window, nullptr, &position, &drawSize,
                                   dc, &source, 0, &blend, ULW_ALPHA) != FALSE;
    }

    void SetAlpha(HWND window, POINT position, BYTE alpha) {
        if (!dc || !bitmap) {
            return;
        }
        POINT source{0, 0};
        BLENDFUNCTION blend{AC_SRC_OVER, 0, alpha, AC_SRC_ALPHA};
        UpdateLayeredWindow(window, nullptr, &position, &drawSize,
                            dc, &source, 0, &blend, ULW_ALPHA);
    }

    void Destroy() {
        target = nullptr;
        if (dc) {
            if (oldBitmap) {
                SelectObject(dc, oldBitmap);
            }
            DeleteDC(dc);
            dc = nullptr;
        }
        if (bitmap) {
            DeleteObject(bitmap);
            bitmap = nullptr;
        }
        oldBitmap = nullptr;
    }

    winrt::com_ptr<ID2D1DCRenderTarget> target;

   private:
    HDC dc = nullptr;
    HBITMAP bitmap = nullptr;
    HGDIOBJ oldBitmap = nullptr;
    SIZE bitmapSize{};
    SIZE drawSize{};
};

void PlaceWallpaperOverlay(HWND window) {
    HWND progman = FindWindowW(L"Progman", nullptr);
    HWND above = progman ? GetWindow(progman, GW_HWNDPREV) : nullptr;
    for (int i = 0; above && i < 1000 &&
                    (above == window || !IsWindowVisible(above)); ++i) {
        above = GetWindow(above, GW_HWNDPREV);
    }
    const bool topmost =
        above && (GetWindowLongPtrW(above, GWL_EXSTYLE) & WS_EX_TOPMOST);
    const HWND insertAfter =
        !progman ? HWND_BOTTOM : (above && !topmost ? above : HWND_TOP);
    SetWindowPos(window, insertAfter, 0, 0, 0, 0,
                 SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
}

struct WallpaperChange {
    HWND notifyWindow;
    int imageIndex;
    std::wstring path;
    RECT monitor;
    WallpaperTransition transition;
    POINT origin;
};

DWORD WINAPI WallpaperChangeThreadProc(void* parameter) {
    std::unique_ptr<WallpaperChange> change((WallpaperChange*)parameter);
    SetThreadDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
    const HRESULT com = CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    bool applied = false;
    const SIZE size{change->monitor.right - change->monitor.left,
                    change->monitor.bottom - change->monitor.top};
    const POINT position{change->monitor.left, change->monitor.top};
    DESKTOP_WALLPAPER_POSITION wallpaperPosition = DWPOS_FILL;
    COLORREF backgroundColor = RGB(0, 0, 0);
    winrt::com_ptr<IDesktopWallpaper> wallpaper;
    if (SUCCEEDED(CoCreateInstance(CLSID_DesktopWallpaper, nullptr, CLSCTX_ALL,
                                   IID_PPV_ARGS(wallpaper.put())))) {
        wallpaper->GetPosition(&wallpaperPosition);
        wallpaper->GetBackgroundColor(&backgroundColor);
    }

    const double duration = 0.7;
    D2D1_RECT_F pictureRect{};
    winrt::com_ptr<IWICImagingFactory> wic;
    winrt::com_ptr<ID2D1Factory> factory;
    winrt::com_ptr<IWICBitmapSource> picture;
    winrt::com_ptr<ID2D1Bitmap> bitmap;
    WallpaperCanvas canvas;
    HWND overlay = nullptr;

    if (duration > 0 && size.cx > 0 && size.cy > 0 &&
        SUCCEEDED(CoCreateInstance(CLSID_WICImagingFactory, nullptr,
                                   CLSCTX_INPROC_SERVER,
                                   IID_PPV_ARGS(wic.put()))) &&
        SUCCEEDED(D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED,
                                    factory.put())) &&
        canvas.Create(factory.get()) &&
        (picture = LoadWallpaperPicture(wic.get(), change->path.c_str(),
                                        size, wallpaperPosition,
                                        &pictureRect))) {
        overlay = CreateWindowExW(
            WS_EX_LAYERED | WS_EX_TRANSPARENT | WS_EX_TOOLWINDOW |
                WS_EX_NOACTIVATE,
            L"STATIC", nullptr, WS_POPUP, 0, 0, 0, 0,
            nullptr, nullptr, GetModuleHandleW(nullptr), nullptr);
        if (overlay) {
            SetPropW(overlay, L"NonRudeHWND", (HANDLE)TRUE);
            if (canvas.Begin(size) &&
                SUCCEEDED(canvas.target->CreateBitmapFromWicBitmap(
                    picture.get(), nullptr, bitmap.put()))) {
                canvas.target->EndDraw();
            }
        }
    }

    if (overlay && bitmap) {
        const float width = (float)size.cx;
        const float height = (float)size.cy;
        const D2D1_POINT_2F origin{
            (float)(change->origin.x - change->monitor.left),
            (float)(change->origin.y - change->monitor.top)};
        const float reach = std::hypot(std::max(origin.x, width - origin.x),
                                       std::max(origin.y, height - origin.y));
        const double start = (double)GetTickCount64() / 1000.0;
        bool shown = false;
        for (;;) {
            const double now = (double)GetTickCount64() / 1000.0;
            const double t = std::clamp((now - start) / duration, 0.0, 1.0);
            const float k = (float)(t < 0.5 ? 4 * t * t * t
                                           : 1 - std::pow(-2 * t + 2, 3) / 2);
            if (!canvas.Begin(size)) {
                break;
            }
            ID2D1RenderTarget* target = canvas.target.get();
            const D2D1_RECT_F full{0, 0, width, height};
            winrt::com_ptr<ID2D1SolidColorBrush> fill;
            target->CreateSolidColorBrush(
                D2D1::ColorF(GetRValue(backgroundColor) / 255.0f,
                             GetGValue(backgroundColor) / 255.0f,
                             GetBValue(backgroundColor) / 255.0f, 1),
                fill.put());
            auto drawPicture = [&](float offset, float opacity) {
                if (fill) {
                    fill->SetOpacity(opacity);
                    target->FillRectangle({offset, 0, offset + width, height},
                                          fill.get());
                }
                const D2D1_RECT_F rect{
                    pictureRect.left + offset, pictureRect.top,
                    pictureRect.right + offset, pictureRect.bottom};
                target->DrawBitmap(bitmap.get(), &rect, opacity,
                                   D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
            };
            switch (change->transition) {
                case WallpaperTransition::Circle: {
                    winrt::com_ptr<ID2D1EllipseGeometry> circle;
                    winrt::com_ptr<ID2D1Layer> layer;
                    if (SUCCEEDED(factory->CreateEllipseGeometry(
                            D2D1::Ellipse(origin, reach * k, reach * k),
                            circle.put())) &&
                        SUCCEEDED(target->CreateLayer(nullptr, layer.put()))) {
                        target->PushLayer(
                            D2D1::LayerParameters(full, circle.get()),
                            layer.get());
                        drawPicture(0, 1);
                        target->PopLayer();
                    }
                    break;
                }
                case WallpaperTransition::Slide:
                    drawPicture((1 - k) * width, 0.4f + 0.6f * k);
                    break;
                case WallpaperTransition::Zoom:
                    target->SetTransform(D2D1::Matrix3x2F::Scale(
                        1.12f - 0.12f * k, 1.12f - 0.12f * k,
                        {width / 2, height / 2}));
                    drawPicture(0, k);
                    target->SetTransform(D2D1::Matrix3x2F::Identity());
                    break;
                case WallpaperTransition::Fade:
                default:
                    drawPicture(0, k);
                    break;
            }
            if (!canvas.Present(overlay, position)) {
                break;
            }
            if (!shown) {
                ShowWindow(overlay, SW_SHOWNOACTIVATE);
                PlaceWallpaperOverlay(overlay);
                shown = true;
            }
            if (t >= 1) {
                break;
            }
            Sleep(16);
        }

        std::vector<DWORD> wanted;
        DwmFlush();
        wanted = SampleScreen(change->monitor);
        const bool sampled =
            !wanted.empty() &&
            SetWindowDisplayAffinity(overlay, WDA_EXCLUDEFROMCAPTURE) != FALSE;
        if (sampled) {
            DwmFlush();
        }
        const std::vector<DWORD> before =
            sampled ? SampleScreen(change->monitor) : std::vector<DWORD>{};
        applied = SetWallpaperForMonitor(change->monitor, change->path.c_str());

        const int pixels = kScreenSampleWidth * kScreenSampleHeight;
        std::vector<size_t> places;
        if (before.size() == wanted.size()) {
            for (size_t i = 0; i < before.size(); ++i) {
                if (PixelDiffers(before[i], wanted[i], 24)) {
                    places.push_back(i);
                }
            }
        }
        const double waitStart = (double)GetTickCount64() / 1000.0;
        std::vector<DWORD> last = before;
        int still = 0;
        while (applied && !places.empty() &&
               (double)GetTickCount64() / 1000.0 - waitStart < 2.5 &&
               still < 2) {
            Sleep(50);
            std::vector<DWORD> current = SampleScreen(change->monitor);
            if (current.size() != before.size()) {
                break;
            }
            still = SampleShows(current, wanted, places) &&
                            SampleChanges(current, last, 4) <= pixels / 50
                        ? still + 1
                        : 0;
            last = std::move(current);
        }
        if (before.empty()) {
            Sleep(400);
        }
        if (sampled) {
            SetWindowDisplayAffinity(overlay, WDA_NONE);
        }
        for (int step = 8; step >= 0; --step) {
            canvas.SetAlpha(overlay, position,
                            (BYTE)(step * 255 / 8));
            Sleep(25);
        }
    } else {
        applied = SetWallpaperForMonitor(change->monitor,
                                         change->path.c_str());
    }

    if (overlay) {
        RemovePropW(overlay, L"NonRudeHWND");
        DestroyWindow(overlay);
    }
    bitmap = nullptr;
    canvas.Destroy();
    canvas.target = nullptr;
    factory = nullptr;
    picture = nullptr;
    wic = nullptr;
    wallpaper = nullptr;
    if (SUCCEEDED(com)) {
        CoUninitialize();
    }
    PostMessageW(change->notifyWindow, kWallpaperChangeDone,
                 (WPARAM)change->imageIndex, applied ? 1 : 0);
    return 0;
}

WallpaperTransition ChooseWallpaperTransition() {
    if (g_transitionMode >= 0 && g_transitionMode < 4) {
        g_lastRandomTransition = g_transitionMode;
        return (WallpaperTransition)g_transitionMode;
    }
    static std::mt19937 random(
        (unsigned)GetTickCount() ^ (unsigned)(uintptr_t)&g_wallpaperThread);
    std::uniform_int_distribution<int> distribution(0, 3);
    int choice = distribution(random);
    if (choice == g_lastRandomTransition) {
        std::uniform_int_distribution<int> other(1, 3);
        choice = (choice + other(random)) % 4;
    }
    g_lastRandomTransition = choice;
    return (WallpaperTransition)choice;
}

void StartWallpaperChange(int image) {
    if (g_shuttingDown.load() || g_transitionActive ||
        image < 0 || image >= (int)g_images.size() || !g_hostWindow) {
        return;
    }
    POINT cursor{};
    GetCursorPos(&cursor);
    HMONITOR monitor = MonitorFromPoint(cursor, MONITOR_DEFAULTTONEAREST);
    MONITORINFO info{sizeof(info)};
    if (!monitor || !GetMonitorInfoW(monitor, &info)) {
        return;
    }
    if (g_wallpaperThread) {
        CloseHandle(g_wallpaperThread);
        g_wallpaperThread = nullptr;
    }
    auto* change = new WallpaperChange{
        g_hostWindow, image, g_images[image], info.rcMonitor,
        ChooseWallpaperTransition(), cursor};
    g_transitionPath = g_images[image];
    g_transitionActive = true;
    g_wallpaperThread = CreateThread(nullptr, 0, WallpaperChangeThreadProc,
                                     change, 0, nullptr);
    if (!g_wallpaperThread) {
        delete change;
        g_transitionActive = false;
        if (SetWallpaperForMonitor(info.rcMonitor, g_images[image].c_str())) {
            g_currentImage = image;
            for (HWND tile : g_tiles) {
                if (tile) {
                    InvalidateRect(tile, nullptr, FALSE);
                }
            }
        }
    }
}

void ApplyImageIndex(int image) {
    if (g_transitionActive || image < 0 || image >= (int)g_images.size()) {
        return;
    }
    g_selectedImage = image;
    for (HWND tile : g_tiles) {
        if (tile) {
            InvalidateRect(tile, nullptr, FALSE);
        }
    }
    StartWallpaperChange(image);
}

void StepImage(int step) {
    if (g_transitionActive) {
        return;
    }
    if (g_images.empty()) {
        ListImages();
    }
    if (g_images.empty()) {
        ShowWindow(g_pickerWindow, SW_SHOWNORMAL);
        SetForegroundWindow(g_pickerWindow);
        return;
    }
    int current = g_currentImage;
    if (current < 0) {
        current = step > 0 ? -1 : 0;
    }
    const int next = (current + step + (int)g_images.size()) %
                     (int)g_images.size();
    g_page = (size_t)next / kPageSize;
    g_selectedImage = next;
    RefreshList();
    StartWallpaperChange(next);
}

void StepPage(int step) {
    const int pages = (int)std::max<size_t>(
        1, (g_images.size() + kPageSize - 1) / kPageSize);
    const int page = ((int)g_page + step % pages + pages) % pages;
    if ((size_t)page == g_page) {
        return;
    }
    g_page = (size_t)page;
    g_selectedImage = g_images.empty() ? -1 : (int)(g_page * kPageSize);
    RefreshList();
}

void MoveSelection(int delta) {
    if (g_images.empty() || g_transitionActive) {
        return;
    }
    int current = g_selectedImage;
    if (current < 0 || current >= (int)g_images.size()) {
        current = g_currentImage >= 0 ? g_currentImage : 0;
    }
    const int count = (int)g_images.size();
    const int next = (current + delta % count + count) % count;
    g_selectedImage = next;
    const size_t page = (size_t)next / kPageSize;
    if (page != g_page) {
        g_page = page;
        RefreshList();
    } else {
        for (HWND tile : g_tiles) {
            if (tile) {
                InvalidateRect(tile, nullptr, FALSE);
            }
        }
    }
    const size_t slot = (size_t)next % kPageSize;
    if (g_tiles[slot]) {
        SetFocus(g_tiles[slot]);
    }
}

bool HandlePickerKey(UINT key) {
    switch (key) {
        case VK_LEFT:
            MoveSelection(-1);
            return true;
        case VK_RIGHT:
            MoveSelection(1);
            return true;
        case VK_UP:
            MoveSelection(-(int)kGridColumns);
            return true;
        case VK_DOWN:
            MoveSelection((int)kGridColumns);
            return true;
        case VK_SPACE:
        case VK_RETURN:
            if (!g_transitionActive && g_selectedImage >= 0) {
                ApplyImageIndex(g_selectedImage);
            }
            return true;
        default:
            return false;
    }
}

LRESULT CALLBACK TileSubclassProc(HWND hwnd, UINT message, WPARAM wParam,
                                  LPARAM lParam, UINT_PTR, DWORD_PTR) {
    if (message == WM_MOUSEWHEEL && GetDlgCtrlID(hwnd) >= kFirstTileId) {
        StepPage(GET_WHEEL_DELTA_WPARAM(wParam) > 0 ? -1 : 1);
        return 0;
    }
    if (message == WM_KEYDOWN && wParam == VK_ESCAPE) {
        PostMessageW(GetAncestor(hwnd, GA_ROOT), WM_CLOSE, 0, 0);
        return 0;
    }
    if (message == WM_KEYDOWN && HandlePickerKey((UINT)wParam)) {
        return 0;
    }
    if (message == WM_KEYUP &&
        (wParam == VK_SPACE || wParam == VK_RETURN)) {
        return 0;
    }
    return DefSubclassProc(hwnd, message, wParam, lParam);
}

void ShowPicker() {
    if (!g_pickerWindow) {
        return;
    }
    if (g_folder.empty()) {
        std::wstring folder;
        if (PickFolder(g_pickerWindow, &folder)) {
            g_folder = std::move(folder);
            PersistFolder();
            ListImages();
            RefreshList();
        }
    } else if (g_images.empty()) {
        ListImages();
        RefreshList();
    }
    if (!IsWindowVisible(g_pickerWindow)) {
        POINT cursor{};
        GetCursorPos(&cursor);
        MONITORINFO info{sizeof(info)};
        HMONITOR monitor = MonitorFromPoint(cursor, MONITOR_DEFAULTTONEAREST);
        if (monitor && GetMonitorInfoW(monitor, &info)) {
            constexpr int width = 560;
            constexpr int height = 360;
            const RECT& work = info.rcWork;
            const int x = work.left +
                          std::max(0L, (work.right - work.left - width) / 2);
            const int y = work.top +
                          std::max(0L, (work.bottom - work.top - height) / 2);
            SetWindowPos(g_pickerWindow, HWND_TOPMOST, x, y, width, height,
                         SWP_NOACTIVATE);
        }
    }
    if (g_selectedImage < 0 || g_selectedImage >= (int)g_images.size()) {
        g_selectedImage = g_currentImage >= 0
                              ? g_currentImage
                              : (g_images.empty() ? -1 : (int)(g_page * kPageSize));
    }
    if (!IsWindowVisible(g_pickerWindow)) {
        if (!AnimateWindow(g_pickerWindow, 160, AW_BLEND | AW_ACTIVATE)) {
            ShowWindow(g_pickerWindow, SW_SHOWNORMAL);
        }
    }
    SetForegroundWindow(g_pickerWindow);
    if (g_selectedImage >= 0 && !g_transitionActive) {
        const size_t slot = (size_t)g_selectedImage % kPageSize;
        if (g_tiles[slot]) {
            SetFocus(g_tiles[slot]);
        }
    }
    // AnimateWindow can show the parent before every owner-drawn child has
    // completed its first paint. Refresh the whole tree once it is visible.
    RedrawWindow(g_pickerWindow, nullptr, nullptr,
                 RDW_INVALIDATE | RDW_ALLCHILDREN | RDW_UPDATENOW);
}

void TogglePicker() {
    if (!g_pickerWindow) {
        return;
    }
    if (IsWindowVisible(g_pickerWindow)) {
        PostMessageW(g_pickerWindow, WM_CLOSE, 0, 0);
    } else {
        ShowPicker();
    }
}

HFONT CreatePickerFont(HWND hwnd) {
    UINT dpi = GetDpiForWindow(hwnd);
    if (!dpi) {
        dpi = 96;
    }
    return CreateFontW(-MulDiv(10, (int)dpi, 72), 0, 0, 0, FW_NORMAL,
                       FALSE, FALSE, FALSE, DEFAULT_CHARSET,
                       OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                       CLEARTYPE_QUALITY, VARIABLE_PITCH | FF_DONTCARE,
                       L"Segoe UI Variable Text");
}

HWND CreateStyledButton(HWND parent, PCWSTR text, int id, int x, int y,
                        int width, int height, bool primary = false) {
    HWND button = CreateWindowExW(0, L"BUTTON", text,
        WS_CHILD | WS_VISIBLE | BS_OWNERDRAW, x, y, width, height, parent,
        (HMENU)(INT_PTR)id, GetModuleHandleW(nullptr), nullptr);
    if (button && g_pickerFont) {
        SendMessageW(button, WM_SETFONT, (WPARAM)g_pickerFont, TRUE);
    }
    if (button && primary) {
        SetPropW(button, L"WallpaperSwitcherPrimary", (HANDLE)1);
    }
    return button;
}

void DrawStyledButton(const DRAWITEMSTRUCT* item) {
    if (!item || item->CtlType != ODT_BUTTON) {
        return;
    }
    const bool primary = GetPropW(item->hwndItem,
                                  L"WallpaperSwitcherPrimary") != nullptr;
    const bool disabled = (item->itemState & ODS_DISABLED) != 0;
    const bool pressed = (item->itemState & ODS_SELECTED) != 0;
    const bool hot = (item->itemState & ODS_HOTLIGHT) != 0;
    COLORREF fill = primary ? kAccent : kSurface;
    if (disabled) {
        fill = kBackground;
    } else if (pressed) {
        fill = primary ? RGB(186, 140, 235) : RGB(60, 56, 82);
    } else if (hot) {
        fill = primary ? RGB(218, 184, 255) : RGB(65, 60, 91);
    }
    HBRUSH brush = CreateSolidBrush(fill);
    HPEN pen = CreatePen(PS_SOLID, 1, primary ? kAccent : kBorder);
    HGDIOBJ oldBrush = SelectObject(item->hDC, brush);
    HGDIOBJ oldPen = SelectObject(item->hDC, pen);
    HGDIOBJ oldFont = g_pickerFont
                          ? SelectObject(item->hDC, g_pickerFont)
                          : nullptr;
    const RECT r = item->rcItem;
    FillRect(item->hDC, &r, g_backgroundBrush);
    RoundRect(item->hDC, r.left, r.top, r.right, r.bottom, 10, 10);
    SetBkMode(item->hDC, TRANSPARENT);
    SetTextColor(item->hDC, disabled ? kMuted : (primary ? kBackground : kText));
    WCHAR text[128]{};
    GetWindowTextW(item->hwndItem, text, ARRAYSIZE(text));
    RECT textRect = r;
    DrawTextW(item->hDC, text, -1, &textRect,
              DT_CENTER | DT_VCENTER | DT_SINGLELINE | DT_END_ELLIPSIS);
    if (item->itemState & ODS_FOCUS) {
        RECT focus = r;
        InflateRect(&focus, -4, -4);
        DrawFocusRect(item->hDC, &focus);
    }
    if (oldFont) {
        SelectObject(item->hDC, oldFont);
    }
    SelectObject(item->hDC, oldBrush);
    SelectObject(item->hDC, oldPen);
    DeleteObject(brush);
    DeleteObject(pen);
}

bool DrawTileButton(const DRAWITEMSTRUCT* item) {
    if (!item || item->CtlType != ODT_BUTTON ||
        item->CtlID < kFirstTileId ||
        item->CtlID >= kFirstTileId + kPageSize) {
        return false;
    }
    const size_t slot = item->CtlID - kFirstTileId;
    const size_t index = g_page * kPageSize + slot;
    FillRect(item->hDC, &item->rcItem, g_backgroundBrush);
    if (g_thumbnails[slot]) {
        BITMAP bitmapInfo{};
        if (GetObjectW(g_thumbnails[slot], sizeof(bitmapInfo), &bitmapInfo) &&
            bitmapInfo.bmWidth > 0 && bitmapInfo.bmHeight > 0) {
            HDC sourceDc = CreateCompatibleDC(item->hDC);
            if (sourceDc) {
                HGDIOBJ oldBitmap = SelectObject(sourceDc, g_thumbnails[slot]);
                const int savedDc = SaveDC(item->hDC);
                if (savedDc) {
                    HRGN rounded = CreateRoundRectRgn(
                        item->rcItem.left, item->rcItem.top,
                        item->rcItem.right + 1, item->rcItem.bottom + 1,
                        16, 16);
                    if (rounded) {
                        SelectClipRgn(item->hDC, rounded);
                        const double scale = std::max(
                            (double)kThumbnailWidth / bitmapInfo.bmWidth,
                            (double)kThumbnailHeight / bitmapInfo.bmHeight);
                        const int cropWidth = std::max(
                            1, (int)std::lround(kThumbnailWidth / scale));
                        const int cropHeight = std::max(
                            1, (int)std::lround(kThumbnailHeight / scale));
                        const int cropX = (int)std::max(
                            0L, (bitmapInfo.bmWidth - cropWidth) / 2);
                        const int cropY = (int)std::max(
                            0L, (bitmapInfo.bmHeight - cropHeight) / 2);
                        SetStretchBltMode(item->hDC, HALFTONE);
                        SetBrushOrgEx(item->hDC, 0, 0, nullptr);
                        if (bitmapInfo.bmBitsPixel == 32) {
                            BLENDFUNCTION blend{AC_SRC_OVER, 0, 255,
                                                AC_SRC_ALPHA};
                            AlphaBlend(item->hDC, item->rcItem.left,
                                       item->rcItem.top, kThumbnailWidth,
                                       kThumbnailHeight, sourceDc, cropX,
                                       cropY, cropWidth, cropHeight, blend);
                        } else {
                            StretchBlt(item->hDC, item->rcItem.left,
                                       item->rcItem.top, kThumbnailWidth,
                                       kThumbnailHeight, sourceDc, cropX,
                                       cropY, cropWidth, cropHeight, SRCCOPY);
                        }
                        DeleteObject(rounded);
                    }
                    RestoreDC(item->hDC, savedDc);
                }
                SelectObject(sourceDc, oldBitmap);
                DeleteDC(sourceDc);
            }
        }
    }
    const bool selected = (int)index == g_selectedImage;
    if (selected || (item->itemState & ODS_HOTLIGHT)) {
        const COLORREF color = selected ? kAccent : kMuted;
        HPEN pen = CreatePen(PS_SOLID, selected ? 2 : 1, color);
        HGDIOBJ oldPen = SelectObject(item->hDC, pen);
        HGDIOBJ oldBrush = SelectObject(item->hDC, GetStockObject(NULL_BRUSH));
        RoundRect(item->hDC, item->rcItem.left, item->rcItem.top,
                  item->rcItem.right, item->rcItem.bottom, 16, 16);
        SelectObject(item->hDC, oldBrush);
        SelectObject(item->hDC, oldPen);
        DeleteObject(pen);
    }
    if (item->itemState & ODS_FOCUS) {
        RECT focus = item->rcItem;
        InflateRect(&focus, -4, -4);
        DrawFocusRect(item->hDC, &focus);
    }
    return true;
}

void StylePickerWindow(HWND hwnd) {
    const BOOL dark = TRUE;
    const DWORD corner = 2;  // DWMWCP_ROUNDSMALL
    DwmSetWindowAttribute(hwnd, 20, &dark, sizeof(dark));
    DwmSetWindowAttribute(hwnd, 19, &dark, sizeof(dark));
    DwmSetWindowAttribute(hwnd, 33, &corner, sizeof(corner));
    SetWindowTheme(hwnd, L"DarkMode_Explorer", nullptr);
}

HICON CreateWallpaperTrayIcon() {
    constexpr int size = 32;
    HDC screen = GetDC(nullptr);
    if (!screen) {
        return nullptr;
    }
    BITMAPINFO info{};
    info.bmiHeader.biSize = sizeof(info.bmiHeader);
    info.bmiHeader.biWidth = size;
    info.bmiHeader.biHeight = -size;
    info.bmiHeader.biPlanes = 1;
    info.bmiHeader.biBitCount = 32;
    info.bmiHeader.biCompression = BI_RGB;
    void* bits = nullptr;
    HBITMAP color = CreateDIBSection(screen, &info, DIB_RGB_COLORS,
                                     &bits, nullptr, 0);
    ReleaseDC(nullptr, screen);
    if (!color || !bits) {
        if (color) DeleteObject(color);
        return nullptr;
    }
    std::fill_n((DWORD*)bits, size * size, 0);
    HDC dc = CreateCompatibleDC(nullptr);
    if (!dc) {
        DeleteObject(color);
        return nullptr;
    }
    HGDIOBJ oldBitmap = SelectObject(dc, color);
    HFONT font = CreateFontW(-26, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE,
                             DEFAULT_CHARSET, OUT_DEFAULT_PRECIS,
                             CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY,
                             VARIABLE_PITCH | FF_DONTCARE,
                             L"Segoe Fluent Icons");
    HGDIOBJ oldFont = font ? SelectObject(dc, font) : nullptr;
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, RGB(255, 255, 255));
    RECT rect{0, 0, size, size};
    const WCHAR glyph[] = {0xE8B9, L'\0'};
    DrawTextW(dc, glyph, -1, &rect,
              DT_CENTER | DT_VCENTER | DT_SINGLELINE | DT_NOPREFIX);
    GdiFlush();
    DWORD* pixels = (DWORD*)bits;
    for (int i = 0; i < size * size; ++i) {
        const BYTE red = (BYTE)(pixels[i] >> 16);
        const BYTE green = (BYTE)(pixels[i] >> 8);
        const BYTE blue = (BYTE)pixels[i];
        const BYTE coverage = std::max(red, std::max(green, blue));
        const BYTE r = (BYTE)(GetRValue(kText) * coverage / 255);
        const BYTE g = (BYTE)(GetGValue(kText) * coverage / 255);
        const BYTE b = (BYTE)(GetBValue(kText) * coverage / 255);
        pixels[i] = ((DWORD)coverage << 24) | ((DWORD)r << 16) |
                    ((DWORD)g << 8) | b;
    }
    if (oldFont) SelectObject(dc, oldFont);
    if (font) DeleteObject(font);
    SelectObject(dc, oldBitmap);
    DeleteDC(dc);

    BYTE maskBits[size * 4]{};
    HBITMAP mask = CreateBitmap(size, size, 1, 1, maskBits);
    ICONINFO iconInfo{};
    iconInfo.fIcon = TRUE;
    iconInfo.hbmMask = mask;
    iconInfo.hbmColor = color;
    HICON icon = mask ? CreateIconIndirect(&iconInfo) : nullptr;
    if (mask) DeleteObject(mask);
    DeleteObject(color);
    return icon;
}

void AddTrayIcon(HWND hwnd) {
    g_notifyIcon = {};
    g_notifyIcon.cbSize = sizeof(g_notifyIcon);
    g_notifyIcon.hWnd = hwnd;
    g_notifyIcon.uID = 1;
    g_notifyIcon.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP;
    g_notifyIcon.uCallbackMessage = kTrayCallback;
    g_trayIcon = CreateWallpaperTrayIcon();
    g_notifyIcon.hIcon = g_trayIcon ? g_trayIcon : LoadIcon(nullptr, IDI_APPLICATION);
    wcscpy_s(g_notifyIcon.szTip, L"Simple Wallpaper Switcher");
    Shell_NotifyIconW(NIM_ADD, &g_notifyIcon);
    g_notifyIcon.uVersion = NOTIFYICON_VERSION_4;
    Shell_NotifyIconW(NIM_SETVERSION, &g_notifyIcon);
}

void ShowTrayMenu(HWND hwnd) {
    HMENU menu = CreatePopupMenu();
    AppendMenuW(menu, MF_STRING, kTrayOpen, L"Open wallpaper picker");
    AppendMenuW(menu, MF_STRING, kTrayPrevious, L"Previous wallpaper");
    AppendMenuW(menu, MF_STRING, kTrayNext, L"Next wallpaper");
    AppendMenuW(menu, MF_SEPARATOR, 0, nullptr);
    AppendMenuW(menu, MF_STRING, kTrayExit, L"Close switcher");
    POINT cursor{};
    GetCursorPos(&cursor);
    SetForegroundWindow(hwnd);
    TrackPopupMenu(menu, TPM_RIGHTBUTTON | TPM_BOTTOMALIGN | TPM_LEFTALIGN,
                   cursor.x, cursor.y, 0, hwnd, nullptr);
    DestroyMenu(menu);
}

LRESULT CALLBACK PickerProc(HWND hwnd, UINT message, WPARAM wParam,
                             LPARAM lParam) {
    switch (message) {
        case WM_CREATE: {
            g_pickerFont = CreatePickerFont(hwnd);
            g_folderLabel = CreateWindowExW(0, L"STATIC", L"",
                WS_CHILD | WS_VISIBLE | SS_LEFT, 16, 13, 430, 24, hwnd,
                (HMENU)(INT_PTR)kFolderLabelId, nullptr, nullptr);
            if (g_folderLabel && g_pickerFont) {
                SendMessageW(g_folderLabel, WM_SETFONT,
                             (WPARAM)g_pickerFont, TRUE);
            }
            g_folderButton = CreateStyledButton(hwnd, L"Folder", kChooseFolder,
                                                466, 10, 78, 30);
            if (g_folderButton) {
                SetWindowSubclass(g_folderButton, TileSubclassProc, 2,
                                  (DWORD_PTR)hwnd);
            }
            for (size_t slot = 0; slot < kPageSize; ++slot) {
                const int x = 14 + (int)(slot % kGridColumns) * 132;
                const int y = 50 + (int)(slot / kGridColumns) * 82;
                g_tiles[slot] = CreateWindowExW(0, L"BUTTON", L"",
                    WS_CHILD | WS_VISIBLE | BS_OWNERDRAW, x, y, kThumbnailWidth,
                    kThumbnailHeight, hwnd,
                    (HMENU)(INT_PTR)(kFirstTileId + slot),
                    GetModuleHandleW(nullptr), nullptr);
                if (g_tiles[slot]) {
                    SetWindowSubclass(g_tiles[slot], TileSubclassProc, 1,
                                      (DWORD_PTR)hwnd);
                }
            }
            g_pageLabel = CreateWindowExW(0, L"STATIC", L"1 / 1",
                WS_CHILD | WS_VISIBLE | SS_LEFT, 16, 314, 528, 24,
                hwnd, (HMENU)(INT_PTR)kPageLabelId, nullptr, nullptr);
            if (g_pageLabel && g_pickerFont) {
                SendMessageW(g_pageLabel, WM_SETFONT,
                             (WPARAM)g_pickerFont, TRUE);
            }
            UpdateFolderLabel();
            if (!g_folder.empty()) {
                ListImages();
                g_selectedImage = g_currentImage >= 0
                                      ? g_currentImage
                                      : (g_images.empty() ? -1 : 0);
                RefreshList();
            }
            return 0;
        }
        case WM_COMMAND:
            switch (LOWORD(wParam)) {
                case kChooseFolder: {
                    if (g_transitionActive) {
                        return 0;
                    }
                    std::wstring folder;
                    if (PickFolder(hwnd, &folder)) {
                        g_folder = std::move(folder);
                        g_page = 0;
                        g_currentImage = -1;
                        PersistFolder();
                        ListImages();
                        g_selectedImage = g_images.empty() ? -1 : 0;
                        RefreshList();
                    }
                    return 0;
                }
            }
            if (LOWORD(wParam) >= kFirstTileId &&
                LOWORD(wParam) < kFirstTileId + kPageSize) {
                const size_t slot = LOWORD(wParam) - kFirstTileId;
                ApplyImageIndex((int)(g_page * kPageSize + slot));
                return 0;
            }
            break;
        case WM_DRAWITEM:
            if (!DrawTileButton((const DRAWITEMSTRUCT*)lParam)) {
                DrawStyledButton((const DRAWITEMSTRUCT*)lParam);
            }
            return TRUE;
        case WM_CTLCOLORSTATIC:
            SetTextColor((HDC)wParam,
                         GetDlgCtrlID((HWND)lParam) == kFolderLabelId
                             ? kText
                             : kMuted);
            SetBkMode((HDC)wParam, TRANSPARENT);
            return (LRESULT)g_backgroundBrush;
        case WM_ERASEBKGND: {
            RECT client{};
            GetClientRect(hwnd, &client);
            FillRect((HDC)wParam, &client, g_backgroundBrush);
            return 1;
        }
        case WM_MOUSEWHEEL:
            StepPage(GET_WHEEL_DELTA_WPARAM(wParam) > 0 ? -1 : 1);
            return 0;
        case WM_KEYDOWN:
            if (wParam == VK_ESCAPE) {
                PostMessageW(hwnd, WM_CLOSE, 0, 0);
                return 0;
            }
            if (HandlePickerKey((UINT)wParam)) {
                return 0;
            }
            break;
        case WM_KEYUP:
            if (wParam == VK_SPACE || wParam == VK_RETURN) {
                return 0;
            }
            break;
        case WM_ACTIVATE:
            if (LOWORD(wParam) == WA_INACTIVE) {
                HWND activated = (HWND)lParam;
                if (!activated ||
                    GetAncestor(activated, GA_ROOTOWNER) != hwnd) {
                    PostMessageW(hwnd, WM_CLOSE, 0, 0);
                }
            }
            return 0;
        case WM_CLOSE:
            AnimateWindow(hwnd, 130, AW_BLEND | AW_HIDE);
            return 0;
        case WM_DESTROY:
            for (HWND tile : g_tiles) {
                if (tile) {
                    RemoveWindowSubclass(tile, TileSubclassProc, 1);
                }
            }
            if (g_folderButton) {
                RemoveWindowSubclass(g_folderButton, TileSubclassProc, 2);
                g_folderButton = nullptr;
            }
            DestroyThumbnails();
            if (g_pickerFont) {
                DeleteObject(g_pickerFont);
                g_pickerFont = nullptr;
            }
            g_pickerWindow = nullptr;
            return 0;
    }
    return DefWindowProcW(hwnd, message, wParam, lParam);
}

LRESULT CALLBACK HostProc(HWND hwnd, UINT message, WPARAM wParam,
                          LPARAM lParam) {
    switch (message) {
        case kWallpaperChangeDone:
            g_transitionActive = false;
            if (lParam && (int)wParam >= 0 &&
                (size_t)wParam < g_images.size() &&
                g_images[(size_t)wParam] == g_transitionPath) {
                g_currentImage = (int)wParam;
                for (HWND tile : g_tiles) {
                    if (tile) {
                        InvalidateRect(tile, nullptr, FALSE);
                    }
                }
            }
            g_transitionPath.clear();
            return 0;
        case kReloadSettings:
            if (!RegisterPickerHotkey(hwnd)) {
                Wh_Log(L"RegisterHotKey failed after settings change");
            }
            g_page = 0;
            g_currentImage = -1;
            ListImages();
            g_selectedImage = g_images.empty() ? -1 : 0;
            RefreshList();
            return 0;
        case WM_HOTKEY:
            if (wParam == kHotkeyId) {
                TogglePicker();
            }
            return 0;
        case kTrayCallback:
            if (LOWORD(lParam) == WM_LBUTTONUP ||
                LOWORD(lParam) == WM_LBUTTONDBLCLK) {
                ShowPicker();
            } else if (LOWORD(lParam) == WM_RBUTTONUP) {
                ShowTrayMenu(hwnd);
            }
            return 0;
        case WM_COMMAND:
            switch (LOWORD(wParam)) {
                case kTrayOpen:
                    ShowPicker();
                    return 0;
                case kTrayPrevious:
                    StepImage(-1);
                    return 0;
                case kTrayNext:
                    StepImage(1);
                    return 0;
                case kTrayExit:
                    DestroyWindow(hwnd);
                    return 0;
            }
            break;
        case WM_DESTROY:
            UnregisterHotKey(hwnd, kHotkeyId);
            Shell_NotifyIconW(NIM_DELETE, &g_notifyIcon);
            if (g_trayIcon) {
                DestroyIcon(g_trayIcon);
                g_trayIcon = nullptr;
            }
            if (g_pickerWindow) {
                DestroyWindow(g_pickerWindow);
            }
            g_hostWindow = nullptr;
            PostQuitMessage(0);
            return 0;
    }
    return DefWindowProcW(hwnd, message, wParam, lParam);
}

DWORD WINAPI UiThreadProc(void*) {
    INITCOMMONCONTROLSEX controls{sizeof(controls), ICC_LISTVIEW_CLASSES};
    InitCommonControlsEx(&controls);
    g_backgroundBrush = CreateSolidBrush(kBackground);
    WNDCLASSEXW hostClass{sizeof(hostClass)};
    hostClass.lpfnWndProc = HostProc;
    hostClass.hInstance = GetModuleHandleW(nullptr);
    hostClass.lpszClassName = L"SimpleWallpaperSwitcherHost";
    RegisterClassExW(&hostClass);
    WNDCLASSEXW pickerClass{sizeof(pickerClass)};
    pickerClass.lpfnWndProc = PickerProc;
    pickerClass.style = CS_DROPSHADOW;
    pickerClass.hInstance = GetModuleHandleW(nullptr);
    pickerClass.hCursor = LoadCursor(nullptr, IDC_ARROW);
    pickerClass.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    pickerClass.lpszClassName = kWindowClass;
    RegisterClassExW(&pickerClass);

    g_hostWindow = CreateWindowExW(0, hostClass.lpszClassName, L"", 0,
        0, 0, 0, 0, HWND_MESSAGE, nullptr, hostClass.hInstance, nullptr);
    if (g_hostWindow) {
        g_pickerWindow = CreateWindowExW(WS_EX_TOOLWINDOW,
            kWindowClass, L"Simple Wallpaper Switcher",
            WS_POPUP,
            CW_USEDEFAULT, CW_USEDEFAULT, 560, 360, nullptr, nullptr,
            pickerClass.hInstance, nullptr);
        if (g_pickerWindow) {
            StylePickerWindow(g_pickerWindow);
        }
        AddTrayIcon(g_hostWindow);
        if (!RegisterPickerHotkey(g_hostWindow)) {
            Wh_Log(L"RegisterHotKey failed; tray icon remains available");
        }
    }
    SetEvent(g_readyEvent);

    MSG message{};
    while (GetMessageW(&message, nullptr, 0, 0) > 0) {
        TranslateMessage(&message);
        DispatchMessageW(&message);
    }
    if (g_hostWindow) {
        DestroyWindow(g_hostWindow);
        g_hostWindow = nullptr;
    }
    if (g_backgroundBrush) {
        DeleteObject(g_backgroundBrush);
        g_backgroundBrush = nullptr;
    }
    return 0;
}

}

void WhTool_ModUninit();

BOOL WhTool_ModInit() {
    g_shuttingDown.store(false);
    LoadSettings();
    g_readyEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr);
    if (!g_readyEvent) {
        return FALSE;
    }
    g_uiThread = CreateThread(nullptr, 0, UiThreadProc, nullptr, 0,
                              &g_uiThreadId);
    if (!g_uiThread) {
        CloseHandle(g_readyEvent);
        g_readyEvent = nullptr;
        return FALSE;
    }
    if (WaitForSingleObject(g_readyEvent, 5000) != WAIT_OBJECT_0 ||
        !g_hostWindow || !g_pickerWindow) {
        WhTool_ModUninit();
        return FALSE;
    }
    return TRUE;
}

void WhTool_ModSettingsChanged() {
    LoadSettings();
    if (g_hostWindow) {
        PostMessageW(g_hostWindow, kReloadSettings, 0, 0);
    }
}

void WhTool_ModUninit() {
    g_shuttingDown.store(true);
    if (g_hostWindow) {
        PostMessageW(g_hostWindow, WM_CLOSE, 0, 0);
    }
    if (g_uiThreadId) {
        PostThreadMessageW(g_uiThreadId, WM_QUIT, 0, 0);
    }
    if (g_uiThread) {
        WaitForSingleObject(g_uiThread, 5000);
        CloseHandle(g_uiThread);
        g_uiThread = nullptr;
    }
    if (g_wallpaperThread) {
        WaitForSingleObject(g_wallpaperThread, INFINITE);
        CloseHandle(g_wallpaperThread);
        g_wallpaperThread = nullptr;
    }
    if (g_readyEvent) {
        CloseHandle(g_readyEvent);
        g_readyEvent = nullptr;
    }
}

