#![cfg(windows)]
// All Win32 interop lives in this file. The pure expansion logic (case
// matching, config parsing) lives in logic.rs and has no dependency on
// Windows, so it can be unit-tested on any platform.

use crate::logic;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::mem::{size_of, zeroed};
use std::os::windows::ffi::OsStrExt;
use std::path::PathBuf;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;

use winapi::shared::minwindef::{HINSTANCE, HKEY, LPARAM, LRESULT, UINT, WPARAM};
use winapi::shared::windef::{HHOOK, HICON, HWND, POINT};
use winapi::shared::winerror::ERROR_ALREADY_EXISTS;
use winapi::um::errhandlingapi::GetLastError;
use winapi::um::libloaderapi::GetModuleHandleW;
use winapi::um::shellapi::{
    ShellExecuteW, Shell_NotifyIconW, NIF_ICON, NIF_MESSAGE, NIF_TIP, NIM_ADD, NIM_DELETE,
    NOTIFYICONDATAW,
};
use winapi::um::synchapi::CreateMutexW;
use winapi::um::winnt::{KEY_SET_VALUE, REG_OPTION_NON_VOLATILE, REG_SZ};
use winapi::um::winreg::{
    RegCloseKey, RegCreateKeyExW, RegDeleteValueW, RegSetValueExW, HKEY_CURRENT_USER,
};
use winapi::um::winuser::{
    AppendMenuW, CallNextHookEx, CreatePopupMenu, CreateWindowExW, DefWindowProcW, DestroyWindow,
    DispatchMessageW, FindWindowW, GetAsyncKeyState, GetCursorPos, GetForegroundWindow,
    GetKeyState, GetKeyboardLayout, GetMessageW, GetSystemMetrics, GetWindowThreadProcessId,
    LoadIconW, LoadImageW, PostQuitMessage, RegisterClassW, RegisterWindowMessageW, SendInput,
    SetForegroundWindow, SetWindowsHookExW, ToUnicodeEx, TrackPopupMenu, TranslateMessage,
    UnhookWindowsHookEx, HC_ACTION, IDI_APPLICATION, IMAGE_ICON, INPUT, INPUT_KEYBOARD,
    KBDLLHOOKSTRUCT, KEYBDINPUT, KEYEVENTF_KEYUP, KEYEVENTF_UNICODE, LLKHF_INJECTED,
    LR_DEFAULTSIZE, MF_CHECKED, MF_SEPARATOR, MF_STRING, MF_UNCHECKED, MSG, SM_CXSMICON,
    SM_CYSMICON, TPM_BOTTOMALIGN, TPM_LEFTALIGN, TPM_RIGHTBUTTON, VK_BACK, VK_CAPITAL,
    VK_CONTROL, VK_LCONTROL, VK_LMENU, VK_LSHIFT, VK_LWIN, VK_MENU, VK_RCONTROL, VK_RETURN,
    VK_RMENU, VK_RSHIFT, VK_RWIN, VK_SHIFT, VK_SPACE, VK_TAB, WH_KEYBOARD_LL, WM_APP, WM_COMMAND,
    WM_DESTROY, WM_KEYDOWN, WM_KEYUP, WM_LBUTTONUP, WM_RBUTTONUP, WM_SYSKEYDOWN, WM_SYSKEYUP,
    WNDCLASSW,
};

const WM_TRAYICON: UINT = WM_APP + 1;
const ID_RELOAD: usize = 1001;
const ID_OPEN_CONFIG: usize = 1002;
const ID_EXIT: usize = 1003;
const ID_TOGGLE_ENABLED: usize = 1004;
const ID_HIDE_TRAY: usize = 1005;
const ID_OPEN_SETTINGS: usize = 1006;
const ID_TOGGLE_STARTUP: usize = 1007;
const TRAY_ID: u32 = 1;
const MAX_BUFFER_LEN: usize = 64;

/// A name used both for the single-instance mutex and as the base for the
/// registered "wake up and show your tray icon again" window message.
/// Kept fairly unique to avoid colliding with unrelated apps.
const APP_UNIQUE_NAME: &str = "Textpander_Alfakynz";

/// Value returned by RegisterWindowMessageW, computed once at startup and
/// used both to post the message (from a second launched instance) and to
/// recognize it (in wndproc of the already-running instance).
static WAKE_MSG: AtomicU32 = AtomicU32::new(0);

/// Remembers the most recent expansion so a Backspace pressed immediately
/// afterward can undo it (restoring exactly what was typed).
struct LastExpansion {
    typed: String,
    expansion: String,
}

struct AppState {
    config: HashMap<String, String>,
    replacements_path: PathBuf,
    settings_path: PathBuf,
    buffer: String,
    last_expansion: Option<LastExpansion>,
    /// Set right after an undo, so that hitting the boundary key again
    /// immediately (without typing any more letters) does not silently
    /// re-expand the same occurrence. Cleared as soon as a letter is typed
    /// (that means the word is being actively edited again) or after the
    /// next boundary key is processed (one-shot).
    suppress_expansion: bool,
    /// When we swallow a keydown ourselves (a boundary key we're replacing,
    /// or the undo Backspace), we must also swallow its matching keyup so
    /// the target app doesn't see an orphaned key-up event.
    suppress_next_keyup: Option<i32>,
    /// The word just finished by a boundary key (space/enter/tab) that did
    /// *not* match any abbreviation. Kept for exactly one Backspace: if the
    /// very next key is Backspace (deleting that boundary character), the
    /// buffer is restored to this word so correcting a typo - e.g. typing
    /// "bjt", noticing the mistake, backspacing over the space and the "t",
    /// then typing "r" - still gets tracked as "bjr" and can expand.
    /// Cleared by any other key, so it never resurrects a long-abandoned
    /// word.
    pending_word: Option<String>,
    /// When false, the hook only ever passes keys through untouched - no
    /// buffer tracking, no expansion, no undo.
    enabled: bool,
    /// Whether the tray icon is currently shown. Purely informational for
    /// the menu label; the actual add/remove happens via show_tray_icon /
    /// hide_tray_icon. Persisted to config.json as `show_tray_icon`.
    tray_visible: bool,
    /// Whether Textpander is registered to launch when the user logs in.
    /// Kept in sync with the HKCU Run registry key and persisted to
    /// config.json as `start_on_login`.
    start_on_login: bool,
}

static STATE: Mutex<Option<AppState>> = Mutex::new(None);

/// Handles needed to add/remove the tray icon on demand (e.g. hide it from
/// the menu, then bring it back later by relaunching the exe). Kept
/// separate from AppState because these are raw Win32 handles rather than
/// plain owned data.
struct TrayResources {
    hwnd: HWND,
    icon: HICON,
}
// SAFETY: HWND/HICON are just handle values (effectively integers/opaque
// pointers understood by the OS). They're only ever touched from this
// process's single UI/hook thread, guarded by the Mutex below.
unsafe impl Send for TrayResources {}

static TRAY: Mutex<Option<TrayResources>> = Mutex::new(None);

fn to_wide(s: &str) -> Vec<u16> {
    OsStr::new(s)
        .encode_wide()
        .chain(std::iter::once(0))
        .collect()
}

/// Equivalent of the Win32 MAKEINTRESOURCEW macro: turns a numeric resource
/// ID into the special pointer value LoadIconW (and friends) expect when
/// you want "resource by ID" rather than "resource by name string".
fn make_int_resource(id: u16) -> *const u16 {
    id as usize as *const u16
}

/// Loads our embedded icon (resource ID 1, see app.rc) at a specific size.
/// Pass cx = cy = 0 to get the system's default icon size instead.
///
/// LoadImageW is used rather than the older LoadIconW: it's the API
/// Microsoft recommends for loading icons from resources (LoadIconW is kept
/// only for backwards compatibility and can be finicky with modern .ico
/// files that include a PNG-compressed 256x256 frame), and it lets us ask
/// for the exact size the tray actually wants instead of a default that may
/// not match. Falls back to LoadIconW, then to the generic Windows icon, if
/// anything goes wrong - so a build/resource hiccup never crashes the app,
/// it just looks like the plain default icon.
fn load_app_icon(hinstance: HINSTANCE, cx: i32, cy: i32) -> HICON {
    unsafe {
        let flags = if cx == 0 && cy == 0 {
            LR_DEFAULTSIZE
        } else {
            0
        };
        let handle = LoadImageW(hinstance, make_int_resource(1), IMAGE_ICON, cx, cy, flags);
        if !handle.is_null() {
            return handle as HICON;
        }

        let fallback = LoadIconW(hinstance, make_int_resource(1));
        if !fallback.is_null() {
            return fallback;
        }

        LoadIconW(null_mut(), IDI_APPLICATION)
    }
}

/// Root folder for all Textpander config files: `%APPDATA%\Textpander`.
/// Falls back to the folder next to the executable if APPDATA isn't set
/// (unusual on Windows, but keeps the app working rather than crashing).
/// Created on demand if it doesn't exist yet.
fn app_data_dir() -> PathBuf {
    let base = env::var_os("APPDATA")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let mut p = env::current_exe().unwrap_or_else(|_| PathBuf::from("."));
            p.pop();
            p
        });
    let dir = base.join("Textpander");
    let _ = fs::create_dir_all(&dir);
    dir
}

/// Abbreviation -> expansion pairs. Formerly named config.json; kept as
/// separate concern from the app-level settings in config.json below.
fn replacements_path() -> PathBuf {
    app_data_dir().join("replacements.json")
}

/// App-level settings (currently just whether replacements start enabled).
fn settings_path() -> PathBuf {
    app_data_dir().join("config.json")
}

const DEFAULT_REPLACEMENTS: &str = r#"{
    "pls": "please",
    "btw": "by the way",
    "thx": "thanks",
    "idk": "I don't know"
}
"#;

fn ensure_replacements_exists(path: &PathBuf) {
    if !path.exists() {
        let _ = fs::write(path, DEFAULT_REPLACEMENTS);
    }
}

fn load_replacements(path: &PathBuf) -> HashMap<String, String> {
    ensure_replacements_exists(path);
    match fs::read_to_string(path) {
        Ok(text) => match logic::load_config_map(&text) {
            Ok(map) => map,
            Err(e) => {
                show_message(&format!(
                    "replacements.json is not valid JSON:\n{}\n\nNo abbreviations were loaded until this is fixed.",
                    e
                ));
                HashMap::new()
            }
        },
        Err(e) => {
            show_message(&format!("Could not read replacements.json:\n{}", e));
            HashMap::new()
        }
    }
}

/// App-level settings, persisted to config.json (separate from the
/// abbreviation list in replacements.json).
#[derive(Debug, Serialize, Deserialize)]
struct AppSettings {
    /// Whether replacements are active on startup. Kept in sync with the
    /// tray "Enable/Disable replacements" toggle.
    #[serde(default = "default_true")]
    enabled: bool,
    /// Whether the tray icon is shown on startup. Kept in sync with the
    /// tray "Hide tray" action (and relaunching the exe to bring it back).
    #[serde(default = "default_true")]
    show_tray_icon: bool,
    /// Whether Textpander launches automatically when the user logs in.
    /// Kept in sync with the tray "Start on login" toggle.
    #[serde(default)]
    start_on_login: bool,
}

fn default_true() -> bool {
    true
}

impl Default for AppSettings {
    fn default() -> Self {
        AppSettings {
            enabled: true,
            show_tray_icon: true,
            start_on_login: false,
        }
    }
}

const DEFAULT_SETTINGS: &str = "{\n    \"enabled\": true,\n    \"show_tray_icon\": true,\n    \"start_on_login\": false\n}\n";

fn ensure_settings_exists(path: &PathBuf) {
    if !path.exists() {
        let _ = fs::write(path, DEFAULT_SETTINGS);
    }
}

fn load_settings(path: &PathBuf) -> AppSettings {
    ensure_settings_exists(path);
    match fs::read_to_string(path) {
        Ok(text) => match serde_json::from_str(&text) {
            Ok(settings) => settings,
            Err(e) => {
                show_message(&format!(
                    "config.json is not valid JSON:\n{}\n\nUsing default settings until this is fixed.",
                    e
                ));
                AppSettings::default()
            }
        },
        Err(e) => {
            show_message(&format!("Could not read config.json:\n{}", e));
            AppSettings::default()
        }
    }
}

fn save_settings(path: &PathBuf, settings: &AppSettings) {
    if let Ok(text) = serde_json::to_string_pretty(settings) {
        let _ = fs::write(path, text);
    }
}

/// Rebuilds the full AppSettings from the live AppState and writes it out.
/// Used whenever any individual persisted setting changes, so we never
/// clobber the other fields with stale/default values.
fn persist_settings(state: &AppState) {
    let settings = AppSettings {
        enabled: state.enabled,
        show_tray_icon: state.tray_visible,
        start_on_login: state.start_on_login,
    };
    save_settings(&state.settings_path, &settings);
}

/// Adds or removes the HKCU ...\Run value that makes Windows launch
/// Textpander automatically at login. Best-effort: failures (e.g. no
/// permission, though HKCU normally doesn't need any) are silently
/// ignored rather than shown as a message box, since this isn't critical
/// to the app's core function.
fn set_start_on_login(enabled: bool) {
    unsafe {
        let subkey = to_wide("Software\\Microsoft\\Windows\\CurrentVersion\\Run");
        let mut hkey: HKEY = null_mut();
        let status = RegCreateKeyExW(
            HKEY_CURRENT_USER,
            subkey.as_ptr(),
            0,
            null_mut(),
            REG_OPTION_NON_VOLATILE,
            KEY_SET_VALUE,
            null_mut(),
            &mut hkey,
            null_mut(),
        );
        if status != 0 || hkey.is_null() {
            return;
        }

        let value_name = to_wide(APP_UNIQUE_NAME);
        if enabled {
            if let Ok(exe_path) = env::current_exe() {
                // Quoted so the launch command stays correct even if the
                // install path contains spaces.
                let quoted = format!("\"{}\"", exe_path.to_string_lossy());
                let data = to_wide(&quoted);
                let data_len_bytes = (data.len() * size_of::<u16>()) as u32;
                RegSetValueExW(
                    hkey,
                    value_name.as_ptr(),
                    0,
                    REG_SZ,
                    data.as_ptr() as *const u8,
                    data_len_bytes,
                );
            }
        } else {
            // Fine if the value doesn't exist yet - just a no-op.
            RegDeleteValueW(hkey, value_name.as_ptr());
        }

        RegCloseKey(hkey);
    }
}

fn show_message(text: &str) {
    unsafe {
        let wtext = to_wide(text);
        let wtitle = to_wide("Textpander");
        winapi::um::winuser::MessageBoxW(
            null_mut(),
            wtext.as_ptr(),
            wtitle.as_ptr(),
            winapi::um::winuser::MB_OK | winapi::um::winuser::MB_ICONWARNING,
        );
    }
}

/// Entry point, called from main() on Windows.
pub fn run() {
    unsafe {
        // --- Single-instance handling -----------------------------------
        // If an instance is already running, this launch's only job is to
        // wake it up (in case its tray icon was hidden) and then exit
        // immediately, so we never end up with two competing keyboard
        // hooks double-typing everything.
        let mutex_name = to_wide(&format!("Local\\{}_Mutex", APP_UNIQUE_NAME));
        let mutex_handle = CreateMutexW(null_mut(), 0, mutex_name.as_ptr());
        let already_running = !mutex_handle.is_null() && GetLastError() == ERROR_ALREADY_EXISTS;

        let class_name = to_wide("TextpanderHiddenWindowClass");
        let wake_message_name = to_wide(&format!("{}_WakeMessage", APP_UNIQUE_NAME));
        let wake_msg = RegisterWindowMessageW(wake_message_name.as_ptr());
        WAKE_MSG.store(wake_msg, Ordering::SeqCst);

        if already_running {
            let existing = FindWindowW(class_name.as_ptr(), null_mut());
            if !existing.is_null() {
                winapi::um::winuser::PostMessageW(existing, wake_msg, 0, 0);
            }
            // Deliberately not calling CloseHandle(mutex_handle) or doing
            // any further setup - this process's only job here is done.
            return;
        }
        // First/only instance: intentionally never close mutex_handle: it
        // needs to stay held for as long as this process is running, so
        // later launches can detect us. It's released automatically by
        // Windows when the process exits.

        let hinstance = GetModuleHandleW(null_mut());

        // Resource ID 1, embedded via app.rc / build.rs from assets/icon.ico.
        // The tray wants a small icon (SM_CXSMICON, usually 16x16); the
        // window class can use the default/large size.
        let small_icon = load_app_icon(
            hinstance,
            GetSystemMetrics(SM_CXSMICON),
            GetSystemMetrics(SM_CYSMICON),
        );
        let large_icon = load_app_icon(hinstance, 0, 0);

        let wnd_class = WNDCLASSW {
            style: 0,
            lpfnWndProc: Some(wndproc),
            cbClsExtra: 0,
            cbWndExtra: 0,
            hInstance: hinstance,
            hIcon: large_icon,
            hCursor: null_mut(),
            hbrBackground: null_mut(),
            lpszMenuName: null_mut(),
            lpszClassName: class_name.as_ptr(),
        };
        RegisterClassW(&wnd_class);

        let window_title = to_wide("Textpander");
        let hwnd = CreateWindowExW(
            0,
            class_name.as_ptr(),
            window_title.as_ptr(),
            0,
            0,
            0,
            0,
            0,
            winapi::um::winuser::HWND_MESSAGE, // message-only window: invisible, no taskbar entry
            null_mut(),
            hinstance,
            null_mut(),
        );

        let replacements_path = replacements_path();
        let settings_path = settings_path();
        let config = load_replacements(&replacements_path);
        let settings = load_settings(&settings_path);

        // Keep the registry in sync with the persisted preference, in case
        // it was changed by hand in config.json or the Run key was cleared
        // by something else since the last launch.
        set_start_on_login(settings.start_on_login);

        *STATE.lock().unwrap() = Some(AppState {
            config,
            replacements_path,
            settings_path,
            buffer: String::new(),
            last_expansion: None,
            suppress_expansion: false,
            suppress_next_keyup: None,
            pending_word: None,
            enabled: settings.enabled,
            tray_visible: settings.show_tray_icon,
            start_on_login: settings.start_on_login,
        });

        *TRAY.lock().unwrap() = Some(TrayResources {
            hwnd,
            icon: small_icon,
        });
        if settings.show_tray_icon {
            show_tray_icon();
        }

        // Global low-level keyboard hook. Must run on a thread with an
        // active message loop, which is exactly what we run below.
        let hook: HHOOK = SetWindowsHookExW(WH_KEYBOARD_LL, Some(keyboard_hook_proc), hinstance, 0);

        let mut msg: MSG = zeroed();
        while GetMessageW(&mut msg, null_mut(), 0, 0) > 0 {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        if !hook.is_null() {
            UnhookWindowsHookEx(hook);
        }
        remove_tray_icon_visual();
    }
}

unsafe extern "system" fn wndproc(
    hwnd: HWND,
    msg: UINT,
    wparam: WPARAM,
    lparam: LPARAM,
) -> LRESULT {
    if msg == WAKE_MSG.load(Ordering::SeqCst) && msg != 0 {
        // Another launch of the app happened while we're already running:
        // this is our cue to re-show the tray icon if it was hidden.
        show_tray_icon();
        return 0;
    }

    match msg {
        m if m == WM_TRAYICON => {
            let event = lparam as u32;
            if event == WM_RBUTTONUP || event == WM_LBUTTONUP {
                show_tray_menu(hwnd);
            }
            0
        }
        WM_COMMAND => {
            let id = (wparam & 0xffff) as usize;
            match id {
                ID_RELOAD => {
                    reload_config();
                }
                ID_OPEN_CONFIG => {
                    open_replacements();
                }
                ID_OPEN_SETTINGS => {
                    open_settings();
                }
                ID_TOGGLE_STARTUP => {
                    toggle_start_on_login();
                }
                ID_TOGGLE_ENABLED => {
                    toggle_enabled();
                }
                ID_HIDE_TRAY => {
                    hide_tray_icon();
                }
                ID_EXIT => {
                    DestroyWindow(hwnd);
                }
                _ => {}
            }
            0
        }
        WM_DESTROY => {
            PostQuitMessage(0);
            0
        }
        _ => DefWindowProcW(hwnd, msg, wparam, lparam),
    }
}

unsafe fn show_tray_menu(hwnd: HWND) {
    let (enabled, _tray_visible, start_on_login) = {
        let guard = STATE.lock().unwrap();
        match guard.as_ref() {
            Some(s) => (s.enabled, s.tray_visible, s.start_on_login),
            None => (true, true, false),
        }
    };

    let menu = CreatePopupMenu();

    let toggle_text = if enabled {
        "Disable replacements"
    } else {
        "Enable replacements"
    };
    let toggle_label = to_wide(toggle_text);
    let hide_label = to_wide("Hide tray");
    let startup_label = to_wide("Start on login");
    let reload_label = to_wide("Reload replacements");
    let open_label = to_wide("Open replacements.json");
    let open_settings_label = to_wide("Open settings (config.json)");
    let exit_label = to_wide("Exit");

    AppendMenuW(menu, MF_STRING, ID_TOGGLE_ENABLED, toggle_label.as_ptr());
    AppendMenuW(menu, MF_STRING, ID_HIDE_TRAY, hide_label.as_ptr());
    let startup_flags = MF_STRING | if start_on_login { MF_CHECKED } else { MF_UNCHECKED };
    AppendMenuW(menu, startup_flags, ID_TOGGLE_STARTUP, startup_label.as_ptr());
    AppendMenuW(menu, MF_SEPARATOR, 0, null_mut());
    AppendMenuW(menu, MF_STRING, ID_RELOAD, reload_label.as_ptr());
    AppendMenuW(menu, MF_STRING, ID_OPEN_CONFIG, open_label.as_ptr());
    AppendMenuW(
        menu,
        MF_STRING,
        ID_OPEN_SETTINGS,
        open_settings_label.as_ptr(),
    );
    AppendMenuW(menu, MF_SEPARATOR, 0, null_mut());
    AppendMenuW(menu, MF_STRING, ID_EXIT, exit_label.as_ptr());

    let mut pt: POINT = zeroed();
    GetCursorPos(&mut pt);

    // Required so the popup menu closes properly when it loses focus.
    SetForegroundWindow(hwnd);
    TrackPopupMenu(
        menu,
        TPM_RIGHTBUTTON | TPM_BOTTOMALIGN | TPM_LEFTALIGN,
        pt.x,
        pt.y,
        0,
        hwnd,
        null_mut(),
    );
    winapi::um::winuser::PostMessageW(hwnd, winapi::um::winuser::WM_NULL, 0, 0);
    winapi::um::winuser::DestroyMenu(menu);
}

/// Adds the tray icon back (idempotent: safe to call even if already shown).
fn show_tray_icon() {
    let tray_guard = TRAY.lock().unwrap();
    if let Some(tray) = tray_guard.as_ref() {
        unsafe {
            let mut nid: NOTIFYICONDATAW = zeroed();
            nid.cbSize = size_of::<NOTIFYICONDATAW>() as u32;
            nid.hWnd = tray.hwnd;
            nid.uID = TRAY_ID;
            nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
            nid.uCallbackMessage = WM_TRAYICON;
            nid.hIcon = tray.icon;
            let tip = to_wide("Textpander (abbreviation replacement)");
            let n = tip.len().min(nid.szTip.len());
            nid.szTip[..n].copy_from_slice(&tip[..n]);
            // NIM_ADD on an icon that's already present simply fails
            // harmlessly, so this is safe to call unconditionally.
            Shell_NotifyIconW(NIM_ADD, &mut nid);
        }
    }
    drop(tray_guard);
    if let Some(state) = STATE.lock().unwrap().as_mut() {
        state.tray_visible = true;
        persist_settings(state);
    }
}

/// Removes the tray icon's visual presence only - no state/settings
/// changes. Used both by the user-facing hide_tray_icon() below and by
/// run()'s shutdown cleanup (which must NOT persist "hidden" just because
/// the process is exiting).
fn remove_tray_icon_visual() {
    let tray_guard = TRAY.lock().unwrap();
    if let Some(tray) = tray_guard.as_ref() {
        unsafe {
            let mut nid: NOTIFYICONDATAW = zeroed();
            nid.cbSize = size_of::<NOTIFYICONDATAW>() as u32;
            nid.hWnd = tray.hwnd;
            nid.uID = TRAY_ID;
            Shell_NotifyIconW(NIM_DELETE, &mut nid);
        }
    }
}

/// Removes the tray icon in response to the user's "Hide tray" menu
/// action. The app keeps running in the background (hook and
/// replacements still active) - only the visible icon goes away. Can be
/// brought back by relaunching the exe (see the single-instance /
/// WAKE_MSG handling in run() and wndproc), which also persists it as
/// visible again.
fn hide_tray_icon() {
    remove_tray_icon_visual();
    if let Some(state) = STATE.lock().unwrap().as_mut() {
        state.tray_visible = false;
        persist_settings(state);
    }
}

fn toggle_enabled() {
    let mut guard = STATE.lock().unwrap();
    if let Some(state) = guard.as_mut() {
        state.enabled = !state.enabled;
        // Don't carry over any in-progress word/undo state across the
        // pause/resume boundary.
        state.buffer.clear();
        state.last_expansion = None;
        state.suppress_expansion = false;
        state.pending_word = None;
        persist_settings(state);
    }
}

fn toggle_start_on_login() {
    let mut guard = STATE.lock().unwrap();
    if let Some(state) = guard.as_mut() {
        state.start_on_login = !state.start_on_login;
        set_start_on_login(state.start_on_login);
        persist_settings(state);
    }
}

fn reload_config() {
    let mut guard = STATE.lock().unwrap();
    if let Some(state) = guard.as_mut() {
        state.config = load_replacements(&state.replacements_path);
        state.buffer.clear();
        state.last_expansion = None;
        state.suppress_expansion = false;
        state.pending_word = None;
    }
}

fn open_replacements() {
    let guard = STATE.lock().unwrap();
    if let Some(state) = guard.as_ref() {
        unsafe {
            let op = to_wide("open");
            let path = to_wide(state.replacements_path.to_string_lossy().as_ref());
            ShellExecuteW(
                null_mut(),
                op.as_ptr(),
                path.as_ptr(),
                null_mut(),
                null_mut(),
                winapi::um::winuser::SW_SHOWNORMAL as i32,
            );
        }
    }
}

fn open_settings() {
    let guard = STATE.lock().unwrap();
    if let Some(state) = guard.as_ref() {
        unsafe {
            let op = to_wide("open");
            let path = to_wide(state.settings_path.to_string_lossy().as_ref());
            ShellExecuteW(
                null_mut(),
                op.as_ptr(),
                path.as_ptr(),
                null_mut(),
                null_mut(),
                winapi::um::winuser::SW_SHOWNORMAL as i32,
            );
        }
    }
}

fn is_ctrl_down() -> bool {
    unsafe { (GetAsyncKeyState(VK_CONTROL) as u16 & 0x8000) != 0 }
}

fn is_alt_down() -> bool {
    unsafe { (GetAsyncKeyState(VK_MENU) as u16 & 0x8000) != 0 }
}

fn is_capslock_on() -> bool {
    // The toggle bit is fine to read via GetKeyState (it's a global toggle,
    // not tied to a specific thread's input queue).
    unsafe { (GetKeyState(VK_CAPITAL) as u16 & 0x0001) != 0 }
}

/// Resolves the actual Unicode character a key produces, honoring the real
/// keyboard layout of the focused window (Shift, CapsLock, and AltGr - e.g.
/// '@' on many European/AZERTY layouts is AltGr + a digit key). We build the
/// key-state array ourselves from GetAsyncKeyState rather than calling
/// GetKeyboardState, for the same reason described near is_ctrl_down: this
/// hook's thread doesn't own the input queue, so thread-scoped state can be
/// stale or simply never populated.
fn char_from_vk(vk: i32, scan_code: u32) -> Option<char> {
    unsafe {
        let mut keyboard_state = [0u8; 256];
        for vk_code in [
            VK_SHIFT,
            VK_LSHIFT,
            VK_RSHIFT,
            VK_CONTROL,
            VK_LCONTROL,
            VK_RCONTROL,
            VK_MENU,
            VK_LMENU,
            VK_RMENU,
        ] {
            let pressed = (GetAsyncKeyState(vk_code) as u16 & 0x8000) != 0;
            keyboard_state[vk_code as usize] = if pressed { 0x80 } else { 0 };
        }
        keyboard_state[VK_CAPITAL as usize] = if is_capslock_on() { 1 } else { 0 };

        let foreground = GetForegroundWindow();
        let thread_id = GetWindowThreadProcessId(foreground, null_mut());
        let hkl = GetKeyboardLayout(thread_id);

        let mut buf = [0u16; 8];
        let result = ToUnicodeEx(
            vk as u32,
            scan_code,
            keyboard_state.as_ptr(),
            buf.as_mut_ptr(),
            buf.len() as i32,
            0,
            hkl,
        );

        if result < 0 {
            // Dead key (an accent waiting to combine with the next letter,
            // e.g. on some layouts). This call leaves the thread-local
            // dead-key state primed; flush it immediately so we don't
            // interfere with the real composition the target app performs
            // on its own. We don't treat this as a typed character.
            let mut flush_buf = [0u16; 8];
            ToUnicodeEx(
                vk as u32,
                scan_code,
                keyboard_state.as_ptr(),
                flush_buf.as_mut_ptr(),
                flush_buf.len() as i32,
                0,
                hkl,
            );
            return None;
        }

        if result <= 0 {
            return None;
        }

        char::from_u32(buf[0] as u32)
    }
}

/// The set of virtual-key codes we deliberately ignore for the purposes of
/// buffer tracking (modifier keys), because they routinely precede a letter
/// key (e.g. Shift then a letter) and must not reset context.
fn is_ignored_modifier(vk: i32) -> bool {
    matches!(
        vk,
        VK_SHIFT
            | VK_LSHIFT
            | VK_RSHIFT
            | VK_CONTROL
            | VK_LCONTROL
            | VK_RCONTROL
            | VK_MENU
            | VK_LMENU
            | VK_RMENU
            | VK_LWIN
            | VK_RWIN
            | VK_CAPITAL
    )
}

unsafe extern "system" fn keyboard_hook_proc(
    ncode: i32,
    wparam: WPARAM,
    lparam: LPARAM,
) -> LRESULT {
    if ncode == HC_ACTION as i32 {
        let kb = &*(lparam as *const KBDLLHOOKSTRUCT);
        // Ignore events we generated ourselves via SendInput, to avoid
        // feedback loops re-entering this same hook.
        if kb.flags & LLKHF_INJECTED == 0 {
            let vk = kb.vkCode as i32;
            let is_keydown = wparam as u32 == WM_KEYDOWN || wparam as u32 == WM_SYSKEYDOWN;
            let is_keyup = wparam as u32 == WM_KEYUP || wparam as u32 == WM_SYSKEYUP;

            if is_keydown {
                if handle_keydown(vk, kb.scanCode) {
                    // We handled this key ourselves (either replaced it with
                    // an expansion, or undid one) - swallow the real event
                    // so the app doesn't also receive the original keystroke.
                    return 1;
                }
            } else if is_keyup {
                if should_swallow_keyup(vk) {
                    return 1;
                }
            }
        }
    }
    CallNextHookEx(null_mut(), ncode, wparam, lparam)
}

fn should_swallow_keyup(vk: i32) -> bool {
    let mut guard = STATE.lock().unwrap();
    if let Some(state) = guard.as_mut() {
        if state.suppress_next_keyup == Some(vk) {
            state.suppress_next_keyup = None;
            return true;
        }
    }
    false
}

/// Returns true if this keydown was fully handled by us and must be
/// swallowed (not delivered to the focused app).
fn handle_keydown(vk: i32, scan_code: u32) -> bool {
    let mut guard = STATE.lock().unwrap();
    let state = match guard.as_mut() {
        Some(s) => s,
        None => return false,
    };

    if !state.enabled {
        // Replacements paused via the tray menu: pass everything through
        // untouched. (The buffer/undo state is already cleared by
        // toggle_enabled when this was switched off.)
        return false;
    }

    if is_ignored_modifier(vk) {
        return false;
    }

    let ctrl = is_ctrl_down();
    let alt = is_alt_down();
    // A "pure" Ctrl-only or Alt-only chord is a real keyboard shortcut
    // (Ctrl+Backspace = delete previous word, Alt+Backspace = Undo in many
    // apps, Ctrl+C, etc.) and must never be intercepted or fed into our
    // synthetic-backspace logic - injecting plain Backspace keystrokes while
    // the real Ctrl is still held gets reinterpreted as Ctrl+Backspace by
    // the target app, deleting far more than intended.
    //
    // AltGr (used to type symbols like '@' on many European layouts) shows
    // up at this level as Ctrl+Alt held *together*, which this check
    // deliberately lets through to the character-handling code below.
    if (ctrl && !alt) || (alt && !ctrl) {
        state.buffer.clear();
        state.last_expansion = None;
        state.suppress_expansion = false;
        state.pending_word = None;
        return false;
    }

    if vk == VK_BACK {
        // Backspace pressed right after an expansion: undo it.
        if let Some(last) = state.last_expansion.take() {
            state.buffer = last.typed.clone();
            state.suppress_expansion = true;
            state.suppress_next_keyup = Some(VK_BACK);
            drop(guard);
            perform_undo(&last);
            return true;
        }
        // Backspace pressed right after a boundary key that did *not*
        // trigger an expansion (e.g. "pld" + space, no match): this
        // Backspace is deleting that boundary character on screen, so
        // resume tracking from the word as it stood right before it,
        // instead of starting over from an empty buffer. This is what
        // makes "type pld, notice the typo, backspace twice, type s"
        // still resolve to "pls" -> please.
        if let Some(pending) = state.pending_word.take() {
            state.buffer = pending;
            return false;
        }
        state.buffer.pop();
        return false;
    }

    // Any key other than Backspace closes the "undo window" and abandons
    // any pending (unmatched) word - it's genuinely a new context now.
    state.last_expansion = None;
    state.pending_word = None;

    if vk == VK_SPACE || vk == VK_RETURN || vk == VK_TAB {
        // One-shot: if this boundary key comes right after an undo with no
        // letters typed in between, don't re-expand the same occurrence.
        let skip_due_to_undo = std::mem::replace(&mut state.suppress_expansion, false);
        if !skip_due_to_undo && !state.buffer.is_empty() {
            if let Some(expansion) = logic::expand(&state.config, &state.buffer) {
                let typed = std::mem::take(&mut state.buffer);
                let abbr_len = typed.chars().count();
                state.last_expansion = Some(LastExpansion {
                    typed,
                    expansion: expansion.clone(),
                });
                state.suppress_next_keyup = Some(vk);
                drop(guard);
                perform_replacement(abbr_len, &expansion, vk);
                // We swallow the boundary key ourselves and re-type it as
                // part of the replacement, so the caller must not let the
                // original keystroke through too (that was the cause of
                // the double-space bug).
                return true;
            }
        }
        // No match (or a one-shot-suppressed undo occurrence): remember
        // this word for exactly one Backspace, in case the user steps
        // back in to correct it.
        state.pending_word = if state.buffer.is_empty() {
            None
        } else {
            Some(std::mem::take(&mut state.buffer))
        };
        state.buffer.clear();
        return false;
    }

    state.suppress_expansion = false;

    // Anything else: resolve the actual character this key produces,
    // honoring the real keyboard layout (Shift, CapsLock, AltGr), so
    // abbreviations can contain letters, digits, or symbols like '@' -
    // not just plain A-Z. Keys that don't produce a character (arrows,
    // function keys, digits-as-shortcuts, etc.) break the word context.
    if let Some(ch) = char_from_vk(vk, scan_code) {
        if state.buffer.len() < MAX_BUFFER_LEN {
            state.buffer.push(ch);
        } else {
            state.buffer.clear();
        }
    } else {
        state.buffer.clear();
    }
    false
}

/// Deletes the typed abbreviation, then types the expansion followed by the
/// boundary key (space / enter / tab) that triggered it. The real boundary
/// keystroke is swallowed by the hook, so this is the only copy of it.
fn perform_replacement(abbr_len: usize, expansion: &str, boundary_vk: i32) {
    let mut inputs: Vec<INPUT> = Vec::new();

    for _ in 0..abbr_len {
        push_vk_input(&mut inputs, VK_BACK as u16, false);
        push_vk_input(&mut inputs, VK_BACK as u16, true);
    }

    // Type the expansion as Unicode, so accented characters work regardless
    // of keyboard layout.
    for unit in expansion.encode_utf16() {
        push_unicode_input(&mut inputs, unit, false);
        push_unicode_input(&mut inputs, unit, true);
    }

    push_vk_input(&mut inputs, boundary_vk as u16, false);
    push_vk_input(&mut inputs, boundary_vk as u16, true);

    unsafe {
        SendInput(
            inputs.len() as u32,
            inputs.as_mut_ptr(),
            size_of::<INPUT>() as i32,
        );
    }
}

/// Deletes the expansion text plus the boundary key that followed it, then
/// retypes the original abbreviation exactly as the user typed it.
fn perform_undo(last: &LastExpansion) {
    let mut inputs: Vec<INPUT> = Vec::new();

    let delete_count = last.expansion.encode_utf16().count() + 1; // +1 for the boundary char
    for _ in 0..delete_count {
        push_vk_input(&mut inputs, VK_BACK as u16, false);
        push_vk_input(&mut inputs, VK_BACK as u16, true);
    }

    for unit in last.typed.encode_utf16() {
        push_unicode_input(&mut inputs, unit, false);
        push_unicode_input(&mut inputs, unit, true);
    }

    unsafe {
        SendInput(
            inputs.len() as u32,
            inputs.as_mut_ptr(),
            size_of::<INPUT>() as i32,
        );
    }
}

fn push_vk_input(inputs: &mut Vec<INPUT>, vk: u16, key_up: bool) {
    unsafe {
        let mut input: INPUT = zeroed();
        input.type_ = INPUT_KEYBOARD;
        let mut ki: KEYBDINPUT = zeroed();
        ki.wVk = vk;
        ki.wScan = 0;
        ki.dwFlags = if key_up { KEYEVENTF_KEYUP } else { 0 };
        ki.time = 0;
        ki.dwExtraInfo = 0;
        *input.u.ki_mut() = ki;
        inputs.push(input);
    }
}

fn push_unicode_input(inputs: &mut Vec<INPUT>, code_unit: u16, key_up: bool) {
    unsafe {
        let mut input: INPUT = zeroed();
        input.type_ = INPUT_KEYBOARD;
        let mut ki: KEYBDINPUT = zeroed();
        ki.wVk = 0;
        ki.wScan = code_unit;
        ki.dwFlags = KEYEVENTF_UNICODE | if key_up { KEYEVENTF_KEYUP } else { 0 };
        ki.time = 0;
        ki.dwExtraInfo = 0;
        *input.u.ki_mut() = ki;
        inputs.push(input);
    }
}
