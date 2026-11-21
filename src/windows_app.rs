#![cfg(windows)]
// All Win32 interop lives in this file. The pure expansion logic (case
// matching, config parsing) lives in logic.rs and has no dependency on
// Windows, so it can be unit-tested on any platform.
//
// Threading model: everything here runs on ONE thread (the one that owns the
// message loop). The low-level hooks are called back on that same thread, so
// STATE is never contended, but it is NOT re-entrant: never hold the STATE
// lock while calling something that can pump messages (MessageBox,
// ShellExecute, TrackPopupMenu...). A hook would fire inside that nested
// loop, try to lock STATE again and deadlock the whole app.

use crate::logic;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::mem::{self, size_of, zeroed};
use std::os::windows::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};

use winapi::shared::minwindef::{HINSTANCE, HKEY, LPARAM, LRESULT, UINT, WPARAM};
use winapi::shared::windef::{HHOOK, HICON, HMENU, HWND, POINT};
use winapi::shared::winerror::ERROR_ALREADY_EXISTS;
use winapi::um::errhandlingapi::GetLastError;
use winapi::um::libloaderapi::GetModuleHandleW;
use winapi::um::shellapi::{
    ShellExecuteW, Shell_NotifyIconW, NIF_ICON, NIF_MESSAGE, NIF_TIP, NIM_ADD, NIM_DELETE,
    NIM_MODIFY, NOTIFYICONDATAW,
};
use winapi::um::synchapi::CreateMutexW;
use winapi::um::winnt::{KEY_SET_VALUE, REG_BINARY, REG_OPTION_NON_VOLATILE, REG_SZ};
use winapi::um::winreg::{
    RegCloseKey, RegCreateKeyExW, RegDeleteValueW, RegSetValueExW, HKEY_CURRENT_USER,
};
use winapi::um::winuser::{
    AppendMenuW, CallNextHookEx, ChangeWindowMessageFilterEx, CreatePopupMenu, CreateWindowExW,
    DefWindowProcW, DestroyMenu, DestroyWindow, DispatchMessageW, FindWindowW, GetAsyncKeyState,
    GetCursorPos, GetForegroundWindow, GetKeyState, GetKeyboardLayout, GetMessageW,
    GetSystemMetrics, GetWindowThreadProcessId, LoadIconW, LoadImageW, MapVirtualKeyExW,
    MessageBoxW, PostMessageW, PostQuitMessage, RegisterClassW, RegisterWindowMessageW, SendInput,
    SetForegroundWindow, SetTimer, SetWindowsHookExW, ToUnicodeEx, TrackPopupMenu,
    TranslateMessage, UnhookWindowsHookEx, HC_ACTION, IDI_APPLICATION, IMAGE_ICON, INPUT,
    INPUT_KEYBOARD, KBDLLHOOKSTRUCT, KEYBDINPUT, KEYEVENTF_KEYUP, KEYEVENTF_UNICODE,
    LLKHF_INJECTED, LR_DEFAULTSIZE, MAPVK_VK_TO_CHAR, MB_ICONINFORMATION, MB_ICONWARNING, MB_OK,
    MF_CHECKED, MF_SEPARATOR, MF_STRING, MF_UNCHECKED, MSG, SM_CXSMICON, SM_CYSMICON,
    SW_SHOWNORMAL, TPM_BOTTOMALIGN, TPM_LEFTALIGN, TPM_RIGHTBUTTON, VK_BACK, VK_CAPITAL,
    VK_CONTROL, VK_LCONTROL, VK_LMENU, VK_LSHIFT, VK_LWIN, VK_MENU, VK_RCONTROL, VK_RETURN,
    VK_RMENU, VK_RSHIFT, VK_RWIN, VK_SHIFT, VK_TAB, WH_KEYBOARD_LL, WH_MOUSE_LL, WM_APP,
    WM_COMMAND, WM_DESTROY, WM_KEYDOWN, WM_KEYUP, WM_LBUTTONDOWN, WM_LBUTTONUP, WM_MBUTTONDOWN,
    WM_NULL, WM_RBUTTONDOWN, WM_RBUTTONUP, WM_SYSKEYDOWN, WM_SYSKEYUP, WM_TIMER, WNDCLASSW,
    WS_EX_TOOLWINDOW, WS_POPUP,
};

const WM_TRAYICON: UINT = WM_APP + 1;
const ID_RELOAD: usize = 1001;
const ID_OPEN_CONFIG: usize = 1002;
const ID_EXIT: usize = 1003;
const ID_TOGGLE_ENABLED: usize = 1004;
const ID_HIDE_TRAY: usize = 1005;
const ID_OPEN_SETTINGS: usize = 1006;
const ID_TOGGLE_STARTUP: usize = 1007;
const ID_ABOUT: usize = 1008;
const TRAY_ID: u32 = 1;
const TRAY_WATCHDOG_TIMER: usize = 1;
const MAX_BUFFER_LEN: usize = 64;

/// Not exposed by winapi 0.3 (Win32 value for ChangeWindowMessageFilterEx).
const MSGFLT_ALLOW: u32 = 1;

const ABOUT_URL: &str = "https://github.com/Alfakynz/Textpander";

/// Base for the single-instance mutex, the registered "wake up" window
/// message and the registry value name. Kept unique to avoid collisions.
const APP_UNIQUE_NAME: &str = "Textpander_Alfakynz";

const RUN_KEY: &str = "Software\\Microsoft\\Windows\\CurrentVersion\\Run";
const STARTUP_APPROVED_KEY: &str =
    "Software\\Microsoft\\Windows\\CurrentVersion\\Explorer\\StartupApproved\\Run";

/// Window message posted by a second launch to the running instance, so it
/// re-shows its tray icon (and then the second launch exits).
static WAKE_MSG: AtomicU32 = AtomicU32::new(0);

/// "TaskbarCreated": broadcast by Windows whenever Explorer (re)starts. An
/// Explorer restart silently wipes every tray icon, so we must re-add ours
/// when this arrives.
static TASKBAR_CREATED_MSG: AtomicU32 = AtomicU32::new(0);

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// Remembers the most recent expansion so a Backspace pressed immediately
/// afterwards can undo it (restoring exactly what was typed).
struct LastExpansion {
    typed: String,
    /// Number of Backspaces needed to erase the expansion + its boundary key.
    delete_len: usize,
}

struct AppState {
    config: HashMap<String, String>,
    replacements_path: PathBuf,
    settings_path: PathBuf,
    /// Characters that trigger an expansion attempt (Enter and Tab always do).
    boundary_chars: Vec<char>,
    enabled: bool,
    tray_visible: bool,
    start_on_login: bool,
    /// See `AppSettings::clear_autocomplete`.
    clear_autocomplete: bool,

    // Win32 handles, stored as integers so the struct is naturally `Send`
    // (they are only ever used from the single UI thread).
    hwnd: usize,
    tray_icon: usize,

    // --- typing tracking (see `reset_typing`) ---
    buffer: String,
    last_expansion: Option<LastExpansion>,
    /// Set right after an undo so the next boundary key doesn't immediately
    /// re-expand the same occurrence. One-shot.
    suppress_expansion: bool,
    /// The word finished by a boundary key that matched nothing. Kept for
    /// exactly one Backspace so that fixing a typo ("bjt" + space, then
    /// backspace x2, then "r") still ends up tracked as "bjr".
    pending_word: Option<String>,
    /// Set after a dead key (accent waiting to combine). The *next* key must
    /// not go through ToUnicodeEx either, or it would consume the pending
    /// composition the target app is still waiting to finish.
    skip_next_char_resolution: bool,

    /// When we swallow a keydown ourselves we must swallow its keyup too.
    suppress_next_keyup: Option<i32>,
    /// Last foreground window seen by the hook. A change means the user
    /// moved elsewhere, so any half-typed word is stale.
    last_foreground: usize,
}

impl AppState {
    /// Forgets any in-progress word / undo / dead-key context.
    fn reset_typing(&mut self) {
        self.buffer.clear();
        self.last_expansion = None;
        self.suppress_expansion = false;
        self.pending_word = None;
        self.skip_next_char_resolution = false;
    }
}

static STATE: Mutex<Option<AppState>> = Mutex::new(None);

/// Locks STATE, ignoring poisoning (a panic elsewhere must not turn every
/// later keystroke into another panic inside an `extern "system"` callback).
fn lock_state() -> MutexGuard<'static, Option<AppState>> {
    STATE.lock().unwrap_or_else(PoisonError::into_inner)
}

fn with_state<R>(f: impl FnOnce(&mut AppState) -> R) -> Option<R> {
    lock_state().as_mut().map(f)
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

fn to_wide_os(s: &OsStr) -> Vec<u16> {
    s.encode_wide().chain(std::iter::once(0)).collect()
}

fn to_wide(s: &str) -> Vec<u16> {
    to_wide_os(OsStr::new(s))
}

/// Equivalent of the Win32 MAKEINTRESOURCEW macro.
fn make_int_resource(id: u16) -> *const u16 {
    id as usize as *const u16
}

fn message_box(title: &str, text: &str, icon: UINT) {
    let (wtitle, wtext) = (to_wide(title), to_wide(text));
    unsafe {
        MessageBoxW(null_mut(), wtext.as_ptr(), wtitle.as_ptr(), MB_OK | icon);
    }
}

fn show_message(text: &str) {
    message_box("Textpander", text, MB_ICONWARNING);
}

fn show_about_window() {
    let text = format!(
        "Textpander {}\n\nMade by Alfakynz.\n\n{}",
        env!("CARGO_PKG_VERSION"),
        ABOUT_URL
    );
    message_box("About Textpander", &text, MB_ICONINFORMATION);
}

fn is_down(vk: i32) -> bool {
    unsafe { (GetAsyncKeyState(vk) as u16 & 0x8000) != 0 }
}

/// Loads our embedded icon (resource ID 1, see app.rc) at a given size
/// (0, 0 = system default size). Falls back to LoadIconW, then to the
/// generic Windows icon, so a resource hiccup never crashes the app.
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

/// Opens a file with its default app, falling back to Notepad when no
/// association exists for it.
fn open_in_default_app(path: &Path) {
    let (op, wpath) = (to_wide("open"), to_wide_os(path.as_os_str()));
    let result = unsafe {
        ShellExecuteW(
            null_mut(),
            op.as_ptr(),
            wpath.as_ptr(),
            null_mut(),
            null_mut(),
            SW_SHOWNORMAL,
        )
    };
    // ShellExecute returns a value <= 32 on failure.
    if (result as isize) <= 32 {
        let _ = Command::new("notepad").arg(path).spawn();
    }
}

// ---------------------------------------------------------------------------
// Config files
// ---------------------------------------------------------------------------

/// `%APPDATA%\Textpander` (next to the exe if APPDATA is missing), created
/// on demand.
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

const DEFAULT_REPLACEMENTS: &str = r#"{
    "pls": "please",
    "btw": "by the way",
    "thx": "thanks",
    "idk": "I don't know"
}
"#;

const DEFAULT_SETTINGS: &str = r#"{
    "enabled": true,
    "show_tray_icon": true,
    "start_on_login": false,
    "clear_autocomplete": true,
    "characters": [" ", ",", ".", ";", ":", "!", "?", ")", "\"", "\n"]
}
"#;

/// App-level settings, persisted to config.json (separate from the
/// abbreviation list in replacements.json).
#[derive(Debug, Serialize, Deserialize)]
struct AppSettings {
    #[serde(default = "default_true")]
    enabled: bool,
    #[serde(default = "default_true")]
    show_tray_icon: bool,
    #[serde(default)]
    start_on_login: bool,
    /// Browser address bars (and similar fields) inline-autocomplete as you
    /// type: after "ca" they may show "ca" + a *selected* suggestion. The
    /// first Backspace then deletes that suggestion instead of a letter, and
    /// the expansion ends up with a leftover character ("cça"). When true,
    /// a throw-away character is typed first so any selection is replaced,
    /// then deleted along with the abbreviation. Set to false to disable.
    #[serde(default = "default_true")]
    clear_autocomplete: bool,
    /// Characters that trigger an expansion attempt, e.g. [" ", ",", ")"].
    /// Only the first character of each entry is used.
    #[serde(default = "default_boundary_characters")]
    characters: Vec<String>,
}

fn default_true() -> bool {
    true
}

fn default_boundary_characters() -> Vec<String> {
    vec![" ".to_string()]
}

impl Default for AppSettings {
    fn default() -> Self {
        AppSettings {
            enabled: true,
            show_tray_icon: true,
            start_on_login: false,
            clear_autocomplete: true,
            characters: default_boundary_characters(),
        }
    }
}

fn boundary_chars_from_settings(settings: &AppSettings) -> Vec<char> {
    settings
        .characters
        .iter()
        .filter_map(|s| s.chars().next())
        .collect()
}

/// Reads a config file (creating it with defaults if missing) and strips a
/// UTF-8 BOM, which some editors add and serde_json would reject.
fn read_or_create(path: &Path, default: &str, name: &str) -> Result<String, String> {
    if !path.exists() {
        let _ = fs::write(path, default);
    }
    fs::read_to_string(path)
        .map(|t| t.trim_start_matches('\u{feff}').to_owned())
        .map_err(|e| format!("Could not read {name}:\n{e}"))
}

fn load_replacements(path: &Path) -> Result<HashMap<String, String>, String> {
    let text = read_or_create(path, DEFAULT_REPLACEMENTS, "replacements.json")?;
    logic::load_config_map(&text).map_err(|e| format!("replacements.json is not valid JSON:\n{e}"))
}

fn load_settings(path: &Path) -> Result<AppSettings, String> {
    let text = read_or_create(path, DEFAULT_SETTINGS, "config.json")?;
    serde_json::from_str(&text).map_err(|e| format!("config.json is not valid JSON:\n{e}"))
}

/// Writes through a temp file + rename so a crash mid-write can never leave
/// a truncated config.json behind.
fn persist_settings(state: &AppState) {
    let settings = AppSettings {
        enabled: state.enabled,
        show_tray_icon: state.tray_visible,
        start_on_login: state.start_on_login,
        clear_autocomplete: state.clear_autocomplete,
        characters: state.boundary_chars.iter().map(|c| c.to_string()).collect(),
    };
    let Ok(text) = serde_json::to_string_pretty(&settings) else {
        return;
    };
    let tmp = state.settings_path.with_extension("json.tmp");
    if fs::write(&tmp, text).is_err() || fs::rename(&tmp, &state.settings_path).is_err() {
        let _ = fs::remove_file(&tmp);
    }
}

// ---------------------------------------------------------------------------
// Start on login (registry)
// ---------------------------------------------------------------------------

/// Minimal RAII wrapper around an open HKCU registry key.
struct RegKey(HKEY);

impl RegKey {
    fn open(subkey: &str) -> Option<Self> {
        let subkey = to_wide(subkey);
        let mut hkey: HKEY = null_mut();
        let status = unsafe {
            RegCreateKeyExW(
                HKEY_CURRENT_USER,
                subkey.as_ptr(),
                0,
                null_mut(),
                REG_OPTION_NON_VOLATILE,
                KEY_SET_VALUE,
                null_mut(),
                &mut hkey,
                null_mut(),
            )
        };
        (status == 0 && !hkey.is_null()).then_some(RegKey(hkey))
    }

    fn set(&self, name: &str, kind: u32, data: &[u8]) {
        let name = to_wide(name);
        unsafe {
            RegSetValueExW(
                self.0,
                name.as_ptr(),
                0,
                kind,
                data.as_ptr(),
                data.len() as u32,
            );
        }
    }

    /// Fine if the value doesn't exist: it's just a no-op.
    fn delete(&self, name: &str) {
        let name = to_wide(name);
        unsafe {
            RegDeleteValueW(self.0, name.as_ptr());
        }
    }
}

impl Drop for RegKey {
    fn drop(&mut self) {
        unsafe {
            RegCloseKey(self.0);
        }
    }
}

/// Adds/removes the HKCU Run value that launches Textpander at login, and
/// keeps the matching "StartupApproved" entry in sync. That second entry is
/// what Task Manager's Startup tab toggles; without an explicit "enabled"
/// value, Windows can silently skip a Run entry added by hand. (Its 12-byte
/// format - first byte 0x02 = enabled - is undocumented but well known.)
/// Best-effort: failures are ignored, this isn't critical to the core feature.
fn set_start_on_login(enabled: bool) {
    if let Some(run) = RegKey::open(RUN_KEY) {
        if !enabled {
            run.delete(APP_UNIQUE_NAME);
        } else if let Ok(exe) = env::current_exe() {
            // Quoted so paths containing spaces still work.
            let command = format!("\"{}\"", exe.to_string_lossy());
            let bytes: Vec<u8> = to_wide(&command)
                .iter()
                .flat_map(|u| u.to_le_bytes())
                .collect();
            run.set(APP_UNIQUE_NAME, REG_SZ, &bytes);
        }
    }
    if let Some(approved) = RegKey::open(STARTUP_APPROVED_KEY) {
        if enabled {
            approved.set(
                APP_UNIQUE_NAME,
                REG_BINARY,
                &[0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            );
        } else {
            approved.delete(APP_UNIQUE_NAME);
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point + window procedure
// ---------------------------------------------------------------------------

pub fn run() {
    unsafe {
        // Single instance: a second launch only wakes the first one (so a
        // hidden tray icon comes back) and exits, so two competing keyboard
        // hooks never double-type everything. The mutex handle is never
        // closed on purpose: it must live as long as this process.
        let mutex_name = to_wide(&format!("Local\\{}_Mutex", APP_UNIQUE_NAME));
        let mutex_handle = CreateMutexW(null_mut(), 0, mutex_name.as_ptr());
        let already_running = !mutex_handle.is_null() && GetLastError() == ERROR_ALREADY_EXISTS;

        let class_name = to_wide("TextpanderHiddenWindowClass");
        let wake_msg =
            RegisterWindowMessageW(to_wide(&format!("{}_WakeMessage", APP_UNIQUE_NAME)).as_ptr());
        WAKE_MSG.store(wake_msg, Ordering::SeqCst);
        let taskbar_created_msg = RegisterWindowMessageW(to_wide("TaskbarCreated").as_ptr());
        TASKBAR_CREATED_MSG.store(taskbar_created_msg, Ordering::SeqCst);

        if already_running {
            let existing = FindWindowW(class_name.as_ptr(), null_mut());
            if !existing.is_null() {
                PostMessageW(existing, wake_msg, 0, 0);
            }
            return;
        }

        let hinstance = GetModuleHandleW(null_mut());
        let small_icon = load_app_icon(
            hinstance,
            GetSystemMetrics(SM_CXSMICON),
            GetSystemMetrics(SM_CYSMICON),
        );

        let wnd_class = WNDCLASSW {
            style: 0,
            lpfnWndProc: Some(wndproc),
            cbClsExtra: 0,
            cbWndExtra: 0,
            hInstance: hinstance,
            hIcon: load_app_icon(hinstance, 0, 0),
            hCursor: null_mut(),
            hbrBackground: null_mut(),
            lpszMenuName: null_mut(),
            lpszClassName: class_name.as_ptr(),
        };
        RegisterClassW(&wnd_class);

        let hwnd = CreateWindowExW(
            WS_EX_TOOLWINDOW,
            class_name.as_ptr(),
            to_wide("Textpander").as_ptr(),
            WS_POPUP,
            0,
            0,
            0,
            0,
            null_mut(),
            null_mut(),
            hinstance,
            null_mut(),
        );
        if hwnd.is_null() {
            show_message("Could not create the Textpander window.");
            return;
        }
        ChangeWindowMessageFilterEx(hwnd, taskbar_created_msg, MSGFLT_ALLOW, null_mut());

        // Load everything BEFORE installing the hooks / filling STATE.
        let replacements_path = app_data_dir().join("replacements.json");
        let settings_path = app_data_dir().join("config.json");
        let config = load_replacements(&replacements_path).unwrap_or_else(|e| {
            show_message(&format!(
                "{e}\n\nNo abbreviations were loaded until this is fixed."
            ));
            HashMap::new()
        });
        let settings = load_settings(&settings_path).unwrap_or_else(|e| {
            show_message(&format!(
                "{e}\n\nUsing default settings until this is fixed."
            ));
            AppSettings::default()
        });

        // Keep the registry in sync with the persisted preference.
        set_start_on_login(settings.start_on_login);

        *lock_state() = Some(AppState {
            config,
            replacements_path,
            settings_path,
            boundary_chars: boundary_chars_from_settings(&settings),
            enabled: settings.enabled,
            tray_visible: settings.show_tray_icon,
            start_on_login: settings.start_on_login,
            clear_autocomplete: settings.clear_autocomplete,
            hwnd: hwnd as usize,
            tray_icon: small_icon as usize,
            buffer: String::new(),
            last_expansion: None,
            suppress_expansion: false,
            pending_word: None,
            skip_next_char_resolution: false,
            suppress_next_keyup: None,
            last_foreground: 0,
        });

        if settings.show_tray_icon {
            add_tray_icon();
        }
        // Always running (cheap): re-adds the icon if the shell lost it, and
        // also covers the case where the icon is un-hidden later.
        SetTimer(hwnd, TRAY_WATCHDOG_TIMER, 3000, None);

        // Global low-level hooks; they need the message loop below.
        let keyboard_hook: HHOOK =
            SetWindowsHookExW(WH_KEYBOARD_LL, Some(keyboard_hook_proc), hinstance, 0);
        if keyboard_hook.is_null() {
            show_message("Could not install the keyboard hook. Textpander will exit.");
            remove_tray_icon_visual();
            return;
        }
        // Mouse clicks move the caret, so they invalidate the typed word.
        let mouse_hook: HHOOK = SetWindowsHookExW(WH_MOUSE_LL, Some(mouse_hook_proc), hinstance, 0);

        let mut msg: MSG = zeroed();
        while GetMessageW(&mut msg, null_mut(), 0, 0) > 0 {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        UnhookWindowsHookEx(keyboard_hook);
        if !mouse_hook.is_null() {
            UnhookWindowsHookEx(mouse_hook);
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
    if msg != 0 && msg == WAKE_MSG.load(Ordering::SeqCst) {
        // Another launch happened: bring the tray icon back if it was hidden.
        show_tray_icon();
        return 0;
    }
    if msg != 0 && msg == TASKBAR_CREATED_MSG.load(Ordering::SeqCst) {
        // Explorer restarted and wiped our icon. Re-add it, but only if the
        // user didn't deliberately hide it.
        if with_state(|s| s.tray_visible).unwrap_or(true) {
            add_tray_icon();
        }
        return 0;
    }

    match msg {
        WM_TRAYICON => {
            let event = lparam as u32;
            if event == WM_RBUTTONUP || event == WM_LBUTTONUP {
                show_tray_menu(hwnd);
            }
            0
        }
        WM_COMMAND => {
            match wparam & 0xffff {
                ID_RELOAD => reload_config(),
                ID_OPEN_CONFIG => open_config_file(|s| s.replacements_path.clone()),
                ID_OPEN_SETTINGS => open_config_file(|s| s.settings_path.clone()),
                ID_TOGGLE_STARTUP => toggle_start_on_login(),
                ID_TOGGLE_ENABLED => toggle_enabled(),
                ID_HIDE_TRAY => hide_tray_icon(),
                ID_ABOUT => show_about_window(),
                ID_EXIT => {
                    DestroyWindow(hwnd);
                }
                _ => {}
            }
            0
        }
        WM_TIMER if wparam == TRAY_WATCHDOG_TIMER => {
            ensure_tray_icon();
            0
        }
        WM_DESTROY => {
            PostQuitMessage(0);
            0
        }
        _ => DefWindowProcW(hwnd, msg, wparam, lparam),
    }
}

// ---------------------------------------------------------------------------
// Tray icon + menu
// ---------------------------------------------------------------------------

unsafe fn append_item(menu: HMENU, flags: UINT, id: usize, text: &str) {
    let wide = to_wide(text);
    AppendMenuW(menu, flags, id, wide.as_ptr());
}

unsafe fn show_tray_menu(hwnd: HWND) {
    let (enabled, start_on_login) =
        with_state(|s| (s.enabled, s.start_on_login)).unwrap_or((true, false));

    let menu = CreatePopupMenu();
    let toggle_text = if enabled {
        "Disable replacements"
    } else {
        "Enable replacements"
    };
    let startup_flags = MF_STRING
        | if start_on_login {
            MF_CHECKED
        } else {
            MF_UNCHECKED
        };

    append_item(menu, MF_STRING, ID_TOGGLE_ENABLED, toggle_text);
    append_item(menu, MF_STRING, ID_HIDE_TRAY, "Hide tray");
    append_item(menu, startup_flags, ID_TOGGLE_STARTUP, "Start on login");
    AppendMenuW(menu, MF_SEPARATOR, 0, null_mut());
    append_item(menu, MF_STRING, ID_RELOAD, "Reload app");
    append_item(menu, MF_STRING, ID_OPEN_CONFIG, "Open replacements.json");
    append_item(
        menu,
        MF_STRING,
        ID_OPEN_SETTINGS,
        "Open settings (config.json)",
    );
    AppendMenuW(menu, MF_SEPARATOR, 0, null_mut());
    append_item(menu, MF_STRING, ID_ABOUT, "About");
    AppendMenuW(menu, MF_SEPARATOR, 0, null_mut());
    append_item(menu, MF_STRING, ID_EXIT, "Exit");

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
    PostMessageW(hwnd, WM_NULL, 0, 0);
    DestroyMenu(menu);
}

/// Builds the NOTIFYICONDATAW identifying our icon (no payload flags set).
fn tray_data() -> Option<NOTIFYICONDATAW> {
    let (hwnd, icon) = with_state(|s| (s.hwnd, s.tray_icon))?;
    let mut nid: NOTIFYICONDATAW = unsafe { zeroed() };
    nid.cbSize = size_of::<NOTIFYICONDATAW>() as u32;
    nid.hWnd = hwnd as HWND;
    nid.uID = TRAY_ID;
    nid.hIcon = icon as HICON;
    Some(nid)
}

/// Asks the shell to show the icon. Safe to call when it is already there
/// (NIM_ADD then fails harmlessly). Does not touch state or config.json.
fn add_tray_icon() {
    let Some(mut nid) = tray_data() else { return };
    nid.uFlags = NIF_ICON | NIF_MESSAGE | NIF_TIP;
    nid.uCallbackMessage = WM_TRAYICON;
    let tip = to_wide("Textpander (abbreviation replacement)");
    let n = tip.len().min(nid.szTip.len());
    nid.szTip[..n].copy_from_slice(&tip[..n]);
    // The tooltip must stay NUL-terminated even when truncated.
    nid.szTip[nid.szTip.len() - 1] = 0;
    unsafe {
        Shell_NotifyIconW(NIM_ADD, &mut nid);
    }
}

/// User-facing "show": adds the icon and remembers it as visible.
fn show_tray_icon() {
    add_tray_icon();
    with_state(|s| {
        s.tray_visible = true;
        persist_settings(s);
    });
}

/// Watchdog: NIM_MODIFY fails when the shell no longer knows our icon, in
/// which case we add it back (Explorer restarted, NIM_ADD raced with tray
/// startup...).
fn ensure_tray_icon() {
    if !with_state(|s| s.tray_visible).unwrap_or(false) {
        return;
    }
    if let Some(mut nid) = tray_data() {
        if unsafe { Shell_NotifyIconW(NIM_MODIFY, &mut nid) } == 0 {
            add_tray_icon();
        }
    }
}

/// Removes the icon's visual only (also used at shutdown, where we must NOT
/// persist "hidden").
fn remove_tray_icon_visual() {
    if let Some(mut nid) = tray_data() {
        unsafe {
            Shell_NotifyIconW(NIM_DELETE, &mut nid);
        }
    }
}

/// "Hide tray": the app keeps running; relaunching the exe brings it back.
fn hide_tray_icon() {
    remove_tray_icon_visual();
    with_state(|s| {
        s.tray_visible = false;
        persist_settings(s);
    });
}

// ---------------------------------------------------------------------------
// Menu actions
// ---------------------------------------------------------------------------

fn toggle_enabled() {
    with_state(|s| {
        s.enabled = !s.enabled;
        s.reset_typing();
        persist_settings(s);
    });
}

fn toggle_start_on_login() {
    if let Some(now) = with_state(|s| {
        s.start_on_login = !s.start_on_login;
        persist_settings(s);
        s.start_on_login
    }) {
        set_start_on_login(now);
    }
}

fn open_config_file(pick: impl FnOnce(&AppState) -> PathBuf) {
    // Clone the path out first: ShellExecute must not run under the lock.
    if let Some(path) = with_state(|s| pick(s)) {
        open_in_default_app(&path);
    }
}

/// Reloads replacements.json and config.json and applies every setting.
/// On invalid JSON the previous configuration is kept.
fn reload_config() {
    // Files are read BEFORE taking the lock again: a parse error pops a
    // message box whose nested message loop would run the keyboard hook,
    // which locks STATE (see the note at the top of this file).
    let Some((replacements_path, settings_path)) =
        with_state(|s| (s.replacements_path.clone(), s.settings_path.clone()))
    else {
        return;
    };
    let config = load_replacements(&replacements_path);
    let settings = load_settings(&settings_path);

    if let Err(e) = &config {
        show_message(&format!("{e}\n\nThe previous abbreviations stay active."));
    }
    if let Err(e) = &settings {
        show_message(&format!("{e}\n\nThe previous settings stay active."));
    }

    with_state(|s| {
        if let Ok(config) = config {
            s.config = config;
        }
        if let Ok(settings) = &settings {
            s.boundary_chars = boundary_chars_from_settings(settings);
            s.enabled = settings.enabled;
            s.start_on_login = settings.start_on_login;
            s.clear_autocomplete = settings.clear_autocomplete;
        }
        s.reset_typing();
    });

    if let Ok(settings) = settings {
        set_start_on_login(settings.start_on_login);
        if settings.show_tray_icon {
            show_tray_icon();
        } else {
            hide_tray_icon();
        }
    }
}

// ---------------------------------------------------------------------------
// Keyboard handling
// ---------------------------------------------------------------------------

/// Result of resolving what a keydown actually produces.
enum KeyChar {
    /// A dead key (accent waiting to combine with the next letter).
    DeadKey,
    Char(char),
    /// No printable character (arrows, function keys...).
    None,
}

/// Resolves the Unicode character a key produces, honoring the keyboard
/// layout of the focused window (Shift, CapsLock, AltGr...). The key-state
/// array is built from GetAsyncKeyState because this hook thread doesn't own
/// the input queue, so GetKeyboardState can be stale.
fn char_from_vk(vk: i32, scan_code: u32) -> KeyChar {
    unsafe {
        let thread_id = GetWindowThreadProcessId(GetForegroundWindow(), null_mut());
        let hkl = GetKeyboardLayout(thread_id);

        // MapVirtualKeyExW is a stateless table lookup: it never touches the
        // OS dead-key composition state, so it is a free, safe pre-check.
        // It can't see keys that are dead only under AltGr (e.g. "~" on
        // AZERTY) - the ToUnicodeEx result below catches those.
        if MapVirtualKeyExW(vk as u32, MAPVK_VK_TO_CHAR, hkl) & 0x8000_0000 != 0 {
            return KeyChar::DeadKey;
        }

        let mut keys = [0u8; 256];
        for modifier in [
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
            if is_down(modifier) {
                keys[modifier as usize] = 0x80;
            }
        }
        if (GetKeyState(VK_CAPITAL) & 1) != 0 {
            keys[VK_CAPITAL as usize] = 1;
        }

        let translate = |out: &mut [u16; 8]| {
            ToUnicodeEx(
                vk as u32,
                scan_code,
                keys.as_ptr(),
                out.as_mut_ptr(),
                out.len() as i32,
                0,
                hkl,
            )
        };

        let mut buf = [0u16; 8];
        let result = translate(&mut buf);

        if result < 0 {
            // Dead key (once AltGr etc. is taken into account). Our probe
            // just armed the kernel-mode dead-key buffer as a side effect;
            // since we don't swallow dead keys, the focused app would then
            // see a composition already pending and double the character
            // ("~~"). Calling again with identical parameters consumes our
            // own bogus arm so the app's real processing starts clean.
            translate(&mut [0u16; 8]);
            return KeyChar::DeadKey;
        }
        if result == 0 {
            return KeyChar::None;
        }
        char::from_u32(buf[0] as u32).map_or(KeyChar::None, KeyChar::Char)
    }
}

/// Modifier keys we ignore for buffer tracking: they routinely precede a
/// letter (Shift + letter) and must not reset context.
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
    if ncode == HC_ACTION {
        let kb = &*(lparam as *const KBDLLHOOKSTRUCT);
        // Ignore events we injected ourselves, to avoid feedback loops.
        if kb.flags & LLKHF_INJECTED == 0 {
            let vk = kb.vkCode as i32;
            let swallow = match wparam as u32 {
                WM_KEYDOWN | WM_SYSKEYDOWN => handle_keydown(vk, kb.scanCode),
                WM_KEYUP | WM_SYSKEYUP => should_swallow_keyup(vk),
                _ => false,
            };
            if swallow {
                return 1;
            }
        }
    }
    CallNextHookEx(null_mut(), ncode, wparam, lparam)
}

unsafe extern "system" fn mouse_hook_proc(ncode: i32, wparam: WPARAM, lparam: LPARAM) -> LRESULT {
    if ncode == HC_ACTION
        && matches!(
            wparam as u32,
            WM_LBUTTONDOWN | WM_RBUTTONDOWN | WM_MBUTTONDOWN
        )
    {
        // A click can put the caret anywhere (another field, another
        // window): whatever was half-typed no longer applies.
        with_state(|s| s.reset_typing());
    }
    CallNextHookEx(null_mut(), ncode, wparam, lparam)
}

fn should_swallow_keyup(vk: i32) -> bool {
    with_state(|s| {
        let swallow = s.suppress_next_keyup == Some(vk);
        if swallow {
            s.suppress_next_keyup = None;
        }
        swallow
    })
    .unwrap_or(false)
}

/// A key that finished a word and triggers an expansion check: Enter/Tab
/// (always active) or a character from the "characters" list in config.json.
#[derive(Clone, Copy)]
enum Boundary {
    Key(i32),
    Char(char),
}

/// Returns true if this keydown was fully handled by us and must be
/// swallowed (not delivered to the focused app).
fn handle_keydown(vk: i32, scan_code: u32) -> bool {
    let mut guard = lock_state();
    let Some(state) = guard.as_mut() else {
        return false;
    };

    // Paused via the tray menu (state was already cleared when switching
    // off), or a bare modifier: pass through untouched.
    if !state.enabled || is_ignored_modifier(vk) {
        return false;
    }

    // Focus moved to another window since the last key: the word in the
    // buffer belongs to somewhere else.
    let foreground = unsafe { GetForegroundWindow() } as usize;
    if foreground != state.last_foreground {
        state.reset_typing();
        state.last_foreground = foreground;
    }

    // A Ctrl-only or Alt-only chord is a real shortcut (Ctrl+Backspace,
    // Ctrl+C...) and must never feed our synthetic-backspace logic. Ctrl+Alt
    // together is AltGr (used for '@', '~'...) and is let through below.
    if is_down(VK_CONTROL) != is_down(VK_MENU) {
        state.reset_typing();
        return false;
    }

    if vk == VK_BACK {
        // Backspace cancels any pending dead-key composition.
        state.skip_next_char_resolution = false;

        // Right after an expansion: undo it.
        if let Some(last) = state.last_expansion.take() {
            state.buffer.clone_from(&last.typed);
            state.suppress_expansion = true;
            state.suppress_next_keyup = Some(VK_BACK);
            drop(guard);
            perform_undo(&last);
            return true;
        }
        // Right after a boundary key that matched nothing: this Backspace
        // deletes that boundary, so resume tracking the word as it was.
        match state.pending_word.take() {
            Some(word) => state.buffer = word,
            None => {
                state.buffer.pop();
            }
        }
        return false;
    }

    // Any other key closes the undo window and abandons the pending word.
    state.last_expansion = None;
    state.pending_word = None;
    // One-shot: right after an undo, don't re-expand on the next boundary.
    let skip_due_to_undo = mem::take(&mut state.suppress_expansion);

    let boundary = if vk == VK_RETURN || vk == VK_TAB {
        Some(Boundary::Key(vk))
    } else if mem::take(&mut state.skip_next_char_resolution) {
        // Previous key was a dead key: leave this one completely alone so
        // the target app can finish composing the accent itself.
        state.buffer.clear();
        None
    } else {
        match char_from_vk(vk, scan_code) {
            // A dead key alone produces no visible character, so it doesn't
            // invalidate the word; just skip the next key's resolution.
            KeyChar::DeadKey => {
                state.skip_next_char_resolution = true;
                None
            }
            KeyChar::Char(ch) if state.boundary_chars.contains(&ch) => Some(Boundary::Char(ch)),
            KeyChar::Char(ch) => {
                if state.buffer.len() < MAX_BUFFER_LEN {
                    state.buffer.push(ch);
                } else {
                    state.buffer.clear();
                }
                None
            }
            KeyChar::None => {
                state.buffer.clear();
                None
            }
        }
    };
    let Some(boundary) = boundary else {
        return false;
    };

    if !skip_due_to_undo && !state.buffer.is_empty() {
        if let Some(expansion) = logic::expand(&state.config, &state.buffer) {
            let typed = mem::take(&mut state.buffer);
            let abbr_len = typed.chars().count();
            state.last_expansion = Some(LastExpansion {
                typed,
                delete_len: expansion.chars().count() + 1, // +1: the boundary key
            });
            state.suppress_next_keyup = Some(vk);
            let clear_autocomplete = state.clear_autocomplete;
            drop(guard);
            // We swallow the boundary key and re-type it as part of the
            // replacement, so the original keystroke must not pass through.
            perform_replacement(abbr_len, &expansion, boundary, clear_autocomplete);
            return true;
        }
    }

    // No match: remember the word for exactly one Backspace.
    let word = mem::take(&mut state.buffer);
    state.pending_word = (!word.is_empty()).then_some(word);
    false
}

// ---------------------------------------------------------------------------
// Synthetic input
// ---------------------------------------------------------------------------

fn key_input(vk: u16, scan: u16, flags: u32) -> INPUT {
    unsafe {
        let mut input: INPUT = zeroed();
        input.type_ = INPUT_KEYBOARD;
        *input.u.ki_mut() = KEYBDINPUT {
            wVk: vk,
            wScan: scan,
            dwFlags: flags,
            time: 0,
            dwExtraInfo: 0,
        };
        input
    }
}

/// Key press + release of a virtual key.
fn push_key(inputs: &mut Vec<INPUT>, vk: u16) {
    inputs.push(key_input(vk, 0, 0));
    inputs.push(key_input(vk, 0, KEYEVENTF_KEYUP));
}

/// Types text as Unicode, so accents etc. work on any keyboard layout.
fn push_text(inputs: &mut Vec<INPUT>, text: &str) {
    for unit in text.encode_utf16() {
        inputs.push(key_input(0, unit, KEYEVENTF_UNICODE));
        inputs.push(key_input(0, unit, KEYEVENTF_UNICODE | KEYEVENTF_KEYUP));
    }
}

fn push_backspaces(inputs: &mut Vec<INPUT>, count: usize) {
    for _ in 0..count {
        push_key(inputs, VK_BACK as u16);
    }
}

fn send_inputs(inputs: &mut [INPUT]) {
    if !inputs.is_empty() {
        unsafe {
            SendInput(
                inputs.len() as u32,
                inputs.as_mut_ptr(),
                size_of::<INPUT>() as i32,
            );
        }
    }
}

/// Deletes the typed abbreviation, then types the expansion followed by the
/// boundary key/character that triggered it.
fn perform_replacement(
    abbr_len: usize,
    expansion: &str,
    boundary: Boundary,
    clear_autocomplete: bool,
) {
    let mut inputs = Vec::with_capacity((abbr_len + expansion.len() + 2) * 2);
    // Typing over a selected inline-autocomplete suggestion replaces it, so
    // whether or not one exists, the field now ends with "<abbr>~" and one
    // extra Backspace removes exactly the marker. "~" is unlikely to match
    // any suggestion, so it can't re-trigger autocompletion itself.
    if clear_autocomplete {
        push_text(&mut inputs, "~");
    }
    push_backspaces(&mut inputs, abbr_len + usize::from(clear_autocomplete));
    push_text(&mut inputs, expansion);
    match boundary {
        Boundary::Key(vk) => push_key(&mut inputs, vk as u16),
        Boundary::Char(ch) => push_text(&mut inputs, ch.encode_utf8(&mut [0; 4])),
    }
    send_inputs(&mut inputs);
}

/// Deletes the expansion plus its boundary key, then retypes the abbreviation
/// exactly as the user typed it.
fn perform_undo(last: &LastExpansion) {
    let mut inputs = Vec::new();
    push_backspaces(&mut inputs, last.delete_len);
    push_text(&mut inputs, &last.typed);
    send_inputs(&mut inputs);
}
