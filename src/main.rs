// On Windows this hides the console window that would otherwise flash open
// (this is a tray app, not a console app).
#![cfg_attr(windows, windows_subsystem = "windows")]

mod logic;

#[cfg(windows)]
mod windows_app;

fn main() {
    #[cfg(windows)]
    {
        windows_app::run();
    }

    #[cfg(not(windows))]
    {
        eprintln!("Textpander only runs on Windows.");
    }
}
