# Textpander

An app that runs as a tray icon and expands abbreviations as you type, anywhere on the system, based on `replacements.json`. I used AI (Claude) to make it. 

Typing `pls` then a space/Enter/Tab becomes `please`:

- `pls` --> `please`
- `Pls` --> `Please`
- `PLS` --> `PLEASE`

## Installation

### For users

Go to the [releases page](https://github.com/Alfakynz/Textpander/releases) and download the latest `textpander.exe`.

### For developers

To build from source, clone this repository and run `cargo build --release`. The executable will be located in `target/release/textpander.exe`.

## Configuration

Textpander stores its files in `%APPDATA%\Textpander\`:

- `replacements.json`: the abbreviation --> expansion pairs
- `config.json`: app settings - `enabled` (replacements active on startup), `show_tray_icon` (tray icon shown on startup), and `start_on_login` (launch automatically when you log in)

Both are created with sensible defaults on first run if missing. Use the tray menu ("Open replacements.json" / "Open settings (config.json)") to edit them, then "Reload replacements" to pick up changes without restarting. The tray menu's "Hide tray" and "Start on login" toggles update `config.json` automatically, so your choice is remembered the next time the app starts.

## TODO

- Fix start on login
