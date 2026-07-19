# Textpander

An app that runs as a tray icon and expands abbreviations as you type, anywhere on the system, based on `config.json`. I used AI (Claude) to make it. 

Typing `pls` then a space/Enter/Tab becomes `please`:

- `pls` --> `please`
- `Pls` --> `Please`
- `PLS` --> `PLEASE`

## Installation

### For users

Go to the [releases page](https://github.com/Alfakynz/Textpander/releases) and download the latest `textpander.exe`.

### For developers

To build from source, clone this repository and run `cargo build --release`. The executable will be located in `target/release/textpander.exe`.

## TODO

- Installer
- Configs on `AppData` (`dictionary.json` for replacements and `config.json` for settings)
- Replacement with other characters (`" , ) : ; ? !`)
- Start on login
- About
