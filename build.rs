use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if target_os != "windows" {
        return; // Nothing to do when building/checking on non-Windows targets.
    }

    println!("cargo:rerun-if-changed=app.rc");
    println!("cargo:rerun-if-changed=assets/icon.ico");

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default(); // "gnu" or "msvc"
    let res_obj = out_dir.join("app_resource.o");

    let ok = if target_env == "msvc" {
        // MSVC toolchain: use the Resource Compiler that ships with the
        // Windows SDK / Visual Studio Build Tools.
        Command::new("rc.exe")
            .args(["/fo", res_obj.to_str().unwrap(), "app.rc"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    } else {
        // GNU/mingw toolchain: windres ships with mingw-w64.
        let windres = env::var("WINDRES").unwrap_or_else(|_| "windres".to_string());
        Command::new(&windres)
            .args(["app.rc", "-O", "coff", "-o"])
            .arg(&res_obj)
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    };

    if ok {
        println!("cargo:rustc-link-arg-bins={}", res_obj.display());
    } else {
        // Don't fail the whole build over a missing icon - just warn and
        // ship without a custom one (falls back to the default Windows icon
        // at runtime, see windows_app.rs).
        println!(
            "cargo:warning=Could not compile app.rc (icon resource) - building without a custom icon. \
             Make sure a resource compiler (windres for GNU/mingw, or rc.exe for MSVC) is available."
        );
    }
}
