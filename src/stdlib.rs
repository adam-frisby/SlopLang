//! Bundled `core` (freestanding) and `std` (hosted) standard library modules and preludes.
//!
//! Their source is in `lib/`, one file per module (`lib/std/sync.slop` is `std::sync`, and a
//! library's own root is `root.slop`), built into the compiler so it needs no files at run time.

/// Module path and source, for a library's modules.
macro_rules! bundled {
    ($lib:literal: $($module:literal => $file:literal),* $(,)?) => {
        &[$(($module, include_str!(concat!("../lib/", $lib, "/", $file, ".slop")))),*]
    };
}

pub const CORE_MODULES: &[(&str, &str)] = bundled!("core":
    "core" => "root",
    "core::prelude" => "prelude",
    "core::mem" => "mem",
    "core::cmp" => "cmp",
    "core::math" => "math",
    "core::slice" => "slice",
    "core::option" => "option",
    "core::fmt" => "fmt",
    "core::meta" => "meta",
);

pub const STD_MODULES: &[(&str, &str)] = bundled!("std":
    "std" => "root",
    "std::prelude" => "prelude",
    "std::mem" => "mem",
    "std::collections" => "collections",
    "std::sync" => "sync",
    "std::thread" => "thread",
    "std::fmt" => "fmt",
    "std::io" => "io",
    "std::iter" => "iter",
    "std::build" => "build",
);

pub fn is_stdlib_module(mod_path: &str) -> bool {
    mod_path == "core"
        || mod_path.starts_with("core::")
        || mod_path == "std"
        || mod_path.starts_with("std::")
}

/// Every file in `lib/` is a bundled module, and every module's file is named for its path, so
/// a file added there is not silently left out of the compiler.
#[test]
fn bundled_modules_match_lib() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lib");
    let mut on_disk = Vec::new();
    for lib in std::fs::read_dir(&dir).unwrap() {
        let lib = lib.unwrap();
        for file in std::fs::read_dir(lib.path()).unwrap() {
            let file = file.unwrap().path();
            let lib_name = lib.file_name().into_string().unwrap();
            let stem = file.file_stem().unwrap().to_str().unwrap().to_string();
            assert_eq!(file.extension().and_then(|e| e.to_str()), Some("slop"), "{}", file.display());
            on_disk.push(if stem == "root" { lib_name } else { format!("{lib_name}::{stem}") });
        }
    }
    let mut listed: Vec<String> =
        CORE_MODULES.iter().chain(STD_MODULES).map(|(m, _)| m.to_string()).collect();
    on_disk.sort();
    listed.sort();
    assert_eq!(on_disk, listed);
    for (module, src) in CORE_MODULES.iter().chain(STD_MODULES) {
        let parts: Vec<&str> = module.split("::").collect();
        let file = dir.join(parts[0]).join(format!("{}.slop", parts.get(1).unwrap_or(&"root")));
        assert_eq!(*src, std::fs::read_to_string(&file).unwrap(), "{module}");
    }
}
