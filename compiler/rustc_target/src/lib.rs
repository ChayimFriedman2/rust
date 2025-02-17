//! Some stuff used by rustc that doesn't have many dependencies
//!
//! Originally extracted from rustc::back, which was nominally the
//! compiler 'backend', though LLVM is rustc's backend, so rustc_target
//! is really just odds-and-ends relating to code gen and linking.
//! This crate mostly exists to make rustc smaller, so we might put
//! more 'stuff' here in the future. It does not have a dependency on
//! LLVM.

// tidy-alphabetical-start
#![allow(internal_features)]
#![cfg_attr(feature = "nightly", doc(rust_logo))]
#![cfg_attr(feature = "nightly", feature(iter_intersperse))]
#![cfg_attr(feature = "nightly", feature(let_chains))]
#![cfg_attr(feature = "nightly", feature(rustdoc_internals))]
#![doc(html_root_url = "https://doc.rust-lang.org/nightly/nightly-rustc/")]
#![warn(unreachable_pub)]
// tidy-alphabetical-end

use std::hash::BuildHasherDefault;
use std::path::{Path, PathBuf};

use rustc_hash::FxHasher;

pub mod asm;
pub mod callconv;
pub mod json;
pub mod spec;
pub mod target_features;

#[cfg(test)]
mod tests;

#[cfg(feature = "nightly")]
use rustc_abi::HashStableContext;

pub(crate) type FxIndexSet<T> = indexmap::IndexSet<T, BuildHasherDefault<FxHasher>>;

/// The name of rustc's own place to organize libraries.
///
/// Used to be `rustc`, now the default is `rustlib`.
const RUST_LIB_DIR: &str = "rustlib";

/// Returns a `rustlib` path for this particular target, relative to the provided sysroot.
///
/// For example: `target_sysroot_path("/usr", "x86_64-unknown-linux-gnu")` =>
/// `"lib*/rustlib/x86_64-unknown-linux-gnu"`.
pub fn relative_target_rustlib_path(sysroot: &Path, target_triple: &str) -> PathBuf {
    let libdir = find_relative_libdir(sysroot);
    Path::new(libdir.as_ref()).join(RUST_LIB_DIR).join(target_triple)
}

/// The name of the directory rustc expects libraries to be located.
fn find_relative_libdir(sysroot: &Path) -> std::borrow::Cow<'static, str> {
    // FIXME: This is a quick hack to make the rustc binary able to locate
    // Rust libraries in Linux environments where libraries might be installed
    // to lib64/lib32. This would be more foolproof by basing the sysroot off
    // of the directory where `librustc_driver` is located, rather than
    // where the rustc binary is.
    // If --libdir is set during configuration to the value other than
    // "lib" (i.e., non-default), this value is used (see issue #16552).

    #[cfg(target_pointer_width = "64")]
    const PRIMARY_LIB_DIR: &str = "lib64";

    #[cfg(target_pointer_width = "32")]
    const PRIMARY_LIB_DIR: &str = "lib32";

    const SECONDARY_LIB_DIR: &str = "lib";

    match option_env!("CFG_LIBDIR_RELATIVE") {
        None | Some("lib") => {
            if sysroot.join(PRIMARY_LIB_DIR).join(RUST_LIB_DIR).exists() {
                PRIMARY_LIB_DIR.into()
            } else {
                SECONDARY_LIB_DIR.into()
            }
        }
        Some(libdir) => libdir.into(),
    }
}

/// A macro that expands to either `rustc_span::sym::symbol` or to `"symbol"`,
/// so we can build on stable.
#[cfg(feature = "nightly")]
macro_rules! sym {
    ($sym:ident $(,)?) => {
        ::rustc_span::sym::$sym
    };
    ($sym:ident, $value:literal $(,)?) => {
        ::rustc_span::sym::$sym
    };
}
#[cfg(not(feature = "nightly"))]
macro_rules! sym {
    ($sym:ident $(,)?) => {
        stringify!($sym)
    };
    ($sym:ident, $value:literal $(,)?) => {
        $value
    };
}

#[inline]
pub(crate) fn symbol_as_str(sym: &Symbol) -> &str {
    #[cfg(feature = "nightly")]
    let result = sym.as_str();
    #[cfg(not(feature = "nightly"))]
    let result = sym;
    result
}

/// Copy-pasted from `rustc_data_structures`, because we cannot depend on it.
macro_rules! external_bitflags_debug {
    ($Name:ident) => {
        impl ::std::fmt::Debug for $Name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                ::bitflags::parser::to_writer(self, f)
            }
        }
    };
}

/// A type alias that resolves to either [`rustc_span::Symbol`] or `&'static str`, so we can build on stable.
#[cfg(feature = "nightly")]
pub use rustc_span::Symbol;
pub(crate) use {external_bitflags_debug, sym};
#[cfg(not(feature = "nightly"))]
pub type Symbol = &'static str;
