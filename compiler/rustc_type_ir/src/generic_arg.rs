use derive_where::derive_where;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable_NoContext, Encodable_NoContext, HashStable_NoContext};

use crate::Interner;

#[derive_where(Clone, Copy, PartialEq, Debug; I: Interner)]
#[cfg_attr(
    feature = "nightly",
    derive(Decodable_NoContext, Encodable_NoContext, HashStable_NoContext)
)]
pub enum GenericArgKind<'a, I: Interner + 'a> {
    Lifetime(I::RegionRef<'a>),
    Type(I::TyRef<'a>),
    Const(I::ConstRef<'a>),
}

impl<I: Interner> Eq for GenericArgKind<'_, I> {}

#[derive_where(Clone, Copy, PartialEq, Debug; I: Interner)]
#[cfg_attr(
    feature = "nightly",
    derive(Decodable_NoContext, Encodable_NoContext, HashStable_NoContext)
)]
pub enum TermKind<'a, I: Interner + 'a> {
    Ty(I::TyRef<'a>),
    Const(I::ConstRef<'a>),
}

impl<I: Interner> Eq for TermKind<'_, I> {}
