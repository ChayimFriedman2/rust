use derive_where::derive_where;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable_NoContext, Encodable_NoContext, HashStable_NoContext};
use rustc_type_ir_macros::{TypeFoldable_Generic, TypeVisitable_Generic};

use crate::inherent::*;
use crate::ir_traits::*;
use crate::{self as ty, Interner, VariancesOf};

#[derive_where(Clone, Hash, PartialEq, Debug; I: Interner)]
#[derive_where(Copy; I: Interner, I::GenericArgs: Copy)]
#[derive(TypeVisitable_Generic, TypeFoldable_Generic)]
#[cfg_attr(
    feature = "nightly",
    derive(Encodable_NoContext, Decodable_NoContext, HashStable_NoContext)
)]
pub struct OpaqueTypeKey<I: Interner> {
    pub def_id: I::LocalDefId,
    pub args: I::GenericArgs,
}

impl<I: Interner> Eq for OpaqueTypeKey<I> {}

impl<I: Interner> OpaqueTypeKey<I> {
    pub fn iter_captured_args(&self, cx: I) -> impl Iterator<Item = (usize, I::GenericArgRef<'_>)> {
        let variances = cx.variances_of(self.def_id.into());
        std::iter::zip(self.args.r().iter(), variances.into_iter()).enumerate().filter_map(
            |(i, (arg, v))| match (arg.kind(), v) {
                (_, ty::Invariant) => Some((i, arg)),
                (ty::GenericArgKind::Lifetime(_), ty::Bivariant) => None,
                _ => panic!("unexpected opaque type arg variance"),
            },
        )
    }

    pub fn fold_captured_lifetime_args(
        self,
        cx: I,
        mut f: impl FnMut(I::Region) -> I::Region,
    ) -> Self {
        let Self { def_id, args } = self;
        let variances = cx.variances_of(def_id.into());
        let args = std::iter::zip(args.r().iter(), variances.into_iter()).map(|(arg, v)| {
            match (arg.kind(), v) {
                (ty::GenericArgKind::Lifetime(_), ty::Bivariant) => arg.o(),
                (ty::GenericArgKind::Lifetime(lt), _) => f(lt.o()).into(),
                _ => arg.o(),
            }
        });
        let args = cx.mk_args_from_iter(args);
        Self { def_id, args }
    }
}
