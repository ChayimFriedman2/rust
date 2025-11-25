use rustc_type_ir::Interner;
use rustc_type_ir::ir_traits::{MyToOwned, as_owned_kind, as_ref, reborrow};

use crate::ty::TyCtxt;

macro_rules! impl_reborrow {
    ( [] $( $name:ident )* ) => {
        $(
            impl<'a, 'tcx> reborrow::$name<'a, TyCtxt<'tcx>>
                for <TyCtxt<'tcx> as Interner>::$name<'tcx>
            {
                #[inline(always)]
                fn reborrow<'b>(self) -> Self
                where
                    'a: 'b,
                {
                    self
                }
            }
        )*
    };
}

rustc_type_ir::ir_traits::for_each_reborrowable!([] impl_reborrow);

macro_rules! impl_as_ref {
    ( [] $( $owned:ident $borrowed:ident )* ) => {
        $(
            impl<'tcx> as_ref::$owned<TyCtxt<'tcx>>
                for <TyCtxt<'tcx> as Interner>::$owned
            {
                #[inline(always)]
                fn r(&self) -> <TyCtxt<'tcx> as Interner>::$borrowed<'_> {
                    *self
                }
            }

            impl<'tcx> MyToOwned<TyCtxt<'tcx>> for <TyCtxt<'tcx> as Interner>::$owned {
                type Owned = Self;
                #[inline(always)]
                fn o(self) -> <TyCtxt<'tcx> as Interner>::$owned {
                    self
                }
            }
        )*
    };
}

rustc_type_ir::ir_traits::for_each_owned_borrowed_pair!([] impl_as_ref);

macro_rules! impl_as_owned_kind {
    ( [] $( $name:ident = $kind:ident ),* $(,)? ) => {
        $(
            impl<'tcx> as_owned_kind::$name<TyCtxt<'tcx>> for <TyCtxt<'tcx> as Interner>::$name {
                #[inline(always)]
                fn kind(&self) -> rustc_type_ir::$kind<'_, TyCtxt<'tcx>> {
                    (*self).kind()
                }
            }
        )*
    };
}

rustc_type_ir::ir_traits::for_each_as_owned_kind!([] impl_as_owned_kind);
