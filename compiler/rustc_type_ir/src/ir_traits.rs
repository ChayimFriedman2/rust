use std::fmt::Debug;
use std::hash::Hash;

use crate::Interner;

pub trait MyToOwned<I: Interner>: Sized + Debug + Copy + Hash + PartialEq + Eq {
    type Owned;
    fn o(self) -> Self::Owned;
}

impl<I: Interner, T: MyToOwned<I>> MyToOwned<I> for &T {
    type Owned = T::Owned;

    #[inline]
    fn o(self) -> Self::Owned {
        (*self).o()
    }
}

impl<I: Interner, T: MyToOwned<I>> MyToOwned<I> for Option<T> {
    type Owned = Option<T::Owned>;

    #[inline]
    fn o(self) -> Self::Owned {
        self.map(T::o)
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! __for_each_reborrowable {
    ( $arg:tt $macro:path ) => {
        $macro! {
            $arg

            GenericArgsRef
            GenericArgsSlice
            GenericArgRef
            TermRef
            BoundVarKindsRef
            PredefinedOpaquesRef
            LocalDefIdsRef
            CanonicalVarKindsRef
            ExternalConstraintsRef
            TyRef
            TysRef
            FnInputTys
            BoundExistentialPredicatesRef
            PatListRef
            ConstRef
            RegionRef
            RegionAssumptionsRef
            ParamEnvRef
            PredicateRef
            ClauseRef
            ClausesRef
            VariancesOfRef
        }
    };
}
pub use __for_each_reborrowable as for_each_reborrowable;

#[doc(hidden)]
#[macro_export]
macro_rules! __for_each_owned_borrowed_pair {
    ( $arg:tt $macro:path ) => {
        $macro! {
            $arg

            GenericArgs                 GenericArgsRef
            GenericArg                  GenericArgRef
            Term                        TermRef
            BoundVarKinds               BoundVarKindsRef
            PredefinedOpaques           PredefinedOpaquesRef
            LocalDefIds                 LocalDefIdsRef
            CanonicalVarKinds           CanonicalVarKindsRef
            ExternalConstraints         ExternalConstraintsRef
            Ty                          TyRef
            Tys                         TysRef
            BoundExistentialPredicates  BoundExistentialPredicatesRef
            PatList                     PatListRef
            Const                       ConstRef
            Region                      RegionRef
            RegionAssumptions           RegionAssumptionsRef
            ParamEnv                    ParamEnvRef
            Predicate                   PredicateRef
            Clause                      ClauseRef
            Clauses                     ClausesRef
            VariancesOf                 VariancesOfRef
        }
    };
}
pub use __for_each_owned_borrowed_pair as for_each_owned_borrowed_pair;

#[doc(hidden)]
#[macro_export]
macro_rules! __for_each_as_owned_kind {
    ( $arg:tt $macro:path ) => {
        $macro! {
            $arg

            GenericArg = GenericArgKind,
            Term = TermKind,
        }
    };
}
pub use __for_each_as_owned_kind as for_each_as_owned_kind;

macro_rules! declare_reborrow_trait {
    ( [] $( $name:ident )* ) => {
        pub mod reborrow {
            use super::*;
            $(
                pub trait $name<'a, I: Interner> {
                    fn reborrow<'b>(self) -> I::$name<'b>
                    where
                        'a: 'b;
                }
            )*
        }
        $( pub use reborrow::$name as _; )*
    };
}

for_each_reborrowable!([] declare_reborrow_trait);

macro_rules! declare_as_ref_trait {
    ( [] $( $owned:ident $borrowed:ident )* ) => {
        pub mod as_ref {
            use super::*;
            $(
                pub trait $owned<I: Interner>: Sized + Debug + Clone + Hash + PartialEq + Eq {
                    fn r(&self) -> I::$borrowed<'_>;
                }
            )*
        }
        $( pub use as_ref::$owned as _; )*
    };
}

for_each_owned_borrowed_pair!([] declare_as_ref_trait);

macro_rules! declare_as_owned_kind {
    ( [] $( $name:ident = $kind:ident ),* $(,)? ) => {
        pub mod as_owned_kind {
            use super::*;
            $(
                pub trait $name<I: Interner> {
                    fn kind(&self) -> crate::$kind<'_, I>;
                }
            )*
        }
        $( pub use as_owned_kind::$name as _; )*
    };
}

for_each_as_owned_kind!([] declare_as_owned_kind);
