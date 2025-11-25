use std::borrow::Borrow;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;

use rustc_ast_ir::Movability;
use rustc_index::bit_set::DenseBitSet;

use crate::fold::TypeFoldable;
use crate::inherent::*;
use crate::ir_print::IrPrint;
use crate::ir_traits::{MyToOwned, as_owned_kind, as_ref, reborrow};
use crate::lang_items::{SolverAdtLangItem, SolverLangItem, SolverTraitLangItem};
use crate::relate::{Relate, RelateRef};
use crate::solve::{CanonicalInput, Certainty, ExternalConstraintsData, QueryResult, inspect};
use crate::visit::{Flags, TypeVisitable};
use crate::{
    self as ty, CanonicalParamEnvCacheEntry, TypeSuperFoldable, TypeSuperVisitable, search_graph,
};

#[cfg_attr(feature = "nightly", rustc_diagnostic_item = "type_ir_interner")]
pub trait Interner:
    Sized
    + Copy
    + IrPrint<ty::AliasTy<Self>>
    + IrPrint<ty::AliasTerm<Self>>
    + IrPrint<ty::TraitRef<Self>>
    + IrPrint<ty::TraitPredicate<Self>>
    + IrPrint<ty::HostEffectPredicate<Self>>
    + IrPrint<ty::ExistentialTraitRef<Self>>
    + IrPrint<ty::ExistentialProjection<Self>>
    + IrPrint<ty::ProjectionPredicate<Self>>
    + IrPrint<ty::NormalizesTo<Self>>
    + IrPrint<ty::SubtypePredicate<Self>>
    + IrPrint<ty::CoercePredicate<Self>>
    + IrPrint<ty::FnSig<Self>>
    + IrPrint<ty::PatternKind<Self>>
{
    type DefId: DefId<Self>;
    type LocalDefId: Copy + Debug + Hash + Eq + Into<Self::DefId> + TypeFoldable<Self>;
    // Various more specific `DefId`s.
    //
    // rustc just defines them all to be `DefId`, but rust-analyzer uses different types so this is convenient for it.
    //
    // Note: The `TryFrom<DefId>` always succeeds (in rustc), so don't use it to check if some `DefId`
    // is of some specific type!
    type TraitId: SpecificDefId<Self>;
    type ForeignId: SpecificDefId<Self>;
    type FunctionId: SpecificDefId<Self>;
    type ClosureId: SpecificDefId<Self>;
    type CoroutineClosureId: SpecificDefId<Self>;
    type CoroutineId: SpecificDefId<Self>;
    type AdtId: SpecificDefId<Self>;
    type ImplId: SpecificDefId<Self>;
    type UnevaluatedConstId: SpecificDefId<Self>;
    type Span: Span<Self>;

    type GenericArgs: GenericArgs<Self> + as_ref::GenericArgs<Self>;
    type GenericArgsRef<'a>: GenericArgsRef<'a, Self>
        + MyToOwned<Self, Owned = Self::GenericArgs>
        + reborrow::GenericArgsRef<'a, Self>
    where
        Self: 'a;
    type GenericArgsSlice<'a>: SliceLike<'a, Item = Self::GenericArgRef<'a>>
        + reborrow::GenericArgsSlice<'a, Self>
    where
        Self: 'a;
    type GenericArg: as_ref::GenericArg<Self>
        + TypeFoldable<Self>
        + From<Self::Ty>
        + From<Self::Region>
        + From<Self::Const>
        + From<Self::Term>
        + as_owned_kind::GenericArg<Self>;
    type GenericArgRef<'a>: GenericArg<'a, Self>
        + MyToOwned<Self, Owned = Self::GenericArg>
        + reborrow::GenericArgRef<'a, Self>
    where
        Self: 'a;
    type Term: as_ref::Term<Self> + Term<Self> + as_owned_kind::Term<Self>;
    type TermRef<'a>: TermRef<'a, Self>
        + MyToOwned<Self, Owned = Self::Term>
        + reborrow::TermRef<'a, Self>
    where
        Self: 'a;

    type BoundVarKinds: Default + as_ref::BoundVarKinds<Self>;
    type BoundVarKindsRef<'a>: SliceLike<'a, Item = Self::BoundVarKind>
        + Default
        + MyToOwned<Self, Owned = Self::BoundVarKinds>
        + reborrow::BoundVarKindsRef<'a, Self>
    where
        Self: 'a;
    type BoundVarKind: Copy + Debug + Hash + Eq;

    type PredefinedOpaques: as_ref::PredefinedOpaques<Self> + TypeFoldable<Self>;
    type PredefinedOpaquesRef<'a>: Debug
        + TypeVisitable<Self>
        + SliceLike<'a, Item = (ty::OpaqueTypeKey<Self>, Self::Ty)>
        + MyToOwned<Self, Owned = Self::PredefinedOpaques>
        + reborrow::PredefinedOpaquesRef<'a, Self>
    where
        Self: 'a;
    fn mk_predefined_opaques_in_body(
        self,
        data: &[(ty::OpaqueTypeKey<Self>, Self::Ty)],
    ) -> Self::PredefinedOpaques;

    type LocalDefIds: Default + as_ref::LocalDefIds<Self>;
    type LocalDefIdsRef<'a>: Debug
        + Default
        + TypeVisitable<Self>
        + SliceLike<'a, Item = Self::LocalDefId>
        + MyToOwned<Self, Owned = Self::LocalDefIds>
        + reborrow::LocalDefIdsRef<'a, Self>
    where
        Self: 'a;

    type CanonicalVarKinds: as_ref::CanonicalVarKinds<Self> + Default;
    type CanonicalVarKindsRef<'a>: Debug
        + SliceLike<'a, Item = ty::CanonicalVarKind<Self>>
        + Default
        + MyToOwned<Self, Owned = Self::CanonicalVarKinds>
        + reborrow::CanonicalVarKindsRef<'a, Self>
    where
        Self: 'a;
    fn mk_canonical_var_kinds(
        self,
        kinds: &[ty::CanonicalVarKind<Self>],
    ) -> Self::CanonicalVarKinds;

    type ExternalConstraints: as_ref::ExternalConstraints<Self>
        + Deref<Target = ExternalConstraintsData<Self>>
        + TypeFoldable<Self>;
    type ExternalConstraintsRef<'a>: Debug
        + TypeVisitable<Self>
        + Deref<Target = ExternalConstraintsData<Self>>
        + MyToOwned<Self, Owned = Self::ExternalConstraints>
        + reborrow::ExternalConstraintsRef<'a, Self>
    where
        Self: 'a;
    fn mk_external_constraints(
        self,
        data: ExternalConstraintsData<Self>,
    ) -> Self::ExternalConstraints;

    type DepNodeIndex;
    type Tracked<T: Debug + Clone>: Debug;
    fn mk_tracked<T: Debug + Clone>(
        self,
        data: T,
        dep_node: Self::DepNodeIndex,
    ) -> Self::Tracked<T>;
    fn get_tracked<T: Debug + Clone>(self, tracked: &Self::Tracked<T>) -> T;
    fn with_cached_task<T>(self, task: impl FnOnce() -> T) -> (T, Self::DepNodeIndex);

    // Kinds of tys
    type Ty: Ty<Self> + as_ref::Ty<Self>;
    type TyRef<'a>: TyRef<'a, Self> + MyToOwned<Self, Owned = Self::Ty> + reborrow::TyRef<'a, Self>
    where
        Self: 'a;
    type Tys: as_ref::Tys<Self> + TypeVisitable<Self> + TypeFoldable<Self> + Default;
    type TysRef<'a>: Tys<'a, Self> + MyToOwned<Self, Owned = Self::Tys> + reborrow::TysRef<'a, Self>
    where
        Self: 'a;
    type FnInputTys<'a>: Copy
        + Debug
        + Hash
        + Eq
        + SliceLike<'a, Item = Self::TyRef<'a>>
        + TypeVisitable<Self>
        + reborrow::FnInputTys<'a, Self>
    where
        Self: 'a;
    type ParamTy: ParamLike;
    type BoundTy: BoundVarLike<Self>;
    type PlaceholderTy: PlaceholderLike<Self, Bound = Self::BoundTy>;
    type Symbol: Copy + Hash + PartialEq + Eq + Debug;

    // Things stored inside of tys
    type ErrorGuaranteed: Copy + Debug + Hash + Eq;
    type BoundExistentialPredicates: as_ref::BoundExistentialPredicates<Self> + TypeFoldable<Self>;
    type BoundExistentialPredicatesRef<'a>: BoundExistentialPredicates<'a, Self>
        + MyToOwned<Self, Owned = Self::BoundExistentialPredicates>
        + reborrow::BoundExistentialPredicatesRef<'a, Self>
    where
        Self: 'a;
    type AllocId: Copy + Debug + Hash + Eq;
    type Pat: Copy
        + Debug
        + Hash
        + Eq
        + Debug
        + RelateRef<Self>
        + TypeFoldable<Self>
        + Flags
        + AsKind<Kind = ty::PatternKind<Self>>;
    type PatList: as_ref::PatList<Self> + TypeVisitable<Self>;
    type PatListRef<'a>: Copy
        + Debug
        + Hash
        + Default
        + Eq
        + TypeVisitable<Self>
        + SliceLike<'a, Item = Self::Pat>
        + MyToOwned<Self, Owned = Self::PatList>
        + reborrow::PatListRef<'a, Self>
    where
        Self: 'a;
    type Safety: Safety<Self>;
    type Abi: Abi<Self>;

    // Kinds of consts
    type Const: Const<Self> + as_ref::Const<Self>;
    type ConstRef<'a>: AnyConst<Self>
        + Relate<Self, RelateResult = Self::Const>
        + AsKindRef<'a, Kind = ty::ConstKind<Self>>
        + Into<Self::GenericArgRef<'a>>
        + Into<Self::TermRef<'a>>
        + MyToOwned<Self, Owned = Self::Const>
        + reborrow::ConstRef<'a, Self>
    where
        Self: 'a;
    type ParamConst: Copy + Debug + Hash + Eq + ParamLike;
    type BoundConst: BoundVarLike<Self>;
    type PlaceholderConst: PlaceholderConst<Self>;
    type ValueConst: ValueConst<Self>;
    type ExprConst: ExprConst<Self>;
    type ValTree: Clone + Debug + Hash + Eq;

    // Kinds of regions
    type Region: Region<Self> + as_ref::Region<Self>;
    type RegionRef<'a>: AnyRegion<Self>
        + Relate<Self, RelateResult = Self::Region>
        + Into<Self::GenericArgRef<'a>>
        + MyToOwned<Self, Owned = Self::Region>
        + reborrow::RegionRef<'a, Self>
    where
        Self: 'a;
    type EarlyParamRegion: ParamLike;
    type LateParamRegion: Copy + Debug + Hash + Eq;
    type BoundRegion: BoundVarLike<Self>;
    type PlaceholderRegion: PlaceholderLike<Self, Bound = Self::BoundRegion>;

    type RegionAssumptions: as_ref::RegionAssumptions<Self> + Debug + Hash + Eq + TypeFoldable<Self>;
    type RegionAssumptionsRef<'a>: Copy
        + Debug
        + Hash
        + Eq
        + SliceLike<'a, Item = ty::OutlivesPredicate<Self, Self::GenericArg>>
        + TypeVisitable<Self>
        + MyToOwned<Self, Owned = Self::RegionAssumptions>
        + reborrow::RegionAssumptionsRef<'a, Self>
    where
        Self: 'a;

    // Predicates
    type ParamEnv: as_ref::ParamEnv<Self> + TypeFoldable<Self>;
    type ParamEnvRef<'a>: ParamEnv<'a, Self>
        + MyToOwned<Self, Owned = Self::ParamEnv>
        + reborrow::ParamEnvRef<'a, Self>
    where
        Self: 'a;
    type Predicate: Predicate<Self> + as_ref::Predicate<Self>;
    type PredicateRef<'a>: PredicateRef<'a, Self>
        + MyToOwned<Self, Owned = Self::Predicate>
        + reborrow::PredicateRef<'a, Self>
    where
        Self: 'a;
    type Clause: Clause<Self> + as_ref::Clause<Self>;
    type ClauseRef<'a>: ClauseRef<'a, Self>
        + MyToOwned<Self, Owned = Self::Clause>
        + reborrow::ClauseRef<'a, Self>
    where
        Self: 'a;
    type Clauses: TypeSuperVisitable<Self> + TypeSuperFoldable<Self> + Flags + as_ref::Clauses<Self>;
    type ClausesRef<'a>: Clauses<'a, Self>
        + MyToOwned<Self, Owned = Self::Clauses>
        + reborrow::ClausesRef<'a, Self>
    where
        Self: 'a;

    fn mk_args(self, args: &[Self::GenericArgRef<'_>]) -> Self::GenericArgs;

    fn mk_args_owned(self, args: &[Self::GenericArg]) -> Self::GenericArgs;

    fn mk_args_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: CollectAndApply<Self::GenericArg, Self::GenericArgs>;

    fn next_trait_solver_globally(self) -> bool {
        true
    }

    fn with_global_cache<R>(self, f: impl FnOnce(&mut search_graph::GlobalCache<Self>) -> R) -> R;

    fn canonical_param_env_cache_get_or_insert<R>(
        self,
        param_env: Self::ParamEnvRef<'_>,
        f: impl FnOnce() -> CanonicalParamEnvCacheEntry<Self>,
        from_entry: impl FnOnce(&CanonicalParamEnvCacheEntry<Self>) -> R,
    ) -> R;

    /// Useful for testing. If a cache entry is replaced, this should
    /// (in theory) only happen when concurrent.
    fn assert_evaluation_is_concurrent(&self);

    fn expand_abstract_consts<T: TypeFoldable<Self>>(self, t: T) -> T;

    type GenericsOf: GenericsOf<Self>;
    fn generics_of(self, def_id: Self::DefId) -> Self::GenericsOf;

    type VariancesOf: VariancesOf + Debug + as_ref::VariancesOf<Self>;
    type VariancesOfRef<'a>: Copy
        + Debug
        + SliceLike<'a, Item = ty::Variance>
        + MyToOwned<Self, Owned = Self::VariancesOf>
    where
        Self: 'a;
    fn variances_of(self, def_id: Self::DefId) -> Self::VariancesOf;

    fn opt_alias_variances(
        self,
        kind: impl Into<ty::AliasTermKind>,
        def_id: Self::DefId,
    ) -> Option<Self::VariancesOf>;

    fn type_of(self, def_id: Self::DefId) -> ty::EarlyBinder<Self, Self::Ty>;
    fn type_of_opaque_hir_typeck(self, def_id: Self::LocalDefId)
    -> ty::EarlyBinder<Self, Self::Ty>;
    fn const_of_item(self, def_id: Self::DefId) -> ty::EarlyBinder<Self, Self::Const>;

    type AdtDef: AdtDef<Self>;
    fn adt_def(self, adt_def_id: Self::AdtId) -> Self::AdtDef;

    fn alias_ty_kind(self, alias: &ty::AliasTy<Self>) -> ty::AliasTyKind;

    fn alias_term_kind(self, alias: &ty::AliasTerm<Self>) -> ty::AliasTermKind;

    fn trait_ref_and_own_args_for_alias<'a>(
        self,
        def_id: Self::DefId,
        args: Self::GenericArgsRef<'a>,
    ) -> (ty::TraitRef<Self>, Self::GenericArgsSlice<'a>)
    where
        Self: 'a;

    fn check_args_compatible(self, def_id: Self::DefId, args: Self::GenericArgsRef<'_>) -> bool;

    fn debug_assert_args_compatible(self, def_id: Self::DefId, args: Self::GenericArgsRef<'_>);

    /// Assert that the args from an `ExistentialTraitRef` or `ExistentialProjection`
    /// are compatible with the `DefId`.
    fn debug_assert_existential_args_compatible(
        self,
        def_id: Self::DefId,
        args: Self::GenericArgsRef<'_>,
    );

    fn mk_type_list_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: CollectAndApply<Self::Ty, Self::Tys>;

    fn parent(self, def_id: Self::DefId) -> Self::DefId;

    fn recursion_limit(self) -> usize;

    type Features: Features<Self>;
    fn features(self) -> Self::Features;

    fn coroutine_hidden_types(
        self,
        def_id: Self::CoroutineId,
    ) -> ty::EarlyBinder<Self, ty::Binder<Self, ty::CoroutineWitnessTypes<Self>>>;

    fn fn_sig(
        self,
        def_id: Self::FunctionId,
    ) -> ty::EarlyBinder<Self, ty::Binder<Self, ty::FnSig<Self>>>;

    fn coroutine_movability(self, def_id: Self::CoroutineId) -> Movability;

    fn coroutine_for_closure(self, def_id: Self::CoroutineClosureId) -> Self::CoroutineId;

    fn generics_require_sized_self(self, def_id: Self::DefId) -> bool;

    fn item_bounds(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>>;

    fn item_self_bounds(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>>;

    fn item_non_self_bounds(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>>;

    fn predicates_of(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>>;

    fn own_predicates_of(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>>;

    fn explicit_super_predicates_of(
        self,
        def_id: Self::TraitId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = (Self::Clause, Self::Span)>>;

    fn explicit_implied_predicates_of(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = (Self::Clause, Self::Span)>>;

    /// This is equivalent to computing the super-predicates of the trait for this impl
    /// and filtering them to the outlives predicates. This is purely for performance.
    fn impl_super_outlives(
        self,
        impl_def_id: Self::ImplId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = Self::Clause>>;

    fn impl_is_const(self, def_id: Self::ImplId) -> bool;
    fn fn_is_const(self, def_id: Self::FunctionId) -> bool;
    fn alias_has_const_conditions(self, def_id: Self::DefId) -> bool;
    fn const_conditions(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = ty::Binder<Self, ty::TraitRef<Self>>>>;
    fn explicit_implied_const_bounds(
        self,
        def_id: Self::DefId,
    ) -> ty::EarlyBinder<Self, impl IntoIterator<Item = ty::Binder<Self, ty::TraitRef<Self>>>>;

    fn impl_self_is_guaranteed_unsized(self, def_id: Self::ImplId) -> bool;

    fn has_target_features(self, def_id: Self::FunctionId) -> bool;

    fn require_lang_item(self, lang_item: SolverLangItem) -> Self::DefId;

    fn require_trait_lang_item(self, lang_item: SolverTraitLangItem) -> Self::TraitId;

    fn require_adt_lang_item(self, lang_item: SolverAdtLangItem) -> Self::AdtId;

    fn is_lang_item(self, def_id: Self::DefId, lang_item: SolverLangItem) -> bool;

    fn is_trait_lang_item(self, def_id: Self::TraitId, lang_item: SolverTraitLangItem) -> bool;

    fn is_adt_lang_item(self, def_id: Self::AdtId, lang_item: SolverAdtLangItem) -> bool;

    fn is_default_trait(self, def_id: Self::TraitId) -> bool;

    fn is_sizedness_trait(self, def_id: Self::TraitId) -> bool;

    fn as_lang_item(self, def_id: Self::DefId) -> Option<SolverLangItem>;

    fn as_trait_lang_item(self, def_id: Self::TraitId) -> Option<SolverTraitLangItem>;

    fn as_adt_lang_item(self, def_id: Self::AdtId) -> Option<SolverAdtLangItem>;

    fn associated_type_def_ids(
        self,
        def_id: Self::TraitId,
    ) -> impl IntoIterator<Item = Self::DefId>;

    fn for_each_relevant_impl(
        self,
        trait_def_id: Self::TraitId,
        self_ty: Self::TyRef<'_>,
        f: impl FnMut(Self::ImplId),
    );
    fn for_each_blanket_impl(self, trait_def_id: Self::TraitId, f: impl FnMut(Self::ImplId));

    fn has_item_definition(self, def_id: Self::DefId) -> bool;

    fn impl_specializes(self, impl_def_id: Self::ImplId, victim_def_id: Self::ImplId) -> bool;

    fn impl_is_default(self, impl_def_id: Self::ImplId) -> bool;

    fn impl_trait_ref(self, impl_def_id: Self::ImplId)
    -> ty::EarlyBinder<Self, ty::TraitRef<Self>>;

    fn impl_polarity(self, impl_def_id: Self::ImplId) -> ty::ImplPolarity;

    fn trait_is_auto(self, trait_def_id: Self::TraitId) -> bool;

    fn trait_is_coinductive(self, trait_def_id: Self::TraitId) -> bool;

    fn trait_is_alias(self, trait_def_id: Self::TraitId) -> bool;

    fn trait_is_dyn_compatible(self, trait_def_id: Self::TraitId) -> bool;

    fn trait_is_fundamental(self, def_id: Self::TraitId) -> bool;

    fn trait_may_be_implemented_via_object(self, trait_def_id: Self::TraitId) -> bool;

    /// Returns `true` if this is an `unsafe trait`.
    fn trait_is_unsafe(self, trait_def_id: Self::TraitId) -> bool;

    fn is_impl_trait_in_trait(self, def_id: Self::DefId) -> bool;

    fn delay_bug(self, msg: impl ToString) -> Self::ErrorGuaranteed;

    fn is_general_coroutine(self, coroutine_def_id: Self::CoroutineId) -> bool;
    fn coroutine_is_async(self, coroutine_def_id: Self::CoroutineId) -> bool;
    fn coroutine_is_gen(self, coroutine_def_id: Self::CoroutineId) -> bool;
    fn coroutine_is_async_gen(self, coroutine_def_id: Self::CoroutineId) -> bool;

    type UnsizingParams: Deref<Target = DenseBitSet<u32>>;
    fn unsizing_params_for_adt(self, adt_def_id: Self::AdtId) -> Self::UnsizingParams;

    fn anonymize_bound_vars<T: TypeFoldable<Self>>(
        self,
        binder: ty::Binder<Self, T>,
    ) -> ty::Binder<Self, T>;

    fn opaque_types_defined_by(self, defining_anchor: Self::LocalDefId) -> Self::LocalDefIds;

    fn opaque_types_and_coroutines_defined_by(
        self,
        defining_anchor: Self::LocalDefId,
    ) -> Self::LocalDefIds;

    type Probe: Debug + Hash + Eq + Borrow<inspect::Probe<Self>>;
    fn mk_probe(self, probe: inspect::Probe<Self>) -> Self::Probe;
    fn evaluate_root_goal_for_proof_tree_raw(
        self,
        canonical_goal: CanonicalInput<Self>,
    ) -> (QueryResult<Self>, Self::Probe);
}

pub trait VariancesOf {
    fn into_iter(self) -> impl Iterator<Item = ty::Variance>;
}

impl VariancesOf for &[ty::Variance] {
    #[inline]
    fn into_iter(self) -> impl Iterator<Item = ty::Variance> {
        self.iter().copied()
    }
}

/// Imagine you have a function `F: FnOnce(&[T]) -> R`, plus an iterator `iter`
/// that produces `T` items. You could combine them with
/// `f(&iter.collect::<Vec<_>>())`, but this requires allocating memory for the
/// `Vec`.
///
/// This trait allows for faster implementations, intended for cases where the
/// number of items produced by the iterator is small. There is a blanket impl
/// for `T` items, but there is also a fallible impl for `Result<T, E>` items.
pub trait CollectAndApply<T, R>: Sized {
    type Output;

    /// Produce a result of type `Self::Output` from `iter`. The result will
    /// typically be produced by applying `f` on the elements produced by
    /// `iter`, though this may not happen in some impls, e.g. if an error
    /// occurred during iteration.
    fn collect_and_apply<I, F>(iter: I, f: F) -> Self::Output
    where
        I: Iterator<Item = Self>,
        F: FnOnce(&[T]) -> R;
}

/// The blanket impl that always collects all elements and applies `f`.
impl<T, R> CollectAndApply<T, R> for T {
    type Output = R;

    /// Equivalent to `f(&iter.collect::<Vec<_>>())`.
    fn collect_and_apply<I, F>(mut iter: I, f: F) -> R
    where
        I: Iterator<Item = T>,
        F: FnOnce(&[T]) -> R,
    {
        // This code is hot enough that it's worth specializing for the most
        // common length lists, to avoid the overhead of `Vec` creation.

        let Some(t0) = iter.next() else {
            return f(&[]);
        };

        let Some(t1) = iter.next() else {
            return f(&[t0]);
        };

        let Some(t2) = iter.next() else {
            return f(&[t0, t1]);
        };

        let Some(t3) = iter.next() else {
            return f(&[t0, t1, t2]);
        };

        let Some(t4) = iter.next() else {
            return f(&[t0, t1, t2, t3]);
        };

        let Some(t5) = iter.next() else {
            return f(&[t0, t1, t2, t3, t4]);
        };

        let Some(t6) = iter.next() else {
            return f(&[t0, t1, t2, t3, t4, t5]);
        };

        let Some(t7) = iter.next() else {
            return f(&[t0, t1, t2, t3, t4, t5, t6]);
        };

        let Some(t8) = iter.next() else {
            return f(&[t0, t1, t2, t3, t4, t5, t6, t7]);
        };

        f(&[t0, t1, t2, t3, t4, t5, t6, t7, t8].into_iter().chain(iter).collect::<Vec<_>>())
    }
}

/// A fallible impl that will fail, without calling `f`, if there are any
/// errors during collection.
impl<T, R, E> CollectAndApply<T, R> for Result<T, E> {
    type Output = Result<R, E>;

    /// Equivalent to `Ok(f(&iter.collect::<Result<Vec<_>>>()?))`.
    fn collect_and_apply<I, F>(mut iter: I, f: F) -> Result<R, E>
    where
        I: Iterator<Item = Result<T, E>>,
        F: FnOnce(&[T]) -> R,
    {
        // This code is hot enough that it's worth specializing for the most
        // common length lists, to avoid the overhead of `Vec` creation.

        let Some(t0) = iter.next() else {
            return Ok(f(&[]));
        };
        let t0 = t0?;

        let Some(t1) = iter.next() else {
            return Ok(f(&[t0]));
        };
        let t1 = t1?;

        let Some(t2) = iter.next() else {
            return Ok(f(&[t0, t1]));
        };
        let t2 = t2?;

        let Some(t3) = iter.next() else {
            return Ok(f(&[t0, t1, t2]));
        };
        let t3 = t3?;

        let Some(t4) = iter.next() else {
            return Ok(f(&[t0, t1, t2, t3]));
        };
        let t4 = t4?;

        let Some(t5) = iter.next() else {
            return Ok(f(&[t0, t1, t2, t3, t4]));
        };
        let t5 = t5?;

        let Some(t6) = iter.next() else {
            return Ok(f(&[t0, t1, t2, t3, t4, t5]));
        };
        let t6 = t6?;

        let Some(t7) = iter.next() else {
            return Ok(f(&[t0, t1, t2, t3, t4, t5, t6]));
        };
        let t7 = t7?;

        let Some(t8) = iter.next() else {
            return Ok(f(&[t0, t1, t2, t3, t4, t5, t6, t7]));
        };
        let t8 = t8?;

        Ok(f(&[Ok(t0), Ok(t1), Ok(t2), Ok(t3), Ok(t4), Ok(t5), Ok(t6), Ok(t7), Ok(t8)]
            .into_iter()
            .chain(iter)
            .collect::<Result<Vec<_>, _>>()?))
    }
}

impl<I: Interner> search_graph::Cx for I {
    type Input = CanonicalInput<I>;
    type Result = QueryResult<I>;
    type AmbiguityInfo = Certainty;

    type DepNodeIndex = I::DepNodeIndex;
    type Tracked<T: Debug + Clone> = I::Tracked<T>;
    fn mk_tracked<T: Debug + Clone>(
        self,
        data: T,
        dep_node_index: I::DepNodeIndex,
    ) -> I::Tracked<T> {
        I::mk_tracked(self, data, dep_node_index)
    }
    fn get_tracked<T: Debug + Clone>(self, tracked: &I::Tracked<T>) -> T {
        I::get_tracked(self, tracked)
    }
    fn with_cached_task<T>(self, task: impl FnOnce() -> T) -> (T, I::DepNodeIndex) {
        I::with_cached_task(self, task)
    }
    fn with_global_cache<R>(self, f: impl FnOnce(&mut search_graph::GlobalCache<Self>) -> R) -> R {
        I::with_global_cache(self, f)
    }
    fn assert_evaluation_is_concurrent(&self) {
        self.assert_evaluation_is_concurrent()
    }
}
