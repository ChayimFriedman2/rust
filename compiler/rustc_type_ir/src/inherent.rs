//! Set of traits which are used to emulate the inherent impls that are present in `rustc_middle`.
//! It is customary to glob-import `rustc_type_ir::inherent::*` to bring all of these traits into
//! scope when programming in interner-agnostic settings, and to avoid importing any of these
//! directly elsewhere (i.e. specify the full path for an implementation downstream).

use std::fmt::Debug;
use std::hash::Hash;

use rustc_ast_ir::Mutability;

use crate::elaborate::Elaboratable;
use crate::fold::{TypeFoldable, TypeSuperFoldable};
use crate::ir_traits::*;
use crate::relate::{Relate, RelateRef};
use crate::solve::{AdtDestructorKind, SizedTraitKind};
use crate::visit::{Flags, TypeSuperVisitable, TypeVisitable, TypeVisitableExt};
use crate::{self as ty, CollectAndApply, Interner, UpcastFrom};

pub trait Ty<I: Interner<Ty = Self>>:
    Into<I::GenericArg> + Into<I::Term> + AnyTy<I> + RelateRef<I> + TypeSuperFoldable<I>
{
    fn new_unit(interner: I) -> Self;

    fn new_bool(interner: I) -> Self;

    fn new_u8(interner: I) -> Self;

    fn new_usize(interner: I) -> Self;

    fn new_infer(interner: I, var: ty::InferTy) -> Self;

    fn new_var(interner: I, var: ty::TyVid) -> Self;

    fn new_param(interner: I, param: I::ParamTy) -> Self;

    fn new_placeholder(interner: I, param: I::PlaceholderTy) -> Self;

    fn new_bound(interner: I, debruijn: ty::DebruijnIndex, var: I::BoundTy) -> Self;

    fn new_anon_bound(interner: I, debruijn: ty::DebruijnIndex, var: ty::BoundVar) -> Self;

    fn new_canonical_bound(interner: I, var: ty::BoundVar) -> Self;

    fn new_alias(interner: I, kind: ty::AliasTyKind, alias_ty: ty::AliasTy<I>) -> Self;

    fn new_projection_from_args(interner: I, def_id: I::DefId, args: I::GenericArgs) -> Self {
        Ty::new_alias(
            interner,
            ty::AliasTyKind::Projection,
            ty::AliasTy::new_from_args(interner, def_id, args),
        )
    }

    fn new_projection(
        interner: I,
        def_id: I::DefId,
        args: impl IntoIterator<Item: Into<I::GenericArg>>,
    ) -> Self {
        Ty::new_alias(
            interner,
            ty::AliasTyKind::Projection,
            ty::AliasTy::new(interner, def_id, args),
        )
    }

    fn new_error(interner: I, guar: I::ErrorGuaranteed) -> Self;

    fn new_adt(interner: I, adt_def: I::AdtDef, args: I::GenericArgs) -> Self;

    fn new_foreign(interner: I, def_id: I::ForeignId) -> Self;

    fn new_dynamic(interner: I, preds: I::BoundExistentialPredicates, region: I::Region) -> Self;

    fn new_coroutine(interner: I, def_id: I::CoroutineId, args: I::GenericArgs) -> Self;

    fn new_coroutine_closure(
        interner: I,
        def_id: I::CoroutineClosureId,
        args: I::GenericArgs,
    ) -> Self;

    fn new_closure(interner: I, def_id: I::ClosureId, args: I::GenericArgs) -> Self;

    fn new_coroutine_witness(interner: I, def_id: I::CoroutineId, args: I::GenericArgs) -> Self;

    fn new_coroutine_witness_for_coroutine(
        interner: I,
        def_id: I::CoroutineId,
        coroutine_args: I::GenericArgs,
    ) -> Self;

    fn new_ptr(interner: I, ty: Self, mutbl: Mutability) -> Self;

    fn new_ref(interner: I, region: I::Region, ty: Self, mutbl: Mutability) -> Self;

    fn new_array_with_const_len(interner: I, ty: Self, len: I::Const) -> Self;

    fn new_slice(interner: I, ty: Self) -> Self;
    fn new_tup(interner: I, tys: &[I::TyRef<'_>]) -> Self;

    fn new_tup_from_iter<It, T>(interner: I, iter: It) -> T::Output
    where
        It: Iterator<Item = T>,
        T: CollectAndApply<Self, Self>;

    fn new_fn_def(interner: I, def_id: I::FunctionId, args: I::GenericArgs) -> Self;

    fn new_fn_ptr(interner: I, sig: ty::Binder<I, ty::FnSig<I>>) -> Self;

    fn new_pat(interner: I, ty: Self, pat: I::Pat) -> Self;

    fn new_unsafe_binder(interner: I, ty: ty::Binder<I, I::Ty>) -> Self;

    fn from_closure_kind(interner: I, kind: ty::ClosureKind) -> Self;

    fn from_coroutine_closure_kind(interner: I, kind: ty::ClosureKind) -> Self;
}

pub trait TyRef<'a, I: Interner + 'a>:
    AsKindRef<'a, Kind = ty::TyKind<I>>
    + AnyTy<I>
    + Relate<I, RelateResult = I::Ty>
    + Into<I::GenericArgRef<'a>>
    + Into<I::TermRef<'a>>
{
    fn tuple_fields(self) -> I::TysRef<'a>;

    fn to_opt_closure_kind(self) -> Option<ty::ClosureKind>;

    /// Checks whether this type is an ADT that has unsafe fields.
    fn has_unsafe_fields(self) -> bool;

    fn discriminant_ty(self, interner: I) -> I::Ty;
}

pub trait AnyTy<I: Interner>:
    AsKind<Kind = ty::TyKind<I>>
    + Debug
    + Hash
    + Eq
    + AsKind<Kind = ty::TyKind<I>>
    + TypeSuperVisitable<I>
    + Flags
{
    fn is_ty_var(&self) -> bool {
        matches!(self.kind(), ty::Infer(ty::TyVar(_)))
    }

    fn is_ty_error(&self) -> bool {
        matches!(self.kind(), ty::Error(_))
    }

    fn is_floating_point(&self) -> bool {
        matches!(self.kind(), ty::Float(_) | ty::Infer(ty::FloatVar(_)))
    }

    fn is_integral(&self) -> bool {
        matches!(self.kind(), ty::Infer(ty::IntVar(_)) | ty::Int(_) | ty::Uint(_))
    }

    fn is_fn_ptr(&self) -> bool {
        matches!(self.kind(), ty::FnPtr(..))
    }

    fn fn_sig(&self, interner: I) -> ty::Binder<I, ty::FnSig<I>> {
        self.kind().fn_sig(interner)
    }

    fn is_known_rigid(&self) -> bool {
        self.kind().is_known_rigid()
    }

    fn is_guaranteed_unsized_raw(&self) -> bool {
        match self.kind() {
            ty::Dynamic(_, _) | ty::Slice(_) | ty::Str => true,
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Adt(_, _)
            | ty::Foreign(_)
            | ty::Array(_, _)
            | ty::Pat(_, _)
            | ty::RawPtr(_, _)
            | ty::Ref(_, _, _)
            | ty::FnDef(_, _)
            | ty::FnPtr(_, _)
            | ty::UnsafeBinder(_)
            | ty::Closure(_, _)
            | ty::CoroutineClosure(_, _)
            | ty::Coroutine(_, _)
            | ty::CoroutineWitness(_, _)
            | ty::Never
            | ty::Tuple(_)
            | ty::Alias(_, _)
            | ty::Param(_)
            | ty::Bound(_, _)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => false,
        }
    }
}

pub trait Tys<'a, I: Interner + 'a>:
    Copy + Debug + Hash + Eq + SliceLike<'a, Item = I::TyRef<'a>> + TypeVisitable<I> + Default
{
    fn inputs(self) -> I::FnInputTys<'a>;

    fn output(self) -> I::TyRef<'a>;
}

pub trait Abi<I: Interner<Abi = Self>>: Copy + Debug + Hash + Eq {
    fn rust() -> Self;

    /// Whether this ABI is `extern "Rust"`.
    fn is_rust(self) -> bool;
}

pub trait Safety<I: Interner<Safety = Self>>: Copy + Debug + Hash + Eq {
    fn safe() -> Self;

    fn is_safe(self) -> bool;

    fn prefix_str(self) -> &'static str;
}

pub trait Region<I: Interner<Region = Self>>:
    AnyRegion<I> + TypeFoldable<I> + RelateRef<I> + Into<I::GenericArg>
{
    fn new_bound(interner: I, debruijn: ty::DebruijnIndex, var: I::BoundRegion) -> Self;

    fn new_anon_bound(interner: I, debruijn: ty::DebruijnIndex, var: ty::BoundVar) -> Self;

    fn new_canonical_bound(interner: I, var: ty::BoundVar) -> Self;

    fn new_static(interner: I) -> Self;

    fn new_placeholder(interner: I, var: I::PlaceholderRegion) -> Self;
}

pub trait AnyRegion<I: Interner>:
    Sized + Debug + Hash + Eq + AsKind<Kind = ty::RegionKind<I>> + TypeVisitable<I> + Flags
{
    fn is_bound(&self) -> bool {
        matches!(self.kind(), ty::ReBound(..))
    }
}

pub trait Const<I: Interner<Const = Self>>:
    Into<I::GenericArg>
    + Into<I::Term>
    + AsKind<Kind = ty::ConstKind<I>>
    + TypeSuperFoldable<I>
    + AnyConst<I>
    + RelateRef<I>
{
    fn new_infer(interner: I, var: ty::InferConst) -> Self;

    fn new_var(interner: I, var: ty::ConstVid) -> Self;

    fn new_bound(interner: I, debruijn: ty::DebruijnIndex, bound_const: I::BoundConst) -> Self;

    fn new_anon_bound(interner: I, debruijn: ty::DebruijnIndex, var: ty::BoundVar) -> Self;

    fn new_canonical_bound(interner: I, var: ty::BoundVar) -> Self;

    fn new_placeholder(interner: I, param: I::PlaceholderConst) -> Self;

    fn new_unevaluated(interner: I, uv: ty::UnevaluatedConst<I>) -> Self;

    fn new_expr(interner: I, expr: I::ExprConst) -> Self;

    fn new_error(interner: I, guar: I::ErrorGuaranteed) -> Self;

    fn new_error_with_message(interner: I, msg: impl ToString) -> Self {
        Self::new_error(interner, interner.delay_bug(msg))
    }
}

pub trait AnyConst<I: Interner>:
    Debug + Hash + Eq + AsKind<Kind = ty::ConstKind<I>> + TypeSuperVisitable<I> + Flags
{
    fn is_ct_var(&self) -> bool {
        matches!(self.kind(), ty::ConstKind::Infer(ty::InferConst::Var(_)))
    }

    fn is_ct_error(&self) -> bool {
        matches!(self.kind(), ty::ConstKind::Error(_))
    }
}

pub trait ValueConst<I: Interner<ValueConst = Self>>: Clone + Debug + Hash + Eq {
    fn ty(&self) -> I::TyRef<'_>;
    fn valtree(&self) -> &I::ValTree;
}

pub trait ExprConst<I: Interner<ExprConst = Self>>:
    Copy + Debug + Hash + Eq + TypeFoldable<I> + RelateRef<I>
{
    fn args(&self) -> I::GenericArgsRef<'_>;
}

pub trait GenericsOf<I: Interner<GenericsOf = Self>> {
    fn count(&self) -> usize;
}

pub trait AsOwnedKindRef<'a> {
    type Kind;

    fn kind(self) -> Self::Kind;
}

pub trait GenericArg<'a, I: Interner + 'a>:
    Copy
    + Debug
    + Hash
    + Eq
    + AsOwnedKindRef<'a, Kind = ty::GenericArgKind<'a, I>>
    + TypeVisitable<I>
    + Relate<I, RelateResult = I::GenericArg>
    + From<I::TyRef<'a>>
    + From<I::RegionRef<'a>>
    + From<I::ConstRef<'a>>
    + From<I::TermRef<'a>>
{
    fn as_term(self) -> Option<I::TermRef<'a>> {
        match self.kind() {
            ty::GenericArgKind::Lifetime(_) => None,
            ty::GenericArgKind::Type(ty) => Some(ty.into()),
            ty::GenericArgKind::Const(ct) => Some(ct.into()),
        }
    }

    fn as_type(self) -> Option<I::TyRef<'a>> {
        if let ty::GenericArgKind::Type(ty) = self.kind() { Some(ty) } else { None }
    }

    fn expect_ty(self) -> I::TyRef<'a> {
        self.as_type().expect("expected a type")
    }

    fn as_const(self) -> Option<I::ConstRef<'a>> {
        if let ty::GenericArgKind::Const(c) = self.kind() { Some(c) } else { None }
    }

    fn expect_const(self) -> I::ConstRef<'a> {
        self.as_const().expect("expected a const")
    }

    fn as_region(self) -> Option<I::RegionRef<'a>> {
        if let ty::GenericArgKind::Lifetime(c) = self.kind() { Some(c) } else { None }
    }

    fn expect_region(self) -> I::RegionRef<'a> {
        self.as_region().expect("expected a const")
    }

    fn is_non_region_infer(self) -> bool {
        match self.kind() {
            ty::GenericArgKind::Lifetime(_) => false,
            ty::GenericArgKind::Type(ty) => ty.is_ty_var(),
            ty::GenericArgKind::Const(ct) => ct.is_ct_var(),
        }
    }
}

pub trait Term<I: Interner<Term = Self>>: TypeFoldable<I> + RelateRef<I> {
    fn into_type(self) -> Option<I::Ty>;

    fn expect_ty(self) -> I::Ty {
        self.into_type().expect("expected a type, but found a const")
    }

    fn into_const(self) -> Option<I::Const>;

    fn expect_const(self) -> I::Const {
        self.into_const().expect("expected a const, but found a type")
    }
}

pub trait TermRef<'a, I: Interner + 'a>:
    Copy
    + Debug
    + Hash
    + Eq
    + AsOwnedKindRef<'a, Kind = ty::TermKind<'a, I>>
    + TypeVisitable<I>
    + Relate<I, RelateResult = I::Term>
{
    fn as_type(self) -> Option<I::TyRef<'a>> {
        if let ty::TermKind::Ty(ty) = self.kind() { Some(ty) } else { None }
    }

    fn expect_ty(self) -> I::TyRef<'a> {
        self.as_type().expect("expected a type, but found a const")
    }

    fn as_const(self) -> Option<I::ConstRef<'a>> {
        if let ty::TermKind::Const(c) = self.kind() { Some(c) } else { None }
    }

    fn expect_const(self) -> I::ConstRef<'a> {
        self.as_const().expect("expected a const, but found a type")
    }

    fn is_infer(self) -> bool {
        match self.kind() {
            ty::TermKind::Ty(ty) => ty.is_ty_var(),
            ty::TermKind::Const(ct) => ct.is_ct_var(),
        }
    }

    fn is_error(self) -> bool {
        match self.kind() {
            ty::TermKind::Ty(ty) => ty.is_ty_error(),
            ty::TermKind::Const(ct) => ct.is_ct_error(),
        }
    }

    fn is_alias_term(self) -> bool {
        match self.kind() {
            ty::TermKind::Ty(ty) => match ty.kind() {
                ty::Alias(..) => true,
                _ => false,
            },
            ty::TermKind::Const(ct) => match ct.kind() {
                ty::ConstKind::Unevaluated(..) => true,
                _ => false,
            },
        }
    }

    fn to_alias_term(self) -> Option<ty::AliasTerm<I>> {
        match self.kind() {
            ty::TermKind::Ty(ty) => match ty.kind() {
                ty::Alias(_kind, alias_ty) => Some(alias_ty.clone().into()),
                _ => None,
            },
            ty::TermKind::Const(ct) => match ct.kind() {
                ty::ConstKind::Unevaluated(uv) => Some(uv.clone().into()),
                _ => None,
            },
        }
    }
}

pub trait GenericArgs<I: Interner<GenericArgs = Self>>:
    Clone + Debug + Hash + Eq + Default + RelateRef<I> + TypeFoldable<I>
{
}

impl<I, T> GenericArgs<I> for T
where
    I: Interner<GenericArgs = T>,
    T: Clone + Debug + Hash + Eq + Default + RelateRef<I> + TypeFoldable<I>,
{
}

pub trait GenericArgsRef<'a, I: Interner + 'a>:
    Copy
    + Debug
    + Hash
    + Eq
    + SliceLike<'a, Item = I::GenericArgRef<'a>>
    + Default
    + TypeVisitable<I>
    + Relate<I, RelateResult = I::GenericArgs>
{
    fn rebase_onto(
        self,
        interner: I,
        source_def_id: I::DefId,
        target: I::GenericArgsRef<'_>,
    ) -> I::GenericArgs;

    fn type_at(self, i: usize) -> I::TyRef<'a>;

    fn region_at(self, i: usize) -> I::RegionRef<'a>;

    fn const_at(self, i: usize) -> I::ConstRef<'a>;

    fn identity_for_item(interner: I, def_id: I::DefId) -> I::GenericArgs;

    fn extend_with_error(
        interner: I,
        def_id: I::DefId,
        original_args: &[I::GenericArg],
    ) -> I::GenericArgs;

    fn split_closure_args(self) -> ty::ClosureArgsParts<'a, I>;
    fn split_coroutine_closure_args(self) -> ty::CoroutineClosureArgsParts<'a, I>;
    fn split_coroutine_args(self) -> ty::CoroutineArgsParts<'a, I>;

    fn as_closure(self) -> ty::ClosureArgs<'a, I>;
    fn as_coroutine_closure(self) -> ty::CoroutineClosureArgs<'a, I>;
    fn as_coroutine(self) -> ty::CoroutineArgs<'a, I>;
}

pub trait Predicate<I: Interner>:
    Debug
    + Hash
    + Eq
    + TypeSuperVisitable<I>
    + TypeSuperFoldable<I>
    + Flags
    + UpcastFrom<I, ty::PredicateKind<I>>
    + UpcastFrom<I, ty::Binder<I, ty::PredicateKind<I>>>
    + UpcastFrom<I, ty::ClauseKind<I>>
    + UpcastFrom<I, ty::Binder<I, ty::ClauseKind<I>>>
    + UpcastFrom<I, I::Clause>
    + UpcastFrom<I, ty::NormalizesTo<I>>
    + UpcastFrom<I, ty::TraitRef<I>>
    + UpcastFrom<I, ty::Binder<I, ty::TraitRef<I>>>
    + UpcastFrom<I, ty::TraitPredicate<I>>
    + UpcastFrom<I, ty::OutlivesPredicate<I, I::Ty>>
    + UpcastFrom<I, ty::OutlivesPredicate<I, I::Region>>
    + AsKind<Kind = ty::Binder<I, ty::PredicateKind<I>>>
    + Elaboratable<I>
{
    fn as_clause(self) -> Option<I::Clause>;
}

pub trait PredicateRef<'a, I: Interner>:
    Copy
    + Debug
    + Hash
    + Eq
    + TypeSuperVisitable<I>
    + Flags
    + AsKindRef<'a, Kind = ty::Binder<I, ty::PredicateKind<I>>>
{
    fn as_clause(self) -> Option<I::ClauseRef<'a>>;

    fn as_normalizes_to(self) -> Option<ty::Binder<I, &'a ty::NormalizesTo<I>>> {
        let kind = self.kind();
        match kind.skip_binder_ref() {
            ty::PredicateKind::NormalizesTo(pred) => Some(kind.rebind(pred)),
            _ => None,
        }
    }

    // FIXME: Eventually uplift the impl out of rustc and make this defaulted.
    fn allow_normalization(self) -> bool;
}

pub trait Clause<I: Interner<Clause = Self>>:
    Debug
    + Hash
    + Eq
    + TypeVisitable<I>
    + TypeFoldable<I>
    + UpcastFrom<I, ty::Binder<I, ty::ClauseKind<I>>>
    + UpcastFrom<I, ty::TraitRef<I>>
    + UpcastFrom<I, ty::Binder<I, ty::TraitRef<I>>>
    + UpcastFrom<I, ty::TraitPredicate<I>>
    + UpcastFrom<I, ty::Binder<I, ty::TraitPredicate<I>>>
    + UpcastFrom<I, ty::ProjectionPredicate<I>>
    + UpcastFrom<I, ty::Binder<I, ty::ProjectionPredicate<I>>>
    + Elaboratable<I>
{
    fn as_predicate(self) -> I::Predicate;
}

pub trait ClauseRef<'a, I: Interner + 'a>:
    Copy
    + Debug
    + Hash
    + Eq
    + TypeVisitable<I>
    + AsOwnedKindRef<'a, Kind = ty::Binder<I, &'a ty::ClauseKind<I>>>
{
    fn as_predicate(self) -> I::PredicateRef<'a>;

    fn as_trait_clause(self) -> Option<ty::Binder<I, &'a ty::TraitPredicate<I>>> {
        self.kind()
            .map_bound_ref(
                |clause| if let ty::ClauseKind::Trait(t) = clause { Some(t) } else { None },
            )
            .transpose()
    }

    fn as_host_effect_clause(self) -> Option<ty::Binder<I, &'a ty::HostEffectPredicate<I>>> {
        self.kind()
            .map_bound_ref(
                |clause| if let ty::ClauseKind::HostEffect(t) = clause { Some(t) } else { None },
            )
            .transpose()
    }

    fn as_projection_clause(self) -> Option<ty::Binder<I, &'a ty::ProjectionPredicate<I>>> {
        self.kind()
            .map_bound_ref(
                |clause| {
                    if let ty::ClauseKind::Projection(p) = clause { Some(p) } else { None }
                },
            )
            .transpose()
    }

    /// Performs a instantiation suitable for going from a
    /// poly-trait-ref to supertraits that must hold if that
    /// poly-trait-ref holds. This is slightly different from a normal
    /// instantiation in terms of what happens with bound regions.
    fn instantiate_supertrait(self, cx: I, trait_ref: ty::Binder<I, &ty::TraitRef<I>>)
    -> I::Clause;
}

pub trait Clauses<'a, I: Interner + 'a>:
    Copy + Debug + Hash + Eq + TypeSuperVisitable<I> + Flags + SliceLike<'a, Item = I::ClauseRef<'a>>
{
}

/// Common capabilities of placeholder kinds
pub trait PlaceholderLike<I: Interner>: Copy + Debug + Hash + Eq {
    fn universe(self) -> ty::UniverseIndex;
    fn var(self) -> ty::BoundVar;

    type Bound: BoundVarLike<I>;
    fn new(ui: ty::UniverseIndex, bound: Self::Bound) -> Self;
    fn new_anon(ui: ty::UniverseIndex, var: ty::BoundVar) -> Self;
    fn with_updated_universe(self, ui: ty::UniverseIndex) -> Self;
}

pub trait PlaceholderConst<I: Interner>: PlaceholderLike<I, Bound = I::BoundConst> {
    fn find_const_ty_from_env(self, env: I::ParamEnvRef<'_>) -> I::TyRef<'_>;
}
impl<I: Interner> PlaceholderConst<I> for I::PlaceholderConst {
    fn find_const_ty_from_env(self, env: I::ParamEnvRef<'_>) -> I::TyRef<'_> {
        let mut candidates = env.caller_bounds().iter().filter_map(|clause: I::ClauseRef<'_>| {
            // `ConstArgHasType` are never desugared to be higher ranked.
            match clause.kind().skip_binder_ref() {
                ty::ClauseKind::ConstArgHasType(placeholder_ct, ty) => {
                    assert!(!(placeholder_ct, ty).has_escaping_bound_vars());

                    match placeholder_ct.kind() {
                        ty::ConstKind::Placeholder(placeholder_ct) if *placeholder_ct == self => {
                            Some(ty.r())
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        });

        // N.B. it may be tempting to fix ICEs by making this function return
        // `Option<Ty<'tcx>>` instead of `Ty<'tcx>`; however, this is generally
        // considered to be a bandaid solution, since it hides more important
        // underlying issues with how we construct generics and predicates of
        // items. It's advised to fix the underlying issue rather than trying
        // to modify this function.
        let ty = candidates.next().unwrap_or_else(|| {
            panic!("cannot find `{self:?}` in param-env: {env:#?}");
        });
        assert!(
            candidates.next().is_none(),
            "did not expect duplicate `ConstParamHasTy` for `{self:?}` in param-env: {env:#?}"
        );
        ty
    }
}

pub trait AsKindRef<'a> {
    type Kind;

    fn kind(self) -> &'a Self::Kind;
}

pub trait AsKind {
    type Kind;

    fn kind(&self) -> &Self::Kind;
}

impl<Kind, T: for<'a> AsKindRef<'a, Kind = Kind> + Copy> AsKind for T {
    type Kind = Kind;

    #[inline]
    fn kind(&self) -> &Self::Kind {
        <T as AsKindRef>::kind(*self)
    }
}

pub trait BoundVarLike<I: Interner>: Copy + Debug + Hash + Eq {
    fn var(self) -> ty::BoundVar;

    fn assert_eq(self, var: I::BoundVarKind);
}

pub trait ParamLike: Copy + Debug + Hash + Eq {
    fn index(self) -> u32;
}

pub trait AdtDef<I: Interner>: Copy + Debug + Hash + Eq {
    fn def_id(&self) -> I::AdtId;

    fn is_struct(&self) -> bool;

    /// Returns the type of the struct tail.
    ///
    /// Expects the `AdtDef` to be a struct. If it is not, then this will panic.
    fn struct_tail_ty(&self, interner: I) -> Option<ty::EarlyBinder<I, I::Ty>>;

    fn is_phantom_data(&self) -> bool;

    fn is_manually_drop(&self) -> bool;

    // FIXME: perhaps use `all_fields` and expose `FieldDef`.
    fn all_field_tys(&self, interner: I) -> ty::EarlyBinder<I, impl IntoIterator<Item = I::Ty>>;

    fn sizedness_constraint(
        &self,
        interner: I,
        sizedness: SizedTraitKind,
    ) -> Option<ty::EarlyBinder<I, I::Ty>>;

    fn is_fundamental(&self) -> bool;

    fn destructor(&self, interner: I) -> Option<AdtDestructorKind>;
}

pub trait ParamEnv<'a, I: Interner + 'a>: Copy + Debug + Hash + Eq + TypeVisitable<I> {
    fn caller_bounds(self) -> impl SliceLike<'a, Item = I::ClauseRef<'a>>;
}

pub trait Features<I: Interner>: Copy {
    fn generic_const_exprs(self) -> bool;

    fn coroutine_clone(self) -> bool;

    fn associated_const_equality(self) -> bool;

    fn feature_bound_holds_in_crate(self, symbol: I::Symbol) -> bool;
}

pub trait DefId<I: Interner>: Copy + Debug + Hash + Eq + TypeFoldable<I> {
    fn is_local(self) -> bool;

    fn as_local(self) -> Option<I::LocalDefId>;
}

pub trait SpecificDefId<I: Interner>:
    DefId<I> + Into<I::DefId> + TryFrom<I::DefId, Error: std::fmt::Debug>
{
}

impl<I: Interner, T: DefId<I> + Into<I::DefId> + TryFrom<I::DefId, Error: std::fmt::Debug>>
    SpecificDefId<I> for T
{
}

pub trait BoundExistentialPredicates<'a, I: Interner + 'a>:
    Copy
    + Debug
    + Hash
    + Eq
    + Relate<I, RelateResult = I::BoundExistentialPredicates>
    + SliceLike<'a, Item = ty::Binder<I, ty::ExistentialPredicate<I>>>
{
    fn principal_def_id(self) -> Option<I::TraitId>;

    fn principal(self) -> Option<ty::Binder<I, ty::ExistentialTraitRef<I>>>;

    fn auto_traits(self) -> impl IntoIterator<Item = I::TraitId>;

    fn projection_bounds(
        self,
    ) -> impl IntoIterator<Item = ty::Binder<I, ty::ExistentialProjection<I>>>;
}

pub trait Span<I: Interner>: Copy + Debug + Hash + Eq + TypeFoldable<I> {
    fn dummy() -> Self;
}

pub trait OpaqueTypeStorageEntries: Debug + Copy + Default {
    /// Whether the number of opaques has changed in a way that necessitates
    /// reevaluating a goal. For now, this is only when the number of non-duplicated
    /// entries changed.
    fn needs_reevaluation(self, canonicalized: usize) -> bool;
}

pub trait SliceLike<'a>: Sized + Copy {
    type Item: 'a;

    #[inline]
    fn iter_ref(self) -> std::slice::Iter<'a, Self::Item> {
        self.as_slice().iter()
    }

    #[inline]
    fn iter(self) -> std::iter::Copied<std::slice::Iter<'a, Self::Item>>
    where
        Self::Item: Copy,
    {
        self.iter_ref().copied()
    }

    fn as_slice(self) -> &'a [Self::Item];

    #[inline]
    fn get(self, idx: usize) -> Option<Self::Item>
    where
        Self::Item: Copy,
    {
        self.as_slice().get(idx).copied()
    }

    #[inline]
    fn len(self) -> usize {
        self.as_slice().len()
    }

    #[inline]
    fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[inline]
    fn contains(self, t: &Self::Item) -> bool
    where
        Self::Item: PartialEq,
    {
        self.as_slice().contains(t)
    }

    #[inline]
    fn last(self) -> Option<Self::Item>
    where
        Self::Item: Copy,
    {
        self.as_slice().last().copied()
    }

    #[inline]
    fn split_last(self) -> Option<(Self::Item, &'a [Self::Item])>
    where
        Self::Item: Copy,
    {
        self.as_slice().split_last().map(|(last, rest)| (*last, rest))
    }
}

impl<'a: 'b, 'b, T> SliceLike<'b> for &'a [T] {
    type Item = T;

    #[inline]
    fn as_slice(self) -> &'b [Self::Item] {
        self
    }
}

impl<'a: 'b, 'b, T, const N: usize> SliceLike<'b> for &'a [T; N] {
    type Item = T;

    #[inline]
    fn as_slice(self) -> &'b [Self::Item] {
        self
    }
}

impl<'a, 'b, S: SliceLike<'b>> SliceLike<'b> for &'a S {
    type Item = S::Item;

    #[inline]
    fn as_slice(self) -> &'b [Self::Item] {
        (*self).as_slice()
    }
}
