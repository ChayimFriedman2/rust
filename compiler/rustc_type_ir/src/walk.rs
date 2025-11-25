//! An iterator over the type substructure.
//! WARNING: this does not keep track of the region depth.

use smallvec::{SmallVec, smallvec};
use tracing::debug;

use crate::data_structures::SsoHashSet;
use crate::inherent::*;
use crate::ir_traits::*;
use crate::{self as ty, Interner};

// The TypeWalker's stack is hot enough that it's worth going to some effort to
// avoid heap allocations.
type TypeWalkerStack<'a, I> = SmallVec<[<I as Interner>::GenericArgRef<'a>; 8]>;

/// An iterator for walking the type tree.
///
/// It's very easy to produce a deeply
/// nested type tree with a lot of
/// identical subtrees. In order to work efficiently
/// in this situation walker only visits each type once.
/// It maintains a set of visited types and
/// skips any types that are already there.
pub struct TypeWalker<'a, I: Interner + 'a> {
    stack: TypeWalkerStack<'a, I>,
    last_subtree: usize,
    pub visited: SsoHashSet<I::GenericArgRef<'a>>,
}

impl<'a, I: Interner> TypeWalker<'a, I> {
    pub fn new(root: I::GenericArgRef<'a>) -> Self {
        Self { stack: smallvec![root], last_subtree: 1, visited: SsoHashSet::new() }
    }

    /// Skips the subtree corresponding to the last type
    /// returned by `next()`.
    ///
    /// Example: Imagine you are walking `Foo<Bar<i32>, usize>`.
    ///
    /// ```ignore (illustrative)
    /// let mut iter: TypeWalker = ...;
    /// iter.next(); // yields Foo
    /// iter.next(); // yields Bar<i32>
    /// iter.skip_current_subtree(); // skips i32
    /// iter.next(); // yields usize
    /// ```
    pub fn skip_current_subtree(&mut self) {
        self.stack.truncate(self.last_subtree);
    }
}

impl<'a, I: Interner> Iterator for TypeWalker<'a, I> {
    type Item = I::GenericArgRef<'a>;

    fn next(&mut self) -> Option<I::GenericArgRef<'a>> {
        debug!("next(): stack={:?}", self.stack);
        loop {
            let next = self.stack.pop()?;
            self.last_subtree = self.stack.len();
            if self.visited.insert(next) {
                push_inner::<I>(&mut self.stack, next);
                debug!("next: stack={:?}", self.stack);
                return Some(next);
            }
        }
    }
}

/// We push `GenericArg`s on the stack in reverse order so as to
/// maintain a pre-order traversal. As of the time of this
/// writing, the fact that the traversal is pre-order is not
/// known to be significant to any code, but it seems like the
/// natural order one would expect (basically, the order of the
/// types as they are written).
fn push_inner<'a, I: Interner>(stack: &mut TypeWalkerStack<'a, I>, parent: I::GenericArgRef<'a>) {
    match parent.kind() {
        ty::GenericArgKind::Type(parent_ty) => match parent_ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Infer(_)
            | ty::Param(_)
            | ty::Never
            | ty::Error(_)
            | ty::Placeholder(..)
            | ty::Bound(..)
            | ty::Foreign(..) => {}

            ty::Pat(ty, pat) => {
                push_ty_pat::<I>(stack, pat);
                stack.push(ty.r().into());
            }
            ty::Array(ty, len) => {
                stack.push(len.r().into());
                stack.push(ty.r().into());
            }
            ty::Slice(ty) => {
                stack.push(ty.r().into());
            }
            ty::RawPtr(ty, _) => {
                stack.push(ty.r().into());
            }
            ty::Ref(lt, ty, _) => {
                stack.push(ty.r().into());
                stack.push(lt.r().into());
            }
            ty::Alias(_, data) => {
                stack.extend(data.args.r().iter().rev());
            }
            ty::Dynamic(obj, lt) => {
                stack.push(lt.r().into());
                stack.extend(
                    obj.r()
                        .iter_ref()
                        .rev()
                        .filter_map(|predicate| {
                            let (args, opt_ty) = match predicate.skip_binder_ref() {
                                ty::ExistentialPredicate::Trait(tr) => (tr.args.r(), None),
                                ty::ExistentialPredicate::Projection(p) => {
                                    (p.args.r(), Some(p.term.r()))
                                }
                                ty::ExistentialPredicate::AutoTrait(_) => {
                                    return None;
                                }
                            };

                            Some(args.iter().rev().chain(opt_ty.map(|term| match term.kind() {
                                ty::TermKind::Ty(ty) => ty.into(),
                                ty::TermKind::Const(ct) => ct.into(),
                            })))
                        })
                        .flatten(),
                );
            }
            ty::Adt(_, args)
            | ty::Closure(_, args)
            | ty::CoroutineClosure(_, args)
            | ty::Coroutine(_, args)
            | ty::CoroutineWitness(_, args)
            | ty::FnDef(_, args) => {
                stack.extend(args.r().iter().rev());
            }
            ty::Tuple(ts) => stack.extend(ts.r().iter().rev().map(|ty| ty.into())),
            ty::FnPtr(sig_tys, _hdr) => {
                stack.extend(
                    sig_tys
                        .skip_binder_ref()
                        .inputs_and_output
                        .r()
                        .iter()
                        .rev()
                        .map(|ty| ty.into()),
                );
            }
            ty::UnsafeBinder(bound_ty) => {
                stack.push(bound_ty.skip_binder_ref().r().into());
            }
        },
        ty::GenericArgKind::Lifetime(_) => {}
        ty::GenericArgKind::Const(parent_ct) => match parent_ct.kind() {
            ty::ConstKind::Infer(_)
            | ty::ConstKind::Param(_)
            | ty::ConstKind::Placeholder(_)
            | ty::ConstKind::Bound(..)
            | ty::ConstKind::Error(_) => {}

            ty::ConstKind::Value(cv) => stack.push(cv.ty().into()),

            ty::ConstKind::Expr(expr) => stack.extend(expr.args().iter().rev()),
            ty::ConstKind::Unevaluated(ct) => {
                stack.extend(ct.args.r().iter().rev());
            }
        },
    }
}

fn push_ty_pat<'a, I: Interner>(stack: &mut TypeWalkerStack<'a, I>, pat: &'a I::Pat) {
    match pat.kind() {
        ty::PatternKind::Range { start, end } => {
            stack.push(end.r().into());
            stack.push(start.r().into());
        }
        ty::PatternKind::Or(pats) => {
            for pat in pats.r().iter_ref() {
                push_ty_pat::<I>(stack, pat)
            }
        }
        ty::PatternKind::NotNull => {}
    }
}
