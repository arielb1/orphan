#![feature(globs, slicing_syntax, phase, macro_rules, if_let)]
#![allow(dead_code, non_upper_case_globals)]

#[phase(plugin, link)] extern crate log;

use std::fmt;

use Ty::Generic;
use Ty::Param;
use Ty::Simple;

#[deriving(PartialEq, Clone)]
struct CrateNum(u32);

impl fmt::Show for CrateNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CrateNum(n) = *self;
        write!(f, "{}", n)
    }
}

#[deriving(PartialEq, Clone)]
struct DefId {
    krate: CrateNum,
    // not using the node id
}

impl fmt::Show for DefId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}]", self.krate)
    }
}

#[deriving(PartialEq, Clone)]
enum Ty {
    Generic(DefId, Vec<Ty>),
    Simple(DefId), /* like generic, empty params */
    Param,
}

impl fmt::Show for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Param => write!(f, "T"),
            Simple(did) => write!(f, "{}", did),
            Generic(did, ref tys) if tys.is_empty() => write!(f, "{}", did),
            Generic(did, ref tys) => write!(f, "{}<{:#}>", did, tys)
        }
    }
}

#[deriving(PartialEq, Clone)]
struct TraitRef {
    def: DefId,
    self_ty: Ty,
    params: Vec<Ty>
}

impl TraitRef {
    fn new(def: DefId, self_ty: Ty, params: Vec<Ty>) -> TraitRef {
        TraitRef {
            def: def,
            self_ty: self_ty,
            params: params
        }
    }
}

impl fmt::Show for TraitRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.params.is_empty() {
            write!(f, "<{} for {}>", self.def, self.self_ty)
        } else {
            write!(f, "<{}<{:#}> for {}>", self.def, self.params,
                   self.self_ty)
        }
    }
}

/// Orphan Cheker
///
/// The orphan checker exists to prevent two separately-compiled
/// crates having different impls for the same TraitRef.
///
/// To state that in other words, if a substituted-TraitRef could
/// be implemented by 2 crates, then one of them must depend on the
/// other (so coherence can detect the overlap).
///
/// For example, `Path` doesn't currently implement `Show`, so
/// having an `impl Show for Path` in a new crate wouldn't violate
/// coherence, but such an impl can't be accepted: if 2 crates
/// have such an impl, with a different algorithm, it is unobvious
/// which one should be chosen by a crate that depends on both.
trait OrphanChecker {
    fn is_nonorphan(&self, tref: &TraitRef, in_crate: CrateNum) -> bool;
}

/// The order-based orphan checking algorithm.
///
/// Classically, orphan checking works by ensuring that the TraitRef
/// of every impl must contain a definition from the same crate as the impl.
///
/// However, this isn't sufficient. A small counterexample is:
///
/// crate base: trait Base<A> {}
/// crate  foo: struct Foo; impl<T> Base<T> for Foo {}
/// crate  bar: struct Bar; impl<T> Base<Bar> for T {}
///
/// and now, both impls are good for <Base<Bar> for Foo>.
struct PosetOrphanChecker {
    privileged_self: bool
}

impl OrphanChecker for PosetOrphanChecker {
    fn is_nonorphan(&self, tref: &TraitRef, krate: CrateNum) -> bool {
        // R0
        if tref.def.krate == krate {
            debug!("{} is not a {}-orphan by R0", tref, krate);
            return true;
        }

        // R1
        if ty_local(&tref.self_ty, krate) && (
            self.privileged_self || tref.params.iter().all(
                |p| ty_complete(p, krate))) {
            debug!("{} is not a {}-orphan by R1", tref, krate);
            return true;
        }

        // R2
        if ty_complete(&tref.self_ty, krate) &&
            tref.params.iter().all(|p| ty_complete(p, krate)) &&
            tref.params.iter().any(|p| ty_local(p, krate)) {
                debug!("{} is not a {}-orphan by R2", tref, krate);
            return true;
        }

        debug!("{} is a {}-orphan", tref, krate);

        false
    }
}

fn ty_free(t: &Ty) -> bool {
    match *t {
        Param => false,
        Simple(_) => true,
        Generic(_, ref params) => params.iter().all(|t| ty_free(t))
    }
}

fn ty_complete(t: &Ty, krate: CrateNum) -> bool {
    // C0
    if ty_free(t) {
        return true;
    }
    // C1
    if ty_local(t, krate) {
        return true;
    }
    false
}

// This has exponential complexity
// Can be fixed with a cache
fn ty_local(t: &Ty, krate: CrateNum) -> bool {
    match *t {
        Param => {},
        Simple(def) => {
            // T0
            if def.krate == krate {
                return true;
            }
            // T1 can't apply (no param exists)
        }
        Generic(def, ref params) => {
            // T0
            if def.krate == krate {
                debug!(" {} is {}-local by T0", t, krate);
                return true;
            }
            // T1
            if params.iter().all(|p| ty_complete(p, krate)) &&
                params.iter().any(|p| ty_local(p, krate)) {
                    debug!(" {} is {}-local by T1", t, krate);
                    return true;
            }
            debug!(" {} is not {}-local", t, krate);
        }
    }

    false
}

fn ok(d: DefId, s: Ty, p: Vec<Ty>) -> bool {
    let r = ok_ps(d, s.clone(), p.clone(), false);
    assert_eq!(r, ok_ps(d, s, p, true));
    r
}

fn ok_ps(d: DefId, s: Ty, p: Vec<Ty>, ps: bool) -> bool {
    PosetOrphanChecker { privileged_self: ps }.is_nonorphan(
        &TraitRef::new(d, s, p), FOO)
}

const CORE : CrateNum = CrateNum(0);
const FOO : CrateNum = CrateNum(1);
const BAR : CrateNum = CrateNum(2);
const COLLECTIONS: CrateNum = CrateNum(3);

const CORE_D : DefId = DefId { krate: CORE };
const FOO_D : DefId = DefId { krate: FOO };
const BAR_D : DefId = DefId { krate: BAR };
const COLLECTIONS_D: DefId = DefId { krate: COLLECTIONS };

const int_: Ty = Simple(CORE_D);
/// Primitive Foo
const foo_p: Ty = Simple(FOO_D);
/// Foo<T> (1 parameter)
fn foo_(t: Ty) -> Ty {
    Generic(FOO_D, vec![t])
}
/// Option<T>
fn option_(t: Ty) -> Ty {
    Generic(CORE_D, vec![t])
}
/// Vec<T>
fn vec_(t: Ty) -> Ty {
    Generic(COLLECTIONS_D, vec![t])
}
/// Foo::Items<T>
fn foo_items_(t: Ty) -> Ty {
    Generic(FOO_D, vec![t])
}


#[test]
fn lone_type_parameter() {
    /*! `impl<T> Show for T` -- not_ok */
    assert!(!ok(CORE_D, Param, vec![]));
}

#[test]
fn type_parameter() {
    /*! `impl<T> Show for Foo<T>` -- OK */
    assert!(ok(CORE_D, foo_(Param), vec![]));
}

#[test]
fn overlapping_pairs() {
    /*! `impl<T> Show for Pair<Option<T>, Option<Foo>>` -- Bad */

    // Bad because another crate could do:
    // impl<T> Show for Pair<Option<Bar>, Option<T>>

    let pair = Generic(CORE_D, vec![option_(Param), option_(foo_p)]);
    assert!(!ok(CORE_D, pair, vec![]));

}

#[test]
fn overlapping_pairs_self() {
    /*! `impl<T> Add<Foo> for T` -- Bad
        `impl<T> Add<T> for Foo` -- Only with privileged_self */

    assert!(!ok(CORE_D, Param, vec![foo_p]));
    assert!(ok_ps(CORE_D, foo_p, vec![Param], true));
    assert!(!ok_ps(CORE_D, foo_p, vec![Param], false));
}

#[test]
fn iterator_for_items() {
    /*! `impl<T> Iterator<T> for Items<T>` -- Only with privileged_self */
    assert!(ok_ps(CORE_D, foo_items_(Param), vec![Param], true));
    assert!(!ok_ps(CORE_D, foo_items_(Param), vec![Param], false));
}

#[test]
fn bigint_int() {
    /*! `impl Add<Foo> for int` -- OK */

    assert!(ok(CORE_D, int_, vec![foo_p]));
}

#[test]
fn bigint_param() {
    /*! `impl Add<Foo> for T` -- not OK */

    assert!(!ok(CORE_D, Param, vec![foo_p]));
}

#[test]
fn blanket() {
    /*! `impl<T> Foo for T` -- OK */

    assert!(ok(FOO_D, Param, vec![]));
}

#[test]
fn vec_local_1() {
    /*! `impl Clone for Vec<Foo>` -- OK */

    assert!(ok(CORE_D, vec_(foo_p), vec![]));
}

#[test]
fn vec_local_2() {
    /*! `impl<T> Clone for Vec<Foo<T>>` -- OK */

    assert!(ok(CORE_D, vec_(foo_(Param)), vec![]));
}

#[test]
fn bigint_vecint() {
    /*! `impl Add<Foo> for Vec<int>` -- OK */
    assert!(ok(CORE_D, vec_(int_), vec![foo_p]));
}

#[test]
fn all_remote() {
    /*! `impl Clone for int` -- not OK */
    assert!(!ok(CORE_D, int_, vec![]));
}
