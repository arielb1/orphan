#![feature(globs, slicing_syntax, phase, macro_rules, if_let)]
#![allow(dead_code, non_upper_case_globals)]

#[phase(plugin, link)] extern crate log;

use Ty::Generic;
use Ty::Param;
use Ty::Simple;

#[deriving(PartialEq, Show, Clone)]
struct CrateNum(u32);

#[deriving(PartialEq, Show, Clone)]
struct DefId {
    krate: CrateNum,
    // not using the node id
}

#[deriving(PartialEq, Show, Clone)]
enum Ty {
    Generic(DefId, Vec<Ty>),
    Simple(DefId), /* like generic, empty params */
    Param,
}

#[deriving(Show)]
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

trait OrphanChecker {
    fn is_nonorphan(&self, tref: &TraitRef, in_crate: CrateNum) -> bool;
}

struct PosetOrphanChecker {
    privileged_self: bool
}

impl OrphanChecker for PosetOrphanChecker {
    fn is_nonorphan(&self, tref: &TraitRef, krate: CrateNum) -> bool {
        // R0
        if tref.def.krate == krate {
            debug!("{} is not an orphan by R0", tref);
            return true;
        }

        // R1
        if ty_local(&tref.self_ty, krate) && (
            self.privileged_self || tref.params.iter().all(
                |p| ty_complete(p, krate))) {
            debug!("{} is not an orphan by R1", tref);
            return true;
        }

        // R2
        if ty_complete(&tref.self_ty, krate) &&
            tref.params.iter().all(|p| ty_complete(p, krate)) &&
            tref.params.iter().any(|p| ty_local(p, krate)) {
                debug!("{} is not an orphan by R2", tref);
            return true;
        }

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
                debug!(" {} is local by T0", t);
                return true;
            }
            // T1
            if params.iter().all(|p| ty_complete(p, krate)) &&
                params.iter().any(|p| ty_local(p, krate)) {
                    debug!(" {} is local by T1", t);
                    return true;
            }
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
