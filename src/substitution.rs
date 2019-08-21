use super::*;

pub fn gensym(orig: &str, avoid: &HashSet<String>) -> String {
    for i in 0u64.. {
        let ret = format!("{}{}", orig, i);
        if !avoid.contains(&ret[..]) {
            return ret;
        }
    }
    panic!("Somehow gensym used more than 2^{64} ids without finding anything?")
}

pub fn freevars_term(term: &FTermChurch) -> HashSet<String> {
    use self::FTermChurch::*;
    let mut r = HashSet::new();
    match term {
        Var(x) => { r.insert(x.clone()); },
        Lam(x, _, z) => { r.extend(freevars_term(&z)); r.remove(x); },
        App(x, y) => { r.extend(freevars_term(&x)); r.extend(freevars_term(&y)); },
        TLam(_, y) => { r.extend(freevars_term(&y)); }, // type variables don't shadow value variables
        TApp(x, _) => { r.extend(freevars_term(&x)); },
    }
    r
}

pub fn freetyvars_ty(ty: &FType) -> HashSet<String> {
    use self::FType::*;
    let mut r = HashSet::new();
    match ty {
        Var(x) => { r.insert(x.clone()); }
        Arr(x, y) => { r.extend(freetyvars_ty(&x)); r.extend(freetyvars_ty(&y)); }
        Forall(x, y) => { r.extend(freetyvars_ty(&y)); r.remove(x); }
    }
    r
}

pub fn freetyvars_term(term: &FTermChurch) -> HashSet<String> {
    use self::FTermChurch::*;
    let mut r = HashSet::new();
    match term {
        Var(_) => {},
        Lam(_, y, z) => { r.extend(freetyvars_ty(&y)); r.extend(freetyvars_term(&z)); },
        App(x, y) => { r.extend(freetyvars_term(&x)); r.extend(freetyvars_term(&y)); },
        TLam(x, y) => { r.extend(freetyvars_term(&y)); r.remove(x); },
        TApp(x, y) => { r.extend(freetyvars_term(&x)); r.extend(freetyvars_ty(&y)); }
    }
    r
}

pub fn substtyvar_ty(name: &str, replacement: FType, ty: FType) -> FType {
    use self::FType::*;
    match ty {
        Var(x) => if x == name { replacement } else { tvar(x) },
        Arr(x, y) => arr(substtyvar_ty(name, replacement.clone(), *x), substtyvar_ty(name, replacement, *y)),
        Forall(x, y) => { let (newname, newbody) = subst_captureavoid_binder(name, replacement, &*x, *y, freetyvars_ty, substtyvar_ty, tvar); forall(newname, newbody) },
    }
}

pub fn subst_captureavoid_binder<X, Y, FV, SR, V>(name: &str, replacement: X, oldname: &str, oldbody: Y, freevars: FV, subst_rec: SR, mkvar: V) -> (String, Y) 
    where Y: Clone, FV: Fn(&X) -> HashSet<String>, SR: Fn(&str, X, Y) -> Y, V: Fn(String) -> X {
    let fvr = freevars(&replacement);
    let (newname, newbody) = match (oldname == name, fvr.contains(oldname)) {
        (true, _) => (oldname.into(), oldbody.clone()),
        (false, true) => {
            let newname = gensym(oldname, &fvr);
            let body0 = subst_rec(oldname, mkvar(newname.clone()), oldbody);
            let body1 = subst_rec(name, replacement, body0.clone());
            (newname.clone(), body1)
        },
        (false, false) => { (oldname.to_string(), subst_rec(name, replacement, oldbody)) },
    };
    (newname, newbody)
}

pub fn substvar_term(name: &str, replacement: FTermChurch, term: FTermChurch) -> FTermChurch {
    use self::FTermChurch::*;
    match term {
        Var(ref x) => if x == name { replacement } else { term }
        Lam(x, y, z) => { let (newname, newbody) = subst_captureavoid_binder(name, replacement, &*x, *z, freevars_term, substvar_term, var); lam(newname, *y, newbody) },
        App(x, y) => app(substvar_term(name, replacement.clone(), *x), substvar_term(name, replacement, *y)),
        TLam(x, y) => tlam(x, substvar_term(name, replacement, *y)),
        TApp(x, y) => tapp(substvar_term(name, replacement.clone(), *x), *y)
    }
}

pub fn substtyvar_term(name: &str, replacement: FType, term: FTermChurch) -> FTermChurch {
    use self::FTermChurch::*;
    match term {
        Var(_) => term,
        Lam(x, y, z) => lam(x, substtyvar_ty(name, replacement.clone(), *y), substtyvar_term(name, replacement, *z)),
        App(x, y) => app(substtyvar_term(name, replacement.clone(), *x), substtyvar_term(name, replacement, *y)),
        TLam(x, y) => { let (newname, newbody) = subst_captureavoid_binder(name, replacement, &*x, *y, freetyvars_ty, substtyvar_term, tvar); tlam(newname, newbody) }
        TApp(x, y) => tapp(substtyvar_term(name, replacement.clone(), *x), substtyvar_ty(name, replacement, *y)),
    }
}
