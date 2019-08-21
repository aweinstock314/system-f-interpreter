use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
enum FType {
    Var(String),
    Arr(Box<FType>, Box<FType>),
    Forall(String, Box<FType>),
}

impl FType {
    fn is_var(&self) -> bool { if let FType::Var(_) = self { true } else { false } }
    fn is_forall(&self) -> bool { if let FType::Forall(_, _) = self { true } else { false } }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum FTermChurch {
    Var(String),
    Lam(String, Box<FType>, Box<FTermChurch>),
    App(Box<FTermChurch>, Box<FTermChurch>),
    TLam(String, Box<FTermChurch>),
    TApp(Box<FTermChurch>, Box<FType>),
}

impl FTermChurch {
    fn is_var(&self) -> bool { if let FTermChurch::Var(_) = self { true } else { false } }
    fn is_lam(&self) -> bool {
        match self {
            FTermChurch::Lam(_, _, _) | FTermChurch::TLam(_, _) => true,
            _ => false,
        }
    }
    fn is_app(&self) -> bool { if let FTermChurch::App(_, _) = self { true } else { false } }
    fn is_tapp(&self) -> bool { if let FTermChurch::TApp(_, _) = self { true } else { false } }
    fn is_value(&self) -> bool { self.is_lam() }
}

fn parens_if<X: fmt::Display>(x: X, use_parens: bool) -> String {
    if use_parens {
        format!("({})", x)
    } else {
        format!("{}", x)
    }
}

impl fmt::Display for FType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::FType::*;
        match self {
            Var(x) => write!(f, "{}", x),
            Arr(x, y) => write!(f, "{} -> {}", parens_if(x, !x.is_var()), y),
            Forall(x, y) => write!(f, "forall {}, {}", x, y),
        }
    }
}

impl fmt::Display for FTermChurch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::FTermChurch::*;
        match self {
            Var(x) => write!(f, "{}", x),
            Lam(x, y, z) => write!(f, "lam {} : {} => {}", x, y, z),
            App(x, y) => write!(f, "{} {}", parens_if(x, !x.is_var()), parens_if(y, !y.is_var())),
            TLam(x, y) => write!(f, "tlam {} => {}", x, y),
            TApp(x, y) => write!(f, "{} [{}]", parens_if(x, x.is_lam()), y),
        }
    }
}
fn tvar<S: Into<String>>(x: S) -> FType { FType::Var(x.into()) }
fn arr(x: FType, y: FType) -> FType { FType::Arr(Box::new(x), Box::new(y)) }
fn forall<S: Into<String>>(x: S, y: FType) -> FType { FType::Forall(x.into(), Box::new(y)) }
fn var<S: Into<String>>(x: S) -> FTermChurch { FTermChurch::Var(x.into()) }
fn lam<S: Into<String>>(x: S, y: FType, z: FTermChurch) -> FTermChurch { FTermChurch::Lam(x.into(), Box::new(y), Box::new(z)) }
fn app(x: FTermChurch, y: FTermChurch) -> FTermChurch { FTermChurch::App(Box::new(x), Box::new(y)) }
fn tlam<S: Into<String>>(x: S, y: FTermChurch) -> FTermChurch { FTermChurch::TLam(x.into(), Box::new(y)) }
fn tapp(x: FTermChurch, y: FType) -> FTermChurch { FTermChurch::TApp(Box::new(x), Box::new(y)) }

fn gensym(orig: &str, avoid: &HashSet<String>) -> String {
    for i in 0u64.. {
        let ret = format!("{}{}", orig, i);
        if !avoid.contains(&ret[..]) {
            return ret;
        }
    }
    panic!("Somehow gensym used more than 2^{64} ids without finding anything?")
}

fn freevars_term(term: &FTermChurch) -> HashSet<String> {
    use self::FTermChurch::*;
    let mut r = HashSet::new();
    match term {
        Var(x) => { r.insert(x.clone()); },
        Lam(x, y, z) => { r.extend(freevars_term(&z)); r.remove(x); },
        App(x, y) => { r.extend(freevars_term(&x)); r.extend(freevars_term(&y)); },
        TLam(x, y) => { r.extend(freevars_term(&y)); }, // type variables don't shadow value variables
        TApp(x, y) => { r.extend(freevars_term(&x)); },
    }
    r
}

fn freetyvars_ty(ty: &FType) -> HashSet<String> {
    use self::FType::*;
    let mut r = HashSet::new();
    match ty {
        Var(x) => { r.insert(x.clone()); }
        Arr(x, y) => { r.extend(freetyvars_ty(&x)); r.extend(freetyvars_ty(&y)); }
        Forall(x, y) => { r.extend(freetyvars_ty(&y)); r.remove(x); }
    }
    r
}

fn freetyvars_term(term: &FTermChurch) -> HashSet<String> {
    use self::FTermChurch::*;
    let mut r = HashSet::new();
    match term {
        Var(_) => {},
        Lam(x, y, z) => { r.extend(freetyvars_ty(&y));  },
        App(x, y) => { r.extend(freetyvars_term(&x)); r.extend(freetyvars_term(&y)); },
        TLam(x, y) => { r.extend(freetyvars_term(&y)); r.remove(x); },
        TApp(x, y) => { r.extend(freetyvars_term(&x)); r.extend(freetyvars_ty(&y)); }
    }
    r
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum FContextElem {
    HasType(String, FType),
    TyVar(String),
}

fn alpha_eq_ty(x: FType, y: FType) -> bool {
    x == y // TODO: traverse into foralls
}

fn substtyvar_ty(name: &str, replacement: FType, ty: FType) -> FType {
    use self::FType::*;
    match ty {
        Var(x) => if x == name { replacement } else { tvar(x) },
        Arr(x, y) => arr(substtyvar_ty(name, replacement.clone(), *x), substtyvar_ty(name, replacement, *y)),
        Forall(x, y) => forall(x.as_ref(), if x == name { *y } else { substtyvar_ty(name, replacement, *y) }),
    }
}

fn typeinfer(primenv: &HashMap<String, FType>, ctx: &[FContextElem], term: FTermChurch) -> Option<FType> {
    use self::FTermChurch::*;
    match term {
        Var(x) => {
            ctx.iter().filter_map(|e| if let FContextElem::HasType(y, ty) = e { Some((y, ty)) } else { None }).find(|(y, _)| x == **y).map(|(_, ty)| ty.clone())
        },
        Lam(x, y, z) => {
            let mut ctx = ctx.to_vec();
            ctx.push(FContextElem::HasType(x, *y.clone()));
            typeinfer(primenv, &ctx, *z).map(|w| arr(*y, w))

        },
        App(x, y) => {
            typeinfer(primenv, ctx, *x).and_then(|t| typeinfer(primenv, ctx, *y).and_then(|b| {
                if let FType::Arr(a, b2) = &t { if b == **b2 { return Some(b); } }
                None
            }))
        },
        TLam(x, y) => {
            let mut ctx = ctx.to_vec();
            ctx.push(FContextElem::TyVar(x.clone()));
            typeinfer(primenv, &ctx, *y).map(|b| forall(x, b))
        },
        TApp(x, y) => {
            if let Some(FType::Forall(a, b)) = typeinfer(primenv, ctx, *x) {
                Some(substtyvar_ty(&a, *y, *b))
            } else {
                None
            }
        },
    }
}

//fn subst_captureavoid_binder(name: &str, replacement: X, term: 

fn substvar_term(name: &str, replacement: FTermChurch, term: FTermChurch) -> FTermChurch {
    use self::FTermChurch::*;
    match term {
        Var(ref x) => if x == name { replacement } else { term }
        Lam(x, y, z) => {
            let fvr = freevars_term(&replacement);
            let (newname, newbody) = match (x == name, fvr.contains(&x)) {
                (true, _) => (x, *z.clone()),
                (false, true) => {
                    let newname = gensym(&x, &fvr);
                    let x0 = substvar_term(&x, var(&*newname), *z);
                    let x1 = substvar_term(&name, replacement, x0.clone());
                    println!("{:?}\n{:?}\n{:?}", x, x0, x1);
                    (newname.clone(), x1)
                },
                (false, false) => { (x.to_string(), substvar_term(name, replacement, *z)) },
            };
            lam(newname, *y, newbody)
        },
        App(x, y) => app(substvar_term(name, replacement.clone(), *x), substvar_term(name, replacement, *y)),
        TLam(x, y) => tlam(x, substvar_term(name, replacement, *y)),
        TApp(x, y) => tapp(substvar_term(name, replacement.clone(), *x), *y)
    }
}

fn substtyvar_term(name: &str, replacement: FType, term: FTermChurch) -> FTermChurch {
    use self::FTermChurch::*;
    match term {
        Var(_) => term,
        Lam(x, y, z) => lam(x, substtyvar_ty(name, replacement.clone(), *y), substtyvar_term(name, replacement, *z)),
        App(x, y) => app(substtyvar_term(name, replacement.clone(), *x), substtyvar_term(name, replacement, *y)),
        TLam(x, y) => {
            let fvr = freetyvars_ty(&replacement);
            let (newname, newbody) = match (x == name, fvr.contains(&x)) {
                (true, _) => (x, *y.clone()),
                (false, true) => {
                    let newname = gensym(&x, &fvr);
                    let x0 = substtyvar_term(&x, tvar(&*newname), *y);
                    let x1 = substtyvar_term(&name, replacement, x0);
                    (newname.clone(), x1)
                },
                (false, false) => { (name.to_string(), substtyvar_term(&x, replacement, *y)) },
            };
            tlam(newname, newbody)
        },
        TApp(x, y) => tapp(substtyvar_term(name, replacement.clone(), *x), substtyvar_ty(name, replacement, *y)),
    }
}

fn smallstep(term: FTermChurch) -> Option<FTermChurch> {
    use self::FTermChurch::*;
    match term {
        Var(_) => None,
        Lam(_, _, _) => None,
        App(e1, e2) => {
            if !e1.is_value() { let r = smallstep(*e1.clone()).map(|x| app(x, *e2.clone())); if r.is_some() { return r; } }
            if !e2.is_value() { let r = smallstep(*e2.clone()).map(|x| app(*e1.clone(), x)); if r.is_some() { return r; } }
            match *e1 {
                Lam(x, _, z) => return Some(substvar_term(&x, *e2, *z)),
                _ => (),
            }
            None
        }
        TLam(x, y) => smallstep(*y).map(|t| tlam(x, t)),
        TApp(x, y) => match *x {
            TLam(a, b) => Some(substtyvar_term(&a, *y, *b)),
            _ => None
        }
    }
}

fn main() {
    let succ = var("succ");
    let nat = tvar("nat");
    let double = { let x = tvar("X"); tlam("X", lam("f", arr(x.clone(), x.clone()), lam("a", x.clone(), app(var("f"), app(var("f"), var("a")))))) };
    let example = { app(tapp(double.clone(), nat.clone()), lam("x", nat, app(succ.clone(), app(succ.clone(), var("x"))))) };
    println!("double = {}", double);
    let x_arr_x = arr(tvar("X"), tvar("X"));
    let tdouble = forall("X", arr(x_arr_x.clone(), x_arr_x.clone()));
    let inferred = typeinfer(&HashMap::new(), &[], double.clone());
    println!("typeinfer result for double: {:?}", inferred.clone().map(|x| format!("{}", x)));
    println!("expected type of double = {}, equivalent to inferred: {}", tdouble.clone(), inferred == Some(tdouble));
    println!("example = {}", example);
    let natctx = [FContextElem::TyVar("nat".into())];
    let natenv = [("succ".into(), arr(tvar("nat"), tvar("nat")))].iter().cloned().collect::<HashMap<String, FType>>();
    println!("natctx = {:?}", natctx);
    println!("typeinfer result for example: {:?}", typeinfer(&natenv, &natctx, example.clone()).map(|x| format!("{}", x)));
    let idnat = lam("x", tvar("nat"), var("x"));
    let mut tmp = Some(app(example, var("0")));
    while let Some(old) = tmp {
        let new = smallstep(old.clone());
        println!("{} --> {:?}", old, new.clone().map(|x| format!("{}", x)));
        tmp = new;
    }
}
