use std::collections::HashSet;
use std::fmt;

#[derive(Clone, Debug)]
enum FType {
    Var(String),
    Arr(Box<FType>, Box<FType>),
    Forall(String, Box<FType>),
}

impl FType {
    fn is_forall(&self) -> bool { if let FType::Forall(_, _) = self { true } else { false } }
}

#[derive(Clone, Debug)]
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
            Arr(x, y) => write!(f, "{} -> {}", parens_if(x, x.is_forall()), y),
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

fn freevars(term: &FTermChurch) -> HashSet<String> {
    use self::FTermChurch::*;
    let mut r = HashSet::new();
    match term {
        Var(x) => { r.insert(x.clone()); },
        Lam(x, y, z) => { r.extend(freevars(&z)); r.remove(x); },
        App(x, y) => { r.extend(freevars(&x)); r.extend(freevars(&y)); },
        TLam(x, y) => { r.extend(freevars(&y)); }, // type variables don't shadow value variables
        TApp(x, y) => { r.extend(freevars(&x)); },
    }
    r
}

fn freetyvarsty(ty: &FType) -> HashSet<String> {
    use self::FType::*;
    let mut r = HashSet::new();
    match ty {
        Var(x) => { r.insert(x.clone()); }
        Arr(x, y) => { r.extend(freetyvarsty(&x)); r.extend(freetyvarsty(&y)); }
        Forall(x, y) => { r.extend(freetyvarsty(&y)); r.remove(x); }
    }
    r
}

fn freetyvars(term: &FTermChurch) -> HashSet<String> {
    use self::FTermChurch::*;
    let mut r = HashSet::new();
    match term {
        Var(_) => {},
        Lam(x, y, z) => { r.extend(freetyvarsty(&y));  },
        App(x, y) => { r.extend(freetyvars(&x)); r.extend(freetyvars(&y)); },
        TLam(x, y) => { r.extend(freetyvars(&y)); r.remove(x); },
        TApp(x, y) => { r.extend(freetyvars(&x)); r.extend(freetyvarsty(&y)); }
    }
    r
}

#[derive(Clone, Debug)]
enum FContextElem {
    HasType(String, FType),
    TyVar(String),
}

/*
fn alpha_eq_ty(x: FType, y: FType) -> bool {
    x == y // TODO: traverse into foralls
}

fn typecheck(ctx: &[FContextElem], term: FTermChurch, ty: FType) -> bool {
    use self::FTermChurch::*;
    match term {
        Var(x) => ctx.contains(FContextElem::HasType(x, ty)),
        Lam(x, y, z) => { 
            if let FType::Arr(a, b) = ty {
                let mut ctx = ctx.to_vec();
                ctx.push(FContextElem::HasType(x, a));
                alpha_eq_ty(a, y) && typecheck(&ctx, z, b)
            } else {
                false
            }
        },
        App(x, y) => {
            let (a, b) = if let Lam(_, a, _) = x { (*a, ty) } else { return false };
            typecheck(ctx, x, FType::Arr(a, b)) && typecheck(ctx, y, a)
        },
        TLam(x, y) => {
            if let FType::Var(a) = ty {
                let mut ctx = ctx.to_vec();
                ctx.push(FContextElem::TyVar(a));
                typecheck(&ctx, y, ty) && a == x // TODO: should we generalize and substitute here, to allow typechecking `(tlam a => _) : forall b, _` when ascriptions are added?
            } else {
                false
            }
        },
        TApp(x, y) => {
            false // TODO: capture avoiding substitution
        }
    }
}
*/

fn main() {
    let succ = FTermChurch::Var("succ".into());
    let nat = FType::Var("nat".into());
    let double = { let x = tvar("X"); tlam("X", lam("f", arr(x.clone(), x.clone()), lam("a", x.clone(), app(var("f"), app(var("f"), var("a")))))) };
    let example = { app(tapp(double.clone(), nat.clone()), lam("x", nat, app(succ.clone(), app(succ.clone(), var("x"))))) };
    println!("double = {}", double);
    println!("example = {}", example);
}
