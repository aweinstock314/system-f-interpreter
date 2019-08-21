use std::collections::HashSet;

pub mod abssyn;
use self::abssyn::*;

pub mod substitution;
use self::substitution::*;

#[derive(Clone, Debug, PartialEq, Eq)]
enum FContextElem {
    HasType(String, FType),
    TyVar(String),
}

fn typeinfer(ctx: &[FContextElem], term: FTermChurch) -> Option<FType> {
    use self::FTermChurch::*;
    match term {
        Var(x) => {
            ctx.iter().filter_map(|e| if let FContextElem::HasType(y, ty) = e { Some((y, ty)) } else { None }).find(|(y, _)| x == **y).map(|(_, ty)| ty.clone())
        },
        Lam(x, y, z) => {
            let mut ctx = ctx.to_vec();
            ctx.push(FContextElem::HasType(x, *y.clone()));
            typeinfer(&ctx, *z).map(|w| arr(*y, w))

        },
        App(x, y) => {
            typeinfer(ctx, *x).and_then(|t| typeinfer(ctx, *y).and_then(|b| {
                if let FType::Arr(_, b2) = &t { if b == **b2 { return Some(b); } }
                None
            }))
        },
        TLam(x, y) => {
            let mut ctx = ctx.to_vec();
            ctx.push(FContextElem::TyVar(x.clone()));
            typeinfer(&ctx, *y).map(|b| forall(x, b))
        },
        TApp(x, y) => {
            if let Some(FType::Forall(a, b)) = typeinfer(ctx, *x) {
                Some(substtyvar_ty(&a, *y, *b))
            } else {
                None
            }
        },
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
    let inferred = typeinfer(&[], double.clone());
    println!("typeinfer result for double: {:?}", inferred.clone().map(|x| format!("{}", x)));
    println!("expected type of double = {}, equivalent to inferred: {}", tdouble.clone(), inferred == Some(tdouble));
    println!("example = {}", example);
    let natctx = [FContextElem::TyVar("nat".into()), FContextElem::HasType("succ".into(), arr(tvar("nat"), tvar("nat")))];
    println!("natctx = {:?}", natctx);
    println!("typeinfer result for example: {:?}", typeinfer(&natctx, example.clone()).map(|x| format!("{}", x)));
    let idnat = lam("x", tvar("nat"), var("x"));
    let mut tmp = Some(app(idnat, app(example, var("0"))));
    while let Some(old) = tmp {
        let new = smallstep(old.clone());
        println!("{} --> {:?}", old, new.clone().map(|x| format!("{}", x)));
        tmp = new;
    }
}
