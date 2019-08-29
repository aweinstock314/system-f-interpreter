/// Abstract Syntax for F-terms and F-types
use std::fmt;

// The trees themselves
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FType {
    Var(String),
    Arr(Box<FType>, Box<FType>),
    Forall(String, Box<FType>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FTermChurch {
    Var(String),
    Lam(String, Box<FType>, Box<FTermChurch>),
    App(Box<FTermChurch>, Box<FTermChurch>),
    TLam(String, Box<FTermChurch>),
    TApp(Box<FTermChurch>, Box<FType>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FOmegaKind {
    Star,
    Arr(Box<FOmegaKind>, Box<FOmegaKind>),
}


// smart constructors that handle boxing/string allocation
pub fn tvar<S: Into<String>>(x: S) -> FType { FType::Var(x.into()) }
pub fn arr(x: FType, y: FType) -> FType { FType::Arr(Box::new(x), Box::new(y)) }
pub fn forall<S: Into<String>>(x: S, y: FType) -> FType { FType::Forall(x.into(), Box::new(y)) }

pub fn var<S: Into<String>>(x: S) -> FTermChurch { FTermChurch::Var(x.into()) }
pub fn lam<S: Into<String>>(x: S, y: FType, z: FTermChurch) -> FTermChurch { FTermChurch::Lam(x.into(), Box::new(y), Box::new(z)) }
pub fn app(x: FTermChurch, y: FTermChurch) -> FTermChurch { FTermChurch::App(Box::new(x), Box::new(y)) }
pub fn tlam<S: Into<String>>(x: S, y: FTermChurch) -> FTermChurch { FTermChurch::TLam(x.into(), Box::new(y)) }
pub fn tapp(x: FTermChurch, y: FType) -> FTermChurch { FTermChurch::TApp(Box::new(x), Box::new(y)) }


// shorthand for inspecting the tags of the trees
impl FType {
    pub fn is_var(&self) -> bool { if let FType::Var(_) = self { true } else { false } }
    pub fn is_forall(&self) -> bool { if let FType::Forall(_, _) = self { true } else { false } }
}

impl FTermChurch {
    pub fn is_var(&self) -> bool { if let FTermChurch::Var(_) = self { true } else { false } }
    pub fn is_lam(&self) -> bool {
        match self {
            FTermChurch::Lam(_, _, _) | FTermChurch::TLam(_, _) => true,
            _ => false,
        }
    }
    pub fn is_app(&self) -> bool { if let FTermChurch::App(_, _) = self { true } else { false } }
    pub fn is_tapp(&self) -> bool { if let FTermChurch::TApp(_, _) = self { true } else { false } }
    pub fn is_value(&self) -> bool { self.is_lam() }
}

impl FOmegaKind {
    pub fn is_star(&self) -> bool { if let FOmegaKind::Star = self { true } else { false } }
}

// pretty printing and printing machinery
pub fn parens_if<X: fmt::Display>(x: X, use_parens: bool) -> String {
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

impl fmt::Display for FOmegaKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::FOmegaKind::*;
        match self {
            Star => write!(f, "*"),
            Arr(x, y) => write!(f, "{} -> {}", parens_if(x, !x.is_star()), y),
        }
    }
}
