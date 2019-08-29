use super::*;
use nom::{IResult};
use nom::branch::{alt};
use nom::bytes::complete::{take_while1, tag};
use nom::character::{is_alphanumeric, complete::{multispace0, multispace1}};
use nom::sequence::{delimited, separated_pair, tuple};
use nom::combinator::{map, verify};

fn parenthesized<X, F: Fn(&[u8]) -> IResult<&[u8], X>>(f: F, input: &[u8]) -> IResult<&[u8], X> { delimited(tag(b"("), f, tag(b")"))(input) }
fn end_in_null<X, F: Fn(&[u8]) -> IResult<&[u8], X>>(f: F, input: &[u8]) -> IResult<&[u8], X> { map(tuple((f, tag(b"\0"))), |x| x.0)(input) }

fn reserved(input: &[u8]) -> bool {
    match input {
        b"forall" | b"lam" | b"tlam" => true,
        _ => false,
    }
}

fn variable(input: &[u8]) -> IResult<&[u8], String> { map(verify(take_while1(|c| is_alphanumeric(c) || c == b'_'), |s| !reserved(s)), |s| String::from_utf8_lossy(s).into())(input) }

fn parse_tvar(input: &[u8]) -> IResult<&[u8], FType> { map(variable, tvar)(input) }
fn parse_arr(input: &[u8]) -> IResult<&[u8], FType> { map(separated_pair(parse_paren_type, tuple((multispace0, tag(b"->"), multispace0)), parse_paren_type), |(a, b)| arr(a, b))(input) }
fn parse_forall(input: &[u8]) -> IResult<&[u8], FType> { map(tuple((tag(b"forall"), multispace1, variable, tag(b","), multispace0, parse_type)), |(_, _, a, _, _, b)| forall(a, b))(input) }

fn parse_paren_type(input: &[u8]) -> IResult<&[u8], FType> { alt((parse_tvar, parse_forall, delimited(tag(b"("), parse_type, tag(b")"))))(input) }
pub fn parse_type(input: &[u8]) -> IResult<&[u8], FType> { alt((parse_arr, parse_paren_type))(input) }

fn parse_var(input: &[u8]) -> IResult<&[u8], FTermChurch> { map(variable, var)(input) }
fn parse_lam(input: &[u8]) -> IResult<&[u8], FTermChurch> {
    map(tuple((tag(b"lam"), multispace1, variable, multispace1, tag(":"), multispace1, parse_type, multispace1, tag("=>"), multispace1, parse_term)),
    |(_, _, x, _, _, _, y, _, _, _, z)| lam(x, y, z))(input)
}
fn parse_tlam(input: &[u8]) -> IResult<&[u8], FTermChurch> {
    map(tuple((tag(b"tlam"), multispace1, variable, multispace1, tag("=>"), multispace1, parse_term)),
    |(_, _, x, _, _, _, y)| tlam(x, y))(input)
}

fn parse_app(input: &[u8]) -> IResult<&[u8], FTermChurch> { map(separated_pair(parse_paren_term, multispace1, parse_paren_term), |(a, b)| app(a, b))(input) }
fn parse_tapp(input: &[u8]) -> IResult<&[u8], FTermChurch> { map(separated_pair(parse_paren_term, multispace1, delimited(tuple((tag(b"["), multispace0)), parse_paren_type, tuple((multispace0, tag(b"]"))))), |(a, b)| tapp(a, b))(input)  }
fn parse_paren_term(input: &[u8]) -> IResult<&[u8], FTermChurch> { alt((parse_var, parse_lam, parse_tlam, delimited(tag(b"("), parse_term, tag(b")"))))(input) }
pub fn parse_term(input: &[u8]) -> IResult<&[u8], FTermChurch> { alt((parse_app, parse_tapp, parse_paren_term))(input) }

#[test]
fn test_parse_types() {
    let f = |s: &[u8], y: FType| {
        let res = parse_type(s);
        println!("{:?} parses as {:?}", String::from_utf8_lossy(s), res);
        let (rem, x) = res.unwrap();
        assert_eq!(rem, &[]);
        assert_eq!(x, y);
    };
    f(b"nat", tvar("nat"));
    f(b"nat -> nat", arr(tvar("nat"), tvar("nat")));
    f(b"(nat -> nat)", arr(tvar("nat"), tvar("nat")));
    f(b"(nat -> nat) -> nat", arr(arr(tvar("nat"), tvar("nat")), tvar("nat")));
    f(b"nat -> (nat -> nat)", arr(tvar("nat"), arr(tvar("nat"), tvar("nat"))));
    f(b"forall X, nat -> nat", forall("X", arr(tvar("nat"), tvar("nat"))));
    f(b"forall X, (nat -> nat)", forall("X", arr(tvar("nat"), tvar("nat"))));
    f(b"forall X, forall Y, Y -> X", forall("X", forall("Y", arr(tvar("Y"), tvar("X")))));
    f(b"X -> forall y, y", arr(tvar("X"), forall("y", tvar("y"))));
}


#[test]
fn test_parse_terms() {
    let f = |s: &[u8], y: FTermChurch| {
        let res = parse_term(s);
        println!("{:?} parses as {:?}", String::from_utf8_lossy(s), res);
        let (rem, x) = res.unwrap();
        assert_eq!(rem, &[]);
        assert_eq!(x, y);
    };
    f(b"lam x : nat => x", lam("x", tvar("nat"), var("x")));
    let nan = arr(tvar("nat"), tvar("nat"));
    f(b"lam x : nat -> nat => x", lam("x", nan.clone(), var("x")));
    f(b"lam x : forall x, x => x [x]", lam("x", forall("x", tvar("x")), tapp(var("x"), tvar("x"))));
    println!("{:?}", parse_term(b"(lam x : nat => x) ((((tlam X => lam f : X -> X => lam a : X => f (f a)) [nat]) (lam x : nat => succ (succ x))) 0)"));
    f(b"lam 5 : nat => lam f : nat -> nat => (f f) 5", lam("5", tvar("nat"), lam("f", nan.clone(), app(app(var("f"), var("f")), var("5"))))); // should work without parens...
    f(b"lam 5 : nat => lam f : nat -> nat => f (f 5)", lam("5", tvar("nat"), lam("f", nan.clone(), app(var("f"), app(var("f"), var("5"))))));
    println!("{:?}", parse_term(b"(tlam A => lam x : A => x) [nat] 0"));
    f(b"((tlam A => lam x : A => x) [nat]) 0", app(tapp(tlam("A", lam("x", tvar("A"), var("x"))), tvar("nat")), var("0")));
}
