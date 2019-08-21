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
        b"forall" => true,
        _ => false,
    }
}

fn variable(input: &[u8]) -> IResult<&[u8], String> { map(verify(take_while1(|c| is_alphanumeric(c) || c == b'_'), |s| !reserved(s)), |s| String::from_utf8_lossy(s).into())(input) }

fn parse_tvar(input: &[u8]) -> IResult<&[u8], FType> { map(variable, tvar)(input) }
fn parse_arr(input: &[u8]) -> IResult<&[u8], FType> { map(separated_pair(parse_paren_type, tuple((multispace0, tag(b"->"), multispace0)), parse_paren_type), |(a, b)| arr(a, b))(input) }
fn parse_forall(input: &[u8]) -> IResult<&[u8], FType> { map(tuple((tag(b"forall"), multispace1, variable, tag(b","), multispace0, parse_type)), |(_, _, a, _, _, b)| forall(a, b))(input) }

fn parse_paren_type(input: &[u8]) -> IResult<&[u8], FType> { alt((parse_tvar, parse_forall, delimited(tag(b"("), parse_type, tag(b")"))))(input) }
fn parse_type(input: &[u8]) -> IResult<&[u8], FType> { alt((parse_arr, parse_paren_type))(input) }

fn parse_var(input: &[u8]) -> IResult<&[u8], FTermChurch> { map(variable, var)(input) }

#[test]
fn test_parse_types() {
    println!("{:?}", parse_type(b"nat"));
    println!("{:?}", parse_type(b"nat -> nat"));
    println!("{:?}", parse_type(b"(nat -> nat)"));
    println!("{:?}", parse_type(b"(nat -> nat) -> nat"));
    println!("{:?}", parse_type(b"nat -> (nat -> nat)"));
    println!("{:?}", parse_type(b"forall X, nat -> nat"));
    println!("{:?}", parse_type(b"forall X, (nat -> nat)"));
    println!("{:?}", parse_type(b"forall X, forall Y, Y -> X"));
    println!("{:?}", parse_type(b"X -> forall y, y"));
}
