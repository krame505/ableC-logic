grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

type Bits = [Boolean];

function intToBits
Bits ::= signed::Boolean value::Integer
{
  local help::(Bits ::= Integer Bits) =
    \ i::Integer bs::Bits -> if i == 0 then bs else help(i / 2, (i % 2 != 0) :: bs);
  
  local posRes::Bits = help(value, []);
  local negRes::Bits = help(-value, []);
  
  return
    if signed
    then if value < 0
      then if head(negRes)
        then twosComplementBits(false :: negRes)
        else twosComplementBits(negRes)
      else if head(posRes)
        then false :: posRes
        else posRes
    else posRes;
}

-- TODO: This has issues with Integer overflow, since we don't have a better internal representation
function bitsToInt
Integer ::= signed::Boolean bs::Bits
{
  local help::(Integer ::= Integer Bits) =
    \ total::Integer bs::Bits ->
      case bs of
        false :: t -> help(total * 2, t)
      | true :: t -> help(total * 2 + 1, t)
      | [] -> total
      end;
  
  return
    if signed && head(bs)
    then -help(0, twosComplementBits(bs))
    else help(0, bs);
}

function padBits
Bits ::= width::Integer bs::Bits
{
  return repeat(false, width - length(bs)) ++ bs;
}

function notBits
Bits ::= bs::Bits
{
  return map(\ b::Boolean -> !b, bs);
}

function incBits
Bits ::= bs::Bits
{
  local help::(Pair<Bits Boolean> ::= Bits) =
    \ bs::Bits ->
      case bs of
        h :: t ->
          let res::Pair<Bits Boolean> = help(t)
          in pair(xor(h, res.snd) :: res.fst, h && res.snd)
          end
      | [] -> pair([], true)
      end;

  return help(bs).fst;
}

function twosComplementBits
Bits ::= bs::Bits
{
  return incBits(notBits(bs));
}

{-
function addBits
Bits ::= bs1::Bits bs2::Bits
{
  return rippleAdd(padBits(length(bs2), bs1), padBits(length(bs1), bs2)).fst;
}

function rippleAdd
Pair<Bits Boolean> ::= bs1::Bits bs2::Bits
{
  return
    case bs1, bs2 of
      h1 :: t1, h2 :: t2 ->
      let
        tRes::Pair<Bits Boolean> = rippleAdd(t1, t2)
      in let
        hRes::Pair<Boolean Boolean> = fullAdd(h1, h2, tRes.snd)
      in
        pair(hRes.fst :: tRes.fst, hRes.snd)
      end end
    | [], [] -> pair([], false)
    | _, _ -> error(s"rippleAdd bit length mismatch")
    end;
}

function halfAdd
Pair<Boolean Boolean> ::= a::Boolean b::Boolean
{
  return pair(xor(a, b), a && b);
}

function fullAdd
Pair<Boolean Boolean> ::= a::Boolean b::Boolean c::Boolean
{
  local upperRes::Pair<Boolean Boolean> = halfAdd(a, b);
  local lowerRes::Pair<Boolean Boolean> = halfAdd(upperRes.snd, c);
  return pair(upperRes.fst, lowerRes.fst);
}

-}

function xor
Boolean ::= a::Boolean b::Boolean
{
  return (a && !b) || (b && !a);
}

function range
[Integer] ::= min::Integer max::Integer
{
  return if min < max then min :: range(min + 1, max) else [];
}
