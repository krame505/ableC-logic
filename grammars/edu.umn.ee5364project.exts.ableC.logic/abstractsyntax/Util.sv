grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

type Bits = [Boolean];

function intToBits
Bits ::= signed::Boolean value::Integer
{
  local help::(Bits ::= Integer Bits) =
    \ i::Integer bs::Bits -> if i == 0 then bs else help(i / 2, (i % 2 != 0) :: bs);
  
  return 
    -- 0 technically has width 0, but we enforce that the width must always be >= 1
    if signed
    then if value >= 0
      then false :: help(value, [])
      else true :: twosComplementBits(help(-value, []))
    else if value == 0
    then [false]
    else help(value, []);
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

function xor
Boolean ::= a::Boolean b::Boolean
{
  return (a && !b) || (b && !a);
}

function foldBinary1
a ::= f::(a ::= a a) l::[a]
{
  return case l of
    [] -> error("Expected at least one element")
  | [h] -> h
  | _ ->
    let n::Integer = length(l) / 2
    in f(foldBinary1(f, take(n, l)), foldBinary1(f, drop(n, l)))
    end
  end;
}

function range
[Integer] ::= min::Integer max::Integer
{
  return if min < max then min :: range(min + 1, max) else [];
}

function infiniteRange
[Integer] ::= min::Integer
{
  return min :: infiniteRange(min + 1);
}

global naturalNumbers::[Integer] = infiniteRange(0);

-- TODO: Move to core?
function compareInteger
Integer ::= l::Integer  r::Integer
{
  return if l <= r then if l == r then 0 else -1 else 1;
}
