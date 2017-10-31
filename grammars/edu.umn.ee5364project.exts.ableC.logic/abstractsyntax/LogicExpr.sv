grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

nonterminal LogicExpr with logicValueEnv, logicFunctionEnv, pp, host<Expr>, logicType, errors, location;

abstract production constantLogicExpr
top::LogicExpr ::= signed::Boolean bits::Bits
{
  top.pp = pp"0b${ppConcat(map(\bit::Boolean -> if bit then pp"1" else pp"0", bits))}"; -- TODO: Hex if width is multiple of 4
  top.host =
    realConstant(
      integerConstant(
        toString(bitsToInt(signed, bits)),
        !signed,
        noIntSuffix(), -- TODO: Does this need a suffix?
        location=builtin),
      location=top.location);
  top.logicType = integerLogicType(signed, length(bits));
  top.errors := [];
}

abstract production intLiteralLogicExpr
top::LogicExpr ::= signed::Boolean value::Integer
{
  top.pp = cat(text(toString(value)), if signed then notext() else text("u"));
  forwards to constantLogicExpr(signed, intToBits(value), location=top.location);
}

abstract production varLogicExpr
top::LogicExpr ::= id::Name
{
  top.pp = id.pp;
  top.host = declRefExpr(id, location=top.location);
  top.logicType = id.logicValueItem.logicType;
  top.errors := [];
  
  top.errors <- id.logicValueLookupCheck;
}