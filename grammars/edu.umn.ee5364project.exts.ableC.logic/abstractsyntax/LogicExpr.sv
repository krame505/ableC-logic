grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

nonterminal LogicExpr with logicValueEnv, logicFunctionEnv, pp, host<Expr>, logicType, errors, location;

abstract production boolConstantLogicExpr
top::LogicExpr ::= value::Boolean
{
  top.pp = if value then pp"true" else pp"false";
  top.host =
    realConstant(
      integerConstant(
        toString(if value then "1" else "0"),
        true,
        noIntSuffix(),
        location=builtin),
      location=top.location);
  top.logicType = boolLogicType();
  top.errors := [];
}

abstract production intConstantLogicExpr
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
  top.logicType = intLogicType(signed, length(bits));
  top.errors := [];
}

abstract production intLiteralLogicExpr
top::LogicExpr ::= signed::Boolean value::Integer
{
  top.pp = cat(text(toString(value)), if signed then notext() else text("u"));
  forwards to intConstantLogicExpr(signed, intToBits(signed, value), location=top.location);
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

abstract production bitAppendExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = ppConcat([e1.pp, comma(), space(), e2.pp]);
  top.host =
    orBitExpr(
      lshExpr(
        explicitCastExpr(
          typeName(top.logicType.logicTypeExpr.host, baseTypeExpr()),
          e1.host,
          location=builtin),
        mkIntConst(e2.logicType.width, builtin),
        location=top.location),
      explicitCastExpr(
        typeName(top.logicType.logicTypeExpr.host, baseTypeExpr()),
        e2.host,
        location=builtin),
      location=top.location);
  top.logicType = intLogicType(false, e1.logicType.width + e2.logicType.width);
  top.errors := e1.errors ++ e2.errors;
}

abstract production bitSelectExpr
top::LogicExpr ::= e::LogicExpr i::Integer
{
  top.pp = pp"${e.pp}[${text(toString(i))})}]";
  top.host =
    explicitCastExpr(
      typeName(top.logicType.logicTypeExpr.host, baseTypeExpr()),
      andBitExpr(
        mkIntConst(1, builtin),
        rshExpr(e.host, mkIntConst(e.logicType.width - (i + 1), builtin), location=builtin),
        location=builtin),
      location=builtin);
  top.logicType = boolLogicType();
  top.errors := e.errors;
}

abstract production bitSelectRangeExpr
top::LogicExpr ::= e::LogicExpr i::Integer j::Integer
{
  top.pp = pp"${e.pp}[${text(toString(i))}..${text(toString(j))}]";
  top.host =
    explicitCastExpr(
      typeName(top.logicType.logicTypeExpr.host, baseTypeExpr()),
      andBitExpr(
        mkIntConst(bitsToInt(false, repeat(true, j - i + 1)), builtin),
        rshExpr(e.host, mkIntConst(e.logicType.width - (j + 1), builtin), location=builtin),
        location=builtin),
      location=builtin);
  top.logicType = intLogicType(false, j - i + 1);
  top.errors := e.errors;
}
