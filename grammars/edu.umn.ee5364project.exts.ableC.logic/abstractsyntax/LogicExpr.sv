grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

nonterminal LogicExpr with logicValueEnv, logicFunctionEnv, pp, host<Expr>, logicType, errors, logicFlowDefs, logicFlowResult, location;

-- Direct values
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
  top.logicFlowDefs = [];
  top.logicFlowResult = [constantLogicFlowExpr(value)];
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
  top.logicFlowDefs = [];
  top.logicFlowResult = map(constantLogicFlowExpr, bits);
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
  top.logicFlowDefs = [];
  top.logicFlowResult =
    map(\ i::Integer -> nodeLogicFlowExpr(id.name, i), range(0, top.logicType.width));
  
  top.errors <- id.logicValueLookupCheck;
}

abstract production callLogicExpr
top::LogicExpr ::= f::Name a::LogicExprs
{
  top.pp = parens( ppConcat([ f.pp, parens( ppImplode( cat( comma(), space() ), a.pps ))]) );
  top.host = directCallExpr(getLogicFunctionHostName(f), a.host, location=top.location);
  top.logicType = f.logicFunctionItem.returnLogicType;
  top.errors := a.errors;
  
  local callId::Integer = genInt();
  local renameFn::(String ::= String) = \ n::String -> s"_${f.name}_${n}_${toString(callId)}";
  top.logicFlowDefs =
    a.logicFlowDefs ++
    subParamsLogicFlowDefs(
      a.logicFlowResults,
      renameLogicFlowDefs(renameFn, f.logicFunctionItem.logicFlowGraph.logicFlowDefs));
  top.logicFlowResult =
    map(
      subParamsLogicFlowExpr(a.logicFlowResults, _),
      map(
        renameLogicFlowExpr(renameFn, _),
        f.logicFunctionItem.logicFlowGraph.logicFlowResult));
  
  top.errors <- f.logicFunctionLookupCheck;
  top.errors <- if null(f.logicFunctionLookupCheck) then a.argumentErrors else [];
  
  a.argumentPosition = 1;
  a.expectedLogicTypes = f.logicFunctionItem.parameterLogicTypes;
  a.callLocation = top.location;
}

-- Custom bit manipulation constructs
abstract production bitAppendLogicExpr
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
  top.logicFlowDefs = e1.logicFlowDefs ++ e2.logicFlowDefs;
  top.logicFlowResult = e1.logicFlowResult ++ e2.logicFlowResult;
}

abstract production bitSelectLogicExpr
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
  top.logicFlowDefs = e.logicFlowDefs;
  top.logicFlowResult = [head(drop(i, e.logicFlowResult))];
  
  top.errors <-
    if i < 0 || i >= e.logicType.width
    then [err(top.location, s"Out of bounds bit index ${toString(i)} for ${show(80, e.logicType.pp)}")]
    else [];
}

abstract production bitSelectRangeLogicExpr
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
  top.logicFlowDefs = e.logicFlowDefs;
  top.logicFlowResult = take(j - i + 1, drop(i, e.logicFlowResult));
  
  top.errors <-
    if i < 0 || i >= e.logicType.width
    then [err(top.location, s"Out of bounds lower bit index ${toString(i)} for ${show(80, e.logicType.pp)}")]
    else [];
  top.errors <-
    if j < 0 || j >= e.logicType.width
    then [err(top.location, s"Out of upper bit index ${toString(j)} for ${show(80, e.logicType.pp)}")]
    else [];
  top.errors <-
    if i > j
    then [err(top.location, s"Lower bit index ${toString(i)} must be less than upper bit index ${toString(j)}")]
    else [];
}

-- Built-in C operators
abstract production logicalNotLogicExpr
top::LogicExpr ::= e::LogicExpr
{
  top.pp = parens( cat( text("!"), e.pp ) );
  top.host = notExpr(e.host, location=top.location);
  top.logicType = boolLogicType();
  top.errors := e.errors;
  top.logicFlowDefs = e.logicFlowDefs;
  top.logicFlowResult = [notLogicFlowExpr(foldr1(orLogicFlowExpr, e.logicFlowResult))];
}

inherited attribute expectedParameterNames::[String];
inherited attribute expectedLogicTypes::[LogicType];
autocopy attribute callLocation::Location;

nonterminal LogicExprs with logicValueEnv, logicFunctionEnv, argumentPosition, expectedParameterNames, expectedLogicTypes, callLocation, pps, host<Exprs>, count, logicTypes, errors, argumentErrors, logicFlowDefs, logicFlowResults;

abstract production consLogicExpr
top::LogicExprs ::= h::LogicExpr t::LogicExprs
{
  top.pps = h.pp :: t.pps;
  top.host = consExpr(h.host, t.host); -- TODO: Cast h.host to h.logicType.host
  top.count = 1 + t.count;
  top.logicTypes = h.logicType :: t.logicTypes;
  top.errors := h.errors ++ t.errors;
  top.argumentErrors =
    case top.expectedLogicTypes of
      lt :: _ ->
        if h.logicType.width > lt.width
        then [err(h.location, s"Argument ${toString(top.argumentPosition)} type ${show(80, h.logicType.pp)} is wider than parameter type ${show(80, lt.pp)}")]
        else t.argumentErrors
    | [] -> [err(top.callLocation, s"Call expected ${toString(top.argumentPosition - 1)} arguments, got ${toString(top.argumentPosition + t.count)}")]
    end;
  top.logicFlowDefs = h.logicFlowDefs ++ t.logicFlowDefs;
  top.logicFlowResults = h.logicFlowResult :: t.logicFlowResults;
  
  t.argumentPosition = 1 + top.argumentPosition;
  t.expectedParameterNames = tail(top.expectedParameterNames);
  t.expectedLogicTypes = tail(top.expectedLogicTypes);
}

abstract production nilLogicExpr
top::LogicExprs ::= 
{
  top.pps = [];
  top.host = nilExpr();
  top.count = 0;
  top.logicTypes = [];
  top.errors := [];
  top.logicFlowDefs = [];
  top.logicFlowResults = [];
  
  top.argumentErrors =
    if !null(top.expectedLogicTypes)
    then [err(top.callLocation, s"Call expected ${toString(top.argumentPosition + length(top.expectedLogicTypes) - 1)} arguments, got only ${toString(top.argumentPosition - 1)}")]
    else []; 
}
