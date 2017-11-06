grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

nonterminal LogicExpr with logicValueEnv, logicFunctionEnv, pp, host<Expr>, logicType, errors, flowDefs, flowExprs, location;

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
  top.flowDefs = [];
  top.flowExprs = [constantFlowExpr(value)];
}

abstract production intConstantLogicExpr
top::LogicExpr ::= signed::Boolean bits::Bits
{
  top.pp = pp"0b${ppConcat(map(\bit::Boolean -> if bit then pp"1" else pp"0", bits))}"; -- TODO: Show hex if width is multiple of 4
  top.host =
    realConstant(
      integerConstant(
        toString(bitsToInt(signed, bits)),
        !signed,
        noIntSuffix(), -- TODO: Does this need a suffix?
        location=builtin),
      location=top.location);
  top.logicType = if signed then signedLogicType(length(bits)) else signedLogicType(length(bits));
  top.errors := [];
  top.flowDefs = [];
  top.flowExprs = map(constantFlowExpr, bits);
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
  top.flowDefs = [];
  top.flowExprs =
    map(\ id::String -> nodeFlowExpr(id), id.logicValueItem.flowIds);
  
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
  local renameFn::(String ::= String) = \ n::String -> s"${f.name}_${n}_${toString(callId)}";
  local transformedFlowGraph::FlowGraph =
    subParamsFlowGraph(
      a.argumentFlowExprs,
      renameFlowGraph(renameFn, f.logicFunctionItem.flowGraph));
  top.flowDefs = a.flowDefs ++ transformedFlowGraph.flowDefs;
  top.flowExprs = transformedFlowGraph.flowExprs;
  
  a.argumentPosition = 1;
  a.expectedLogicTypes = f.logicFunctionItem.parameterLogicTypes;
  a.callLocation = top.location;
  
  top.errors <- f.logicFunctionLookupCheck;
  top.errors <- if null(f.logicFunctionLookupCheck) then a.argumentErrors else [];
}

-- Custom bit manipulation constructs
abstract production bitAppendLogicExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = ppConcat([e1.pp, comma(), space(), e2.pp]);
  top.host =
    orBitExpr(
      lshExpr(
        -- Convert to unsigned, then cast to correct width before shifting
        explicitCastExpr(
          typeName(top.logicType.logicTypeExpr.host, baseTypeExpr()),
          e1.logicType.hostToUnsignedProd(e1.host, builtin),
          location=builtin),
        mkIntConst(e2.logicType.width, builtin),
        location=top.location),
      e2.logicType.hostToUnsignedProd(e2.host, builtin),
      location=top.location);
  top.logicType = unsignedLogicType(e1.logicType.width + e2.logicType.width);
  top.errors := e1.errors ++ e2.errors;
  top.flowDefs = e1.flowDefs ++ e2.flowDefs;
  top.flowExprs = e1.flowExprs ++ e2.flowExprs;
}

abstract production bitSelectLogicExpr
top::LogicExpr ::= e::LogicExpr i::Integer
{
  top.pp = pp"${e.pp}[${text(toString(i))})}]";
  top.host =
    andBitExpr(
      mkIntConst(1, builtin),
      rshExpr(
        e.logicType.hostToUnsignedProd(e.host, builtin),
        mkIntConst(e.logicType.width - (i + 1), builtin), location=builtin),
      location=builtin);
  top.logicType = boolLogicType();
  top.errors := e.errors;
  top.flowDefs = e.flowDefs;
  top.flowExprs = [head(drop(i, e.flowExprs))];
  
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
    andBitExpr(
      mkIntConst(bitsToInt(false, repeat(true, j - i + 1)), builtin),
      rshExpr(
        e.logicType.hostToUnsignedProd(e.host, builtin),
        mkIntConst(e.logicType.width - (j + 1), builtin), location=builtin),
      location=builtin);
  top.logicType = unsignedLogicType(j - i + 1);
  top.errors := e.errors;
  top.flowDefs = e.flowDefs;
  top.flowExprs = take(j - i + 1, drop(i, e.flowExprs));
  
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

-- Conversions
{-abstract production boolToUnsigned
top::LogicExpr ::= e::LogicExpr
{
  top.pp = pp"boolToUnsigned(${e.pp})";
  top.
}-}

-- Built-in C operators
-- TODO: Binary flat-fold flow translation for logic ops
abstract production bitNotLogicExpr
top::LogicExpr ::= e::LogicExpr
{
  top.pp = parens( cat( text("~"), e.pp ) );
  top.host = bitNegateExpr(e.host, location=top.location);
  top.logicType = e.logicType;
  top.errors := e.errors;
  top.flowDefs = e.flowDefs;
  top.flowExprs = map(notFlowExpr, e.flowExprs);
  
  top.errors <-
    if !e.logicType.isIntegerType
    then [err(top.location, s"Operands to ~ must have an integer type, but got ${show(80, e.logicType.pp)}")]
    else [];
}

abstract production logicalNotLogicExpr
top::LogicExpr ::= e::LogicExpr
{
  top.pp = parens( cat( text("!"), e.pp ) );
  top.host = notExpr(e.host, location=top.location);
  top.logicType = boolLogicType();
  top.errors := e.errors;
  top.flowDefs = e.flowDefs;
  top.flowExprs = [notFlowExpr(foldr1(orFlowExpr, e.flowExprs))];
}

abstract production bitAndLogicExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = pp"(${e1.pp} & ${e2.pp})";
  top.host = andBitExpr(e1.host, e2.host, location=top.location);
  top.logicType = if e1.logicType.width >= e2.logicType.width then e1.logicType else e2.logicType;
  top.errors := e1.errors ++ e2.errors;
  top.flowDefs = e1.flowDefs ++ e2.flowDefs;
  top.flowExprs =
    zipWith(andFlowExpr, top.logicType.bitPad(e1.flowExprs), top.logicType.bitPad(e2.flowExprs));
  
  top.errors <-
    if !e1.logicType.isIntegerType
    then [err(top.location, s"Operands to & must have an integer type, but got ${show(80, e1.logicType.pp)}")]
    else [];
  top.errors <-
    if !e2.logicType.isIntegerType
    then [err(top.location, s"Operands to & must have an integer type, but got ${show(80, e2.logicType.pp)}")]
    else [];
}

abstract production bitXorLogicExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = pp"(${e1.pp} ^ ${e2.pp})";
  top.host = xorExpr(e1.host, e2.host, location=top.location);
  top.logicType = if e1.logicType.width >= e2.logicType.width then e1.logicType else e2.logicType;
  top.errors := e1.errors ++ e2.errors;
  
  local xorId::Integer = genInt();
  local lhsTmpNames::[String] =
    map(
      \ i::Integer -> s"_bitXorLhsTmp${toString(i)}_${toString(xorId)}",
      range(0, top.logicType.width));
  local rhsTmpNames::[String] =
    map(
      \ i::Integer -> s"_bitXorRhsTmp${toString(i)}_${toString(xorId)}",
      range(0, top.logicType.width));
  top.flowDefs =
    e1.flowDefs ++ e2.flowDefs ++
    zipWith(flowDef, lhsTmpNames, top.logicType.bitPad(e1.flowExprs)) ++
    zipWith(flowDef, rhsTmpNames, top.logicType.bitPad(e2.flowExprs));
  local lhsFlowExprs::[FlowExpr] = map(nodeFlowExpr, lhsTmpNames);
  local rhsFlowExprs::[FlowExpr] = map(nodeFlowExpr, rhsTmpNames);
  top.flowExprs =
    zipWith(
      orFlowExpr,
      zipWith(andFlowExpr, lhsFlowExprs, map(notFlowExpr, rhsFlowExprs)),
      zipWith(andFlowExpr, map(notFlowExpr, lhsFlowExprs), rhsFlowExprs));
  
  top.errors <-
    if !e1.logicType.isIntegerType
    then [err(top.location, s"Operands to ^ must have an integer type, but got ${show(80, e1.logicType.pp)}")]
    else [];
  top.errors <-
    if !e2.logicType.isIntegerType
    then [err(top.location, s"Operands to ^ must have an integer type, but got ${show(80, e2.logicType.pp)}")]
    else [];
}

abstract production bitOrLogicExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = pp"(${e1.pp} | ${e2.pp})";
  top.host = orBitExpr(e1.host, e2.host, location=top.location);
  top.logicType = if e1.logicType.width >= e2.logicType.width then e1.logicType else e2.logicType;
  top.errors := e1.errors ++ e2.errors;
  top.flowDefs = e1.flowDefs ++ e2.flowDefs;
  top.flowExprs =
    zipWith(orFlowExpr, top.logicType.bitPad(e1.flowExprs), top.logicType.bitPad(e2.flowExprs));
  
  top.errors <-
    if !e1.logicType.isIntegerType
    then [err(top.location, s"Operands to | must have an integer type, but got ${show(80, e1.logicType.pp)}")]
    else [];
  top.errors <-
    if !e2.logicType.isIntegerType
    then [err(top.location, s"Operands to | must have an integer type, but got ${show(80, e2.logicType.pp)}")]
    else [];
}

abstract production logicalAndLogicExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = pp"(${e1.pp} && ${e2.pp})";
  top.host = andExpr(e1.host, e2.host, location=top.location);
  top.logicType = boolLogicType();
  top.errors := e1.errors ++ e2.errors;
  top.flowDefs = e1.flowDefs ++ e2.flowDefs;
  top.flowExprs =
    [andFlowExpr(foldr1(orFlowExpr, e1.flowExprs), foldr1(orFlowExpr, e2.flowExprs))];
}

abstract production logicalOrLogicExpr
top::LogicExpr ::= e1::LogicExpr e2::LogicExpr
{
  top.pp = pp"(${e1.pp} || ${e2.pp})";
  top.host = orExpr(e1.host, e2.host, location=top.location);
  top.logicType = boolLogicType();
  top.errors := e1.errors ++ e2.errors;
  top.flowDefs = e1.flowDefs ++ e2.flowDefs;
  top.flowExprs =
    [orFlowExpr(foldr1(orFlowExpr, e1.flowExprs), foldr1(orFlowExpr, e2.flowExprs))];
}

inherited attribute expectedParameterNames::[String];
inherited attribute expectedLogicTypes::[LogicType];
autocopy attribute callLocation::Location;

synthesized attribute argumentFlowExprs::[FlowExpr];

nonterminal LogicExprs with logicValueEnv, logicFunctionEnv, argumentPosition, expectedParameterNames, expectedLogicTypes, callLocation, pps, host<Exprs>, count, logicTypes, errors, argumentErrors, flowDefs, flowExprs, argumentFlowExprs;

abstract production consLogicExpr
top::LogicExprs ::= h::LogicExpr t::LogicExprs
{
  top.pps = h.pp :: t.pps;
  top.host =
    consExpr(
      -- TODO: 2 conversions might be inefficient if the types are the same?
      head(top.expectedLogicTypes).hostFromUnsignedProd(
        h.logicType.hostToUnsignedProd(h.host, builtin),
        builtin),
      t.host);
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
  top.flowDefs = h.flowDefs ++ t.flowDefs;
  top.flowExprs = h.flowExprs ++ t.flowExprs;
  -- Pad the argument bits to be the full width of what is expected
  top.argumentFlowExprs = head(top.expectedLogicTypes).bitPad(h.flowExprs) ++ t.argumentFlowExprs;
  
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
  top.argumentErrors =
    if !null(top.expectedLogicTypes)
    then [err(top.callLocation, s"Call expected ${toString(top.argumentPosition + length(top.expectedLogicTypes) - 1)} arguments, got only ${toString(top.argumentPosition - 1)}")]
    else []; 
  top.flowDefs = [];
  top.flowExprs = [];
  top.argumentFlowExprs = [];
}
