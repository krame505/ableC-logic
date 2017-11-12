grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

synthesized attribute logicType::LogicType;
synthesized attribute logicTypes::[LogicType];

nonterminal LogicTypeExpr with pp, host<BaseTypeExpr>, logicType, errors, location;

abstract production boolLogicTypeExpr
top::LogicTypeExpr ::=
{
  top.pp = pp"bool";
  top.host = builtinTypeExpr(nilQualifier(), boolType());
  top.logicType = boolLogicType();
  top.errors := [];
}

abstract production signedLogicTypeExpr
top::LogicTypeExpr ::= width::Integer
{
  top.pp = pp"signed:${text(toString(width))}";
  top.host =
    if width <= 8
    then typedefTypeExpr(nilQualifier(), name("int8_t", location=builtin))
    else if width <= 16
    then typedefTypeExpr(nilQualifier(), name("int16_t", location=builtin))
    else if width <= 32
    then typedefTypeExpr(nilQualifier(), name("int32_t", location=builtin))
    else if width <= 64
    then typedefTypeExpr(nilQualifier(), name("int64_t", location=builtin))
    else errorTypeExpr([err(top.location, s"Integer width not yet implemented: ${toString(width)}")]);
  top.logicType = signedLogicType(width);
  top.errors := if width < 1 then [err(top.location, "Width must be >= 1")] else [];
}

abstract production unsignedLogicTypeExpr
top::LogicTypeExpr ::= width::Integer
{
  top.pp = pp"unsigned:${text(toString(width))}";
  top.host =
    if width <= 8
    then typedefTypeExpr(nilQualifier(), name("uint8_t", location=builtin))
    else if width <= 16
    then typedefTypeExpr(nilQualifier(), name("uint16_t", location=builtin))
    else if width <= 32
    then typedefTypeExpr(nilQualifier(), name("uint32_t", location=builtin))
    else if width <= 64
    then typedefTypeExpr(nilQualifier(), name("uint64_t", location=builtin))
    else errorTypeExpr([err(top.location, s"Integer width not yet implemented: ${toString(width)}")]);
  top.logicType = unsignedLogicType(width);
  top.errors := if width < 1 then [err(top.location, "Width must be >= 1")] else [];
}

abstract production errorLogicTypeExpr
top::LogicTypeExpr ::= msg::[Message]
{
  top.pp = pp"/*err*/";
  top.host = errorTypeExpr(msg);
  top.logicType = errorLogicType();
  top.errors := msg;
}

synthesized attribute logicTypeExpr::LogicTypeExpr;
synthesized attribute width::Integer;

synthesized attribute hostToUnsignedProd::(Expr ::= Expr Location);
synthesized attribute hostFromUnsignedProd::(Expr ::= Expr Location);
synthesized attribute bitPad::(Pair<[FlowDef] [FlowExpr]> ::= [FlowExpr]);

nonterminal LogicType with pp, logicTypeExpr, width, isIntegerType, hostToUnsignedProd, hostFromUnsignedProd, bitPad;

aspect default production
top::LogicType ::=
{
  top.isIntegerType = true;
  top.hostToUnsignedProd = \ e::Expr l::Location -> e;
  top.hostFromUnsignedProd = \ e::Expr l::Location -> e;
  top.bitPad =
    \ fes::[FlowExpr] -> pair([], repeat(constantFlowExpr(false), top.width - length(fes)) ++ fes);
}

abstract production boolLogicType
top::LogicType ::= 
{
  top.pp = pp"bool";
  top.logicTypeExpr = boolLogicTypeExpr(location=builtin);
  top.width = 1;
}

abstract production signedLogicType
top::LogicType ::= width::Integer
{
  top.pp = pp"signed:${text(toString(width))}";
  top.logicTypeExpr = signedLogicTypeExpr(width, location=builtin);
  top.width = width;
  top.bitPad =
    \ fes::[FlowExpr] ->
      let tmpFlowId::String = s"_signedBitPadTmp_${toString(genInt())}"
      in
        pair(
          [flowDef(tmpFlowId, head(fes))],
          repeat(nodeFlowExpr(tmpFlowId), top.width - length(fes) + 1) ++ tail(fes))
      end;  
}

abstract production unsignedLogicType
top::LogicType ::= width::Integer
{
  top.pp = pp"unsigned:${text(toString(width))}";
  top.logicTypeExpr = unsignedLogicTypeExpr(width, location=builtin);
  top.width = width;
}

abstract production errorLogicType
top::LogicType ::= 
{
  top.pp = pp"/*err*/";
  top.logicTypeExpr = errorLogicTypeExpr([], location=builtin); 
  top.width = 1;
}

-- Env is needed to compute types in order to look up defs from stdint.h
function logicTypeToHostType
Type ::= env::Decorated Env  logicType::LogicType
{
  local bty::BaseTypeExpr = logicType.logicTypeExpr.host;
  bty.env = env;
  bty.labelEnv = emptyScope();
  bty.givenRefId = nothing();
  bty.returnType = nothing();
  return bty.typerep;
}
