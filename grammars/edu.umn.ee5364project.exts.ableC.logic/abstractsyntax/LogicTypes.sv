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

inherited attribute otherType::LogicType;

synthesized attribute bitPad::(Pair<[FlowDef] [FlowExpr]> ::= [FlowExpr]);

synthesized attribute hostToUnsignedProd::(Expr ::= Expr Location);
synthesized attribute hostCastProd::(Expr ::= Expr Location);

nonterminal LogicType with otherType, pp, logicTypeExpr, width, isIntegerType, bitPad, hostToUnsignedProd, hostCastProd;

aspect default production
top::LogicType ::=
{
  top.isIntegerType = true;
  top.bitPad =
    \ fes::[FlowExpr] -> pair([], repeat(constantFlowExpr(false), top.width - length(fes)) ++ fes);
  top.hostToUnsignedProd = \ e::Expr l::Location -> e;
  top.hostCastProd = top.hostToUnsignedProd;
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
  top.hostToUnsignedProd =
    explicitCastExpr(
      typeName(unsignedLogicTypeExpr(width, location=builtin).host, baseTypeExpr()),
      _, location=_);
  top.hostCastProd =
    case top.otherType of
      signedLogicType(width2) -> \ e::Expr l::Location -> e
    | _ ->
      if isHostWidth(width)
      then
        \ e::Expr l::Location ->
          explicitCastExpr(
            typeName(
              signedLogicTypeExpr(top.otherType.width, location=builtin).host,
              baseTypeExpr()),
            top.otherType.hostToUnsignedProd(e, l),
            location=l)
      else
        \ e::Expr l::Location ->
          explicitCastExpr(
            typeName(
              signedLogicTypeExpr(top.otherType.width, location=builtin).host,
              baseTypeExpr()),
            -- Convert to unsigned and sign-extend
            let
              mask::Expr =
                mkIntConst(bitsToInt(false, true :: repeat(false, top.otherType.width - 1)), l)
            in
              subExpr(
                xorExpr(top.otherType.hostToUnsignedProd(e, l), mask, location=l),
                mask,
                location=l)
            end,
            location=l)
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

function getHostCastProd
(Expr ::= Expr Location) ::= fromType::LogicType toType::LogicType
{
  toType.otherType = fromType;
  return toType.hostCastProd;
}

function isHostWidth
Boolean ::= width::Integer
{
  return width == 8 || width == 16 || width == 32 || width == 64;
}
