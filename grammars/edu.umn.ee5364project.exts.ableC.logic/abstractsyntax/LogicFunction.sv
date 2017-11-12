grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;

abstract production logicFunctionDeclaration
top::Decl ::= f::LogicFunctionDecl
{
  top.pp = f.pp;
  
  f.logicFunctionEnv = top.env.logicFunctions;
  
  local hostTrans::Decl = functionDeclaration(f.host);
  local hostErrorTrans::Decl =
    defsDecl([valueDef("_logic_function_" ++ f.name, errorValueItem())]);
  
  -- TODO: Check for include of logic.xh
  local localErrors::[Message] = f.errors;
  local fwrd::Decl = hostTrans;
  local errorFwrd::Decl = hostErrorTrans;
  
  forwards to
    decls(
      foldDecl([
        txtDecl(s"/*\n${show(80, f.flowGraph.pp)}\n*/"),
        if !null(localErrors) then decls(foldDecl([warnDecl(localErrors), errorFwrd])) else fwrd,
        defsDecl(
          valueDef(f.name, logicFunctionValueItem(top.env, f)) ::
          map(
            \ item::Pair<String LogicFunctionItem> -> logicFunctionDef(item.fst, item.snd),
            f.logicFunctionDefs))]));
}

abstract production logicFunctionDirectCallExpr
top::Expr ::= id::Name args::Exprs
{
  top.pp = parens( ppConcat([ id.pp, parens( ppImplode( cat( comma(), space() ), args.pps ))]) );
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  args.expectedTypes = map(logicTypeToHostType(top.env, _), id.logicFunctionItem.parameterLogicTypes);
  args.argumentPosition = 1;
  args.callExpr = top;
  args.callVariadic = false;
  
  -- TODO: Replace MSBs with padding bits to the correct width
  local hostTrans::Expr = directCallExpr(getLogicFunctionHostName(id), args, location=top.location);
  
  local localErrors::[Message] = id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local fwrd::Expr = hostTrans;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

synthesized attribute flowGraph::FlowGraph;
synthesized attribute parameterLogicTypes::[LogicType];
synthesized attribute returnLogicType::LogicType;

nonterminal LogicFunctionDecl with logicFunctionEnv, isTopLevel, pp, host<FunctionDecl>, logicFunctionDefs, errors, flowGraph, name, parameterLogicTypes, returnLogicType, sourceLocation;

abstract production logicFunctionDecl
top::LogicFunctionDecl ::= id::Name ret::LogicTypeExpr params::LogicParameters body::LogicStmts
{
  top.pp =
    ppConcat([
      text("logic"), space(), ret.pp, space(), parens(ppImplode(text(", "), params.pps)),
      braces(cat(line(), nestlines(2, terminate(line(), body.pps))))]);
  top.host =
    functionDecl(
      if top.isTopLevel then [staticStorageClass()] else [],
      consSpecialSpecifier(inlineQualifier(), nilSpecialSpecifier()),
      ret.host,
      functionTypeExprWithArgs(baseTypeExpr(), params.host, false, nilQualifier()),
      getLogicFunctionHostName(id),
      nilAttribute(), nilDecl(),
      body.host);
  top.logicFunctionDefs = [pair(id.name, logicFunctionItem(top))];
  top.errors := ret.errors ++ params.errors ++ body.errors;
  local bitPad::Pair<[FlowDef] [FlowExpr]> = ret.logicType.bitPad(body.flowExprs);
  top.flowGraph =
    buildFlowGraph(id.name, params.flowDefs ++ body.flowDefs ++ bitPad.fst, bitPad.snd).simplified;
  
  top.name = id.name;
  top.parameterLogicTypes = params.logicTypes;
  top.returnLogicType = ret.logicType;
  top.sourceLocation = id.location;
  
  params.logicValueEnv = emptyScope();
  params.bitIndex = 0;
  body.logicValueEnv = addScope(params.logicValueDefs, params.logicValueEnv);
  body.logicFunctionEnv = openScope(top.logicFunctionEnv); -- In case we ever add nested logic functions I guess?
  body.givenReturnLogicType = ret.logicType;
  
  top.errors <- id.logicFunctionRedeclarationCheck;
}

inherited attribute bitIndex::Integer; -- Initially 0

nonterminal LogicParameters with logicValueEnv, bitIndex, pps, host<Parameters>, logicTypes, logicValueDefs, errors, flowDefs;

abstract production consLogicParameter
top::LogicParameters ::= h::LogicParameter  t::LogicParameters
{
  top.pps = h.pp :: t.pps;
  top.host = consParameters(h.host, t.host);
  top.logicTypes = h.logicType :: t.logicTypes;
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  top.flowDefs = h.flowDefs ++ t.flowDefs;
  
  t.logicValueEnv = addScope(h.logicValueDefs, h.logicValueEnv);
  h.bitIndex = top.bitIndex;
  t.bitIndex = top.bitIndex + h.logicType.width;
}

abstract production nilLogicParameter
top::LogicParameters ::=
{
  top.pps = [];
  top.host = nilParameters();
  top.logicTypes = [];
  top.logicValueDefs = [];
  top.errors := [];
  top.flowDefs = [];
}

nonterminal LogicParameter with logicValueEnv, bitIndex, pp, name, host<ParameterDecl>, logicType, logicValueDefs, errors, flowIds, flowDefs;

abstract production logicParameter
top::LogicParameter ::= typeExpr::LogicTypeExpr id::Name
{
  top.pp = pp"${typeExpr.pp} ${id.pp}";
  top.name = id.name;
  top.host = parameterDecl([], typeExpr.host, baseTypeExpr(), justName(id), nilAttribute());
  top.logicType = typeExpr.logicType;
  top.logicValueDefs = [pair(id.name, parameterLogicValueItem(top, id.location))];
  top.errors := typeExpr.errors;
  top.flowIds =
    map(
      \ i::Integer -> s"${id.name}${toString(i)}_${toString(genInt())}",
      range(0, typeExpr.logicType.width));
  top.flowDefs =
    zipWith(
      flowDef,
      top.flowIds,
      map(parameterFlowExpr, range(top.bitIndex, top.bitIndex + typeExpr.logicType.width)));
  
  top.errors <- id.logicValueRedeclarationCheck;
}

function getLogicFunctionHostName
Name ::= id::Name
{
  return name("_logic_function_" ++ id.name, location=id.location);
}

global builtin::Location = builtinLoc("logic");
