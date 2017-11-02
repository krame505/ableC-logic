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
  
  local localErrors::[Message] = f.errors;
  local fwrd::Decl = hostTrans;
  local errorFwrd::Decl = hostErrorTrans;
  
  forwards to
    decls(
      foldDecl([
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
  
  local hostTrans::Expr = directCallExpr(getLogicFunctionHostName(id), args, location=top.location);
  
  local localErrors::[Message] = id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local fwrd::Expr = hostTrans;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

synthesized attribute parameterNames::[String];
synthesized attribute parameterLogicTypes::[LogicType];
synthesized attribute returnLogicType::LogicType;

nonterminal LogicFunctionDecl with logicFunctionEnv, pp, host<FunctionDecl>, logicFunctionDefs, errors, logicFlowGraph, name, parameterNames, parameterLogicTypes, returnLogicType, sourceLocation;

abstract production logicFunctionDecl
top::LogicFunctionDecl ::= id::Name ret::LogicTypeExpr params::LogicParameters body::LogicStmts
{
  top.pp =
    ppConcat([
      text("logic"), space(), ret.pp, space(), parens(ppImplode(text(", "), params.pps)),
      braces(cat(line(), nestlines(2, terminate(line(), body.pps))))]);
  top.host =
    functionDecl(
      [], nilSpecialSpecifier(),
      ret.host,
      functionTypeExprWithArgs(baseTypeExpr(), params.host, false, nilQualifier()),
      getLogicFunctionHostName(id),
      nilAttribute(), nilDecl(),
      body.host);
  top.logicFunctionDefs = [pair(id.name, logicFunctionItem(top))];
  top.errors := ret.errors ++ params.errors ++ body.errors;
  top.logicFlowGraph = buildFunctionLogicFlowGraph(_, top.logicFunctionEnv, params, body);
  
  top.name = id.name;
  top.parameterNames = params.names;
  top.parameterLogicTypes = params.logicTypes;
  top.returnLogicType = ret.logicType;
  top.sourceLocation = id.location;
  
  params.logicValueEnv = emptyScope();
  body.logicValueEnv = addScope(params.logicValueDefs, params.logicValueEnv);
  body.logicFunctionEnv = openScope(top.logicFunctionEnv); -- In case we ever add nested logic functions I guess?
  body.givenReturnLogicType = ret.logicType;
  
  top.errors <- id.logicFunctionRedeclarationCheck;
}

function buildFunctionLogicFlowGraph
[LogicFlowExpr] ::= paramLogicFlow::[[LogicFlowExpr]] logicFunctionEnv::Scopes<LogicFunctionItem> params::LogicParameters body::LogicStmts
{
  params.givenLogicFlows = paramLogicFlow;
  body.logicFunctionEnv = logicFunctionEnv;
  body.logicFlowEnv = addScope(params.logicFlowDefs, emptyScope());
  return body.logicFlow;
}

synthesized attribute names::[String];

inherited attribute givenLogicFlows::[[LogicFlowExpr]];

nonterminal LogicParameters with logicValueEnv, givenLogicFlows, pps, names, host<Parameters>, logicTypes, logicValueDefs, errors, logicFlowDefs;

abstract production consLogicParameter
top::LogicParameters ::= h::LogicParameter  t::LogicParameters
{
  top.pps = h.pp :: t.pps;
  top.names = h.name :: t.names;
  top.host = consParameters(h.host, t.host);
  top.logicTypes = h.logicType :: t.logicTypes;
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  top.logicFlowDefs = h.logicFlowDefs ++ t.logicFlowDefs;
  
  t.logicValueEnv = addScope(h.logicValueDefs, h.logicValueEnv);
  h.givenLogicFlow = head(top.givenLogicFlows);
  t.givenLogicFlows = tail(top.givenLogicFlows);
}

abstract production nilLogicParameter
top::LogicParameters ::=
{
  top.pps = [];
  top.names = [];
  top.host = nilParameters();
  top.logicTypes = [];
  top.logicValueDefs = [];
  top.errors := [];
  top.logicFlowDefs = [];
}

inherited attribute givenLogicFlow::[LogicFlowExpr];

nonterminal LogicParameter with logicValueEnv, givenLogicFlow, pp, name, host<ParameterDecl>, logicType, logicValueDefs, errors, logicFlowDefs;

abstract production logicParameter
top::LogicParameter ::= typeExpr::LogicTypeExpr id::Name
{
  top.pp = pp"${typeExpr.pp} ${id.pp}";
  top.name = id.name;
  top.host = parameterDecl([], typeExpr.host, baseTypeExpr(), justName(id), nilAttribute());
  top.logicType = typeExpr.logicType;
  top.logicValueDefs = [pair(id.name, logicValueItem(typeExpr.logicType, id.location))];
  top.errors := typeExpr.errors;
  top.logicFlowDefs = [pair(id.name, decorateLogicFlow(top.givenLogicFlow))];
  
  top.errors <- id.logicValueRedeclarationCheck;
}

function getLogicFunctionHostName
Name ::= id::Name
{
  return name("_logic_function_" ++ id.name, location=id.location);
}

global builtin::Location = builtinLoc("logic");
