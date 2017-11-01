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

synthesized attribute parameterLogicTypes::[LogicType];
synthesized attribute returnLogicType::LogicType;

nonterminal LogicFunctionDecl with logicFunctionEnv, pp, host<FunctionDecl>, logicFunctionDefs, errors, name, parameterLogicTypes, returnLogicType, sourceLocation;

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
  
  top.name = id.name;
  top.parameterLogicTypes = params.logicTypes;
  top.returnLogicType = ret.logicType;
  top.sourceLocation = id.location;
  
  params.logicValueEnv = emptyScope();
  body.logicValueEnv = addScope(params.logicValueDefs, params.logicValueEnv);
  body.logicFunctionEnv = openScope(top.logicFunctionEnv); -- In case we ever add nested logic functions I guess?
  body.givenReturnLogicType = ret.logicType;
  
  top.errors <- id.logicFunctionRedeclarationCheck;
}

nonterminal LogicParameters with logicValueEnv, pps, host<Parameters>, logicTypes, logicValueDefs, errors;

abstract production consLogicParameter
top::LogicParameters ::= h::LogicParameter  t::LogicParameters
{
  top.pps = h.pp :: t.pps;
  top.host = consParameters(h.host, t.host);
  top.logicTypes = h.logicType :: t.logicTypes;
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  
  t.logicValueEnv = addScope(h.logicValueDefs, h.logicValueEnv);
}

abstract production nilLogicParameter
top::LogicParameters ::=
{
  top.pps = [];
  top.host = nilParameters();
  top.logicTypes = [];
  top.logicValueDefs = [];
  top.errors := [];
}

nonterminal LogicParameter with logicValueEnv, pp, host<ParameterDecl>, logicType, logicValueDefs, errors;

abstract production logicParameter
top::LogicParameter ::= typeExpr::LogicTypeExpr id::Name
{
  top.pp = pp"${typeExpr.pp} ${id.pp}";
  top.host = parameterDecl([], typeExpr.host, baseTypeExpr(), justName(id), nilAttribute());
  top.logicType = typeExpr.logicType;
  top.logicValueDefs = [pair(id.name, logicValueItem(typeExpr.logicType, id.location))];
  top.errors := typeExpr.errors;
  
  top.errors <- id.logicValueRedeclarationCheck;
}

function getLogicFunctionHostName
Name ::= id::Name
{
  return name("_logic_function_" ++ id.name, location=id.location);
}

global builtin::Location = builtinLoc("logic");
