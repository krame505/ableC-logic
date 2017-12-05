grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction:parsing;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;

abstract production logicFunctionDeclaration
top::Decl ::= f::LogicFunctionDecl
{
  propagate substituted;
  top.pp = f.pp;
  
  f.logicFunctionEnv = top.env.logicFunctions;
  
  local localErrors::[Message] = checkLogicXHInclude(f.sourceLocation, top.env) ++ f.errors;
  local hostTrans::Decl = functionDeclaration(f.host);
  local hostErrorTrans::Decl =
    defsDecl([valueDef("_logic_function_" ++ f.name, errorValueItem())]);
  
  forwards to
    decls(
      foldDecl([
        txtDecl(s"/*\n${show(80, f.flowGraph.pp)}\n*/"),
        if !null(localErrors) then decls(foldDecl([warnDecl(localErrors), hostErrorTrans])) else hostTrans,
        defsDecl(
          valueDef(f.name, logicFunctionValueItem(top.env, f)) ::
          map(
            \ item::Pair<String LogicFunctionItem> -> logicFunctionDef(item.fst, item.snd),
            f.logicFunctionDefs))]));
}

abstract production logicFunctionDirectCallExpr
top::Expr ::= id::Name args::Exprs
{
  propagate substituted;
  top.pp = parens( ppConcat([ id.pp, parens( ppImplode( cat( comma(), space() ), args.pps ))]) );
  forwards to logicFunctionCallExpr(hostMode(location=top.location), id, args, location=top.location);
}

abstract production logicFunctionCallExpr
top::Expr ::= mode::LogicMode id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic ${mode.pp} call ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  local localErrors::[Message] = mode.errors;
  local fwrd::Expr = 
    stmtExpr(
      logicFunctionInitStmt(mode, id),
      logicFunctionInvokeExpr(mode, id, args, location=top.location),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production logicFunctionInitStmt
top::Stmt ::= mode::LogicMode id::Name
{
  propagate substituted;
  top.pp = pp"logic ${mode.pp} init ${id.pp};";
  top.labelDefs := [];
  forwards to mode.initProd(id);
}

abstract production transLogicFunctionInitStmt
top::Stmt ::= id::Name
{
  propagate substituted;
  top.pp = pp"logic trans init ${id.pp};";
  top.labelDefs := [];
  
  -- Look up specification values defined in the header file
  local numInputs::Integer =
    case lookupValue("NUM_INPUTS", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numGates::Integer =
    case lookupValue("NUM_GATES", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numOutputs::Integer =
    case lookupValue("NUM_OUTPUTS", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local maxCriticalPathLength::Integer =
    case lookupValue("MAX_CRITICAL_PATH_LENGTH", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numChannels::Integer = numInputs + numGates;
  local inputDataSize::Integer = numInputs / 2;
  
  id.logicFunctionEnv = top.env.logicFunctions;
  local flowGraph::FlowGraph = id.logicFunctionItem.flowGraph;
  local nandFlowGraph::NANDFlowGraph = flowGraph.nandFlowGraph;
  -- The actual width, not the expected one, so we can generate a translation for error checking
  -- even if the widths are wrong. 
  nandFlowGraph.numInputs = sum(map((.width), id.logicFunctionItem.parameterLogicTypes));
  local numGatesRequired::Integer = nandFlowGraph.numGatesRequired;
  local criticalPathLength::Integer = nandFlowGraph.criticalPathLength;
  
  local stats::String =
s"""Translation stats for logic function ${id.name}:
# of NAND gates used: ${toString(numGatesRequired)}
Critical path length: ${toString(criticalPathLength)}

""";
  
  local initialChecks::[Message] =
    checkLogicSoftHInclude(id.location, top.env) ++ id.logicFunctionLookupCheck;
  local localErrors::[Message] =
    if !null(initialChecks)
    then initialChecks
    else
      case id.logicFunctionItem.parameterLogicTypes of
        [t1, t2] ->
          (if t1.width != inputDataSize
           then [err(id.location, s"Translation requires invoked logic function parameter 1 to have width ${toString(numInputs / 2)} (got ${toString(t1.width)})")]
           else []) ++
          (if t2.width != inputDataSize
           then [err(id.location, s"Translation requires invoked logic function parameter 2 to have width ${toString(numInputs / 2)} (got ${toString(t2.width)})")]
           else [])
      | a -> [err(id.location, s"Translation requires invoked logic function to have exactly 2 parameters (got ${toString(length(a))})")]
      end ++
      (if id.logicFunctionItem.resultLogicType.width != numOutputs
       then [err(id.location, s"Translation requires invoked logic function result to have width ${toString(numOutputs)} (got ${toString(id.logicFunctionItem.resultLogicType.width)})")]
       else []) ++
      (if numGatesRequired > numGates
       then [err(id.location, s"Insufficient gates available for translation (required ${toString(numGatesRequired)}, allowed ${toString(numGates)})")]
       else []) ++
      (if criticalPathLength > maxCriticalPathLength
       then [err(id.location, s"Critical path is too long (required ${toString(criticalPathLength)}, allowed ${toString(maxCriticalPathLength)})")]
       else []);
  
  local fwrd::Stmt =
    if !null(lookupMisc("--xc-logic-soft", top.env))
    then nandFlowGraph.softHostInitTrans
    else if !null(lookupMisc("--xc-logic-hard", top.env))
    then nandFlowGraph.hardHostInitTrans
    else nandFlowGraph.softHostInitTrans;
  
  -- Hacky method of printing translation stats if requested from the command line
  local statsFwrd::Stmt =
    if !null(lookupMisc("--xc-logic-show-stats", top.env))
    then unsafeTrace(fwrd, print(stats, unsafeIO()))
    else fwrd;
  
  forwards to if !null(localErrors) then warnStmt(localErrors) else statsFwrd;
}

abstract production logicFunctionInvokeExpr
top::Expr ::= mode::LogicMode id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic ${mode.pp} invoke ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  forwards to mode.invokeProd(id, args, top.location);
}

abstract production hostLogicFunctionInvokeExpr
top::Expr ::= id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic host invoke ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  args.expectedLogicTypes = id.logicFunctionItem.parameterLogicTypes;
  args.expectedTypes =
    map(logicTypeToHostType(top.env, _), id.logicFunctionItem.parameterLogicTypes);
  args.argumentPosition = 1;
  args.callExpr = top;
  args.callVariadic = false;
  
  local localErrors::[Message] = id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local fwrd::Expr =
    directCallExpr(getLogicFunctionHostName(id), args.hostInvokeTrans, location=top.location);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

attribute expectedLogicTypes occurs on Exprs;
synthesized attribute hostInvokeTrans::Exprs occurs on Exprs;

aspect production consExpr
top::Exprs ::= h::Expr t::Exprs
{
  top.hostInvokeTrans = consExpr(bitTrimExpr(head(top.expectedLogicTypes).width, h), t);
  t.expectedLogicTypes = tail(top.expectedLogicTypes);
}

aspect production nilExpr
top::Exprs ::=
{
  top.hostInvokeTrans = nilExpr();
}

abstract production transLogicFunctionInvokeExpr
top::Expr ::= id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic trans invoke ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  args.expectedTypes =
    map(logicTypeToHostType(top.env, _), id.logicFunctionItem.parameterLogicTypes);
  args.argumentPosition = 1;
  args.callExpr = top;
  args.callVariadic = false;
  
  local localErrors::[Message] =
    checkLogicSoftHInclude(top.location, top.env) ++
    id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local softFwrd::Expr = directCallExpr(name("soft_invoke", location=builtin), args, location=builtin);
  local hardFwrd::Expr =
    substExpr(
      [declRefSubstitution("__a__", case args of consExpr(h, _) -> h end),
       declRefSubstitution("__b__", case args of consExpr(_, consExpr(h, _)) -> h end)],
      parseExpr(s"""
({proto_typedef int32_t;
  int32_t _result;
  asm("lgi %0, %1, %2" : "=r" (_result) : "r" (__a__) , "r" (__b__));
  _result;})
"""));
  
  local fwrd::Expr =
    if !null(lookupMisc("--xc-logic-soft", top.env))
    then softFwrd
    else if !null(lookupMisc("--xc-logic-hard", top.env))
    then hardFwrd
    else softFwrd;
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

synthesized attribute initProd::(Stmt ::= Name);
synthesized attribute invokeProd::(Expr ::= Name Exprs Location);

nonterminal LogicMode with env, pp, errors, initProd, invokeProd, location;

abstract production hostMode
top::LogicMode ::= 
{
  top.pp = pp"host";
  top.errors := [];
  top.initProd = \ id::Name -> nullStmt();
  top.invokeProd = hostLogicFunctionInvokeExpr(_, _, location=_);
}

abstract production transMode
top::LogicMode ::= 
{
  top.pp = pp"trans";
  top.errors :=
    if null(lookupMisc("--xc-logic-hard", top.env))
    then checkLogicSoftHInclude(top.location, top.env)
    else [];
  top.initProd = transLogicFunctionInitStmt;
  top.invokeProd = transLogicFunctionInvokeExpr(_, _, location=_);
}

abstract production defaultMode
top::LogicMode ::= 
{
  top.pp = pp"default";
  forwards to
    if !null(lookupMisc("--xc-logic-host", top.env))
    then hostMode(location=top.location)
    else if !null(lookupMisc("--xc-logic-trans", top.env))
    then transMode(location=top.location)
    else hostMode(location=top.location);
}

synthesized attribute flowGraph::FlowGraph;
synthesized attribute parameterLogicTypes::[LogicType];
synthesized attribute resultLogicType::LogicType;

nonterminal LogicFunctionDecl with logicFunctionEnv, isTopLevel, pp, host<FunctionDecl>, logicFunctionDefs, errors, flowGraph, name, parameterLogicTypes, resultLogicType, sourceLocation;

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
      seqStmt(declStmt(decls(body.hostPreDecls)), body.host));
  top.logicFunctionDefs = [pair(id.name, logicFunctionItem(top))];
  top.errors := ret.errors ++ params.errors ++ body.errors;
  local bitPad::Pair<[FlowDef] [FlowExpr]> = ret.logicType.bitPad(body.flowExprs);
  top.flowGraph =
    makeFlowGraph(id.name, params.flowDefs ++ body.flowDefs ++ bitPad.fst, bitPad.snd).simplified;
  
  top.name = id.name;
  top.parameterLogicTypes = params.logicTypes;
  top.resultLogicType = ret.logicType;
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

function checkLogicXHInclude
[Message] ::= loc::Location env::Decorated Env
{
  return
    if null(lookupValue("NUM_INPUTS", env))
    then [err(loc, "Missing include of logic.xh")]
    else [];
}

function checkLogicSoftHInclude
[Message] ::= loc::Location env::Decorated Env
{
  return
    if null(lookupValue("soft_invoke", env))
    then [err(loc, "Missing include of logic_soft.h")]
    else [];
}

global builtin::Location = builtinLoc("logic");
