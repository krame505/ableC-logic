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
  
  -- TODO: Check for include of logic.xh
  local localErrors::[Message] = f.errors;
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
  top.pp = parens( ppConcat([ id.pp, parens( ppImplode( cat( comma(), space() ), args.pps ))]) );
  forwards to logicFunctionCallExpr(hostMode(), id, args, location=top.location);
}

abstract production logicFunctionCallExpr
top::Expr ::= mode::LogicMode id::Name args::Exprs
{
  top.pp = pp"logic ${mode.pp} call ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  local localErrors::[Message] = id.logicFunctionLookupCheck ++ args.errors;
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
  top.pp = pp"logic ${mode.pp} init ${id.pp};";
  top.labelDefs := [];
  forwards to mode.initProd(id);
}

abstract production softLogicFunctionInitStmt
top::Stmt ::= id::Name
{
  top.pp = pp"logic soft init ${id.pp};";
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
  nandFlowGraph.numInputs = numInputs;
  local numGatesRequired::Integer = nandFlowGraph.numGatesRequired;
  local criticalPathLength::Integer = nandFlowGraph.criticalPathLength;
  
  -- TODO: Check for include of logic.xh
  local localErrors::[Message] =
    if !null(id.logicFunctionLookupCheck)
    then id.logicFunctionLookupCheck
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
  
  local fwrd::Stmt = nandFlowGraph.softHostInitTrans;
  
  forwards to if !null(localErrors) then warnStmt(localErrors) else fwrd;
}

abstract production logicFunctionInvokeExpr
top::Expr ::= mode::LogicMode id::Name args::Exprs
{
  top.pp = pp"logic ${mode.pp} invoke ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  forwards to mode.invokeProd(id, args, top.location);
}

abstract production hostLogicFunctionInvokeExpr
top::Expr ::= id::Name args::Exprs
{
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

abstract production softLogicFunctionInvokeExpr
top::Expr ::= id::Name args::Exprs
{
  top.pp = pp"logic soft invoke ${id.pp}(${ppImplode( cat( comma(), space() ), args.pps )})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  args.expectedTypes =
    map(logicTypeToHostType(top.env, _), id.logicFunctionItem.parameterLogicTypes);
  args.argumentPosition = 1;
  args.callExpr = top;
  args.callVariadic = false;
  
  local localErrors::[Message] = id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  -- TODO: Check for include of logic.xh
  local fwrd::Expr = directCallExpr(name("soft_invoke", location=builtin), args, location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

synthesized attribute initProd::(Stmt ::= Name);
synthesized attribute invokeProd::(Expr ::= Name Exprs Location);

nonterminal LogicMode with env, pp, initProd, invokeProd;

abstract production hostMode
top::LogicMode ::= 
{
  top.pp = pp"host";
  top.initProd = \ id::Name -> nullStmt();
  top.invokeProd = hostLogicFunctionInvokeExpr(_, _, location=_);
}

abstract production softMode
top::LogicMode ::= 
{
  top.pp = pp"soft";
  top.initProd = softLogicFunctionInitStmt;
  top.invokeProd = softLogicFunctionInvokeExpr(_, _, location=_);
}

abstract production hardMode
top::LogicMode ::= 
{
  top.pp = pp"hard";
  top.initProd = error("Not yet implemented");
  top.invokeProd = error("Not yet implemented");
}

abstract production defaultMode
top::LogicMode ::= 
{
  top.pp = pp"default";
  forwards to
    if !null(lookupMisc("--xc-logic-soft", top.env))
    then softMode()
    else if !null(lookupMisc("--xc-logic-hard", top.env))
    then hardMode()
    else hostMode();
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
      body.host);
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

global builtin::Location = builtinLoc("logic");
