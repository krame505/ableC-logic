grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;
imports silver:util:raw:treemap as tm;

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
  local hostTrans::Decl = f.host;
  local hostErrorTrans::Decl =
    defsDecl([valueDef("_logic_function_" ++ f.name, errorValueItem())]);
  
  forwards to
    decls(
      foldDecl([
        if !null(lookupMisc("--xc-logic-output-flow-graphs", top.env))
        then txtDecl(s"/*\n${show(80, f.flowGraph.pp)}\n*/")
        else decls(nilDecl()),
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
  
  local localErrors::[Message] = mode.errors ++ id.logicFunctionLookupCheck;
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
  top.functionDefs := [];
  forwards to mode.initProd(id);
}

abstract production transLogicFunctionInitStmt
top::Stmt ::= id::Name
{
  propagate substituted;
  top.pp = pp"logic trans init ${id.pp};";
  top.functionDefs := [];
  
  -- Look up specification values defined in the header file
  local wordSize::Integer =
    case lookupValue("WORD_SIZE", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numDirectInputs::Integer =
    case lookupValue("NUM_DIRECT_INPUTS", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numDirectOutputs::Integer =
    case lookupValue("NUM_DIRECT_OUTPUTS", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numStaticChannels::Integer =
    case lookupValue("NUM_STATIC_CHANNELS", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numGates::Integer =
    case lookupValue("NUM_GATES", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local maxCriticalPathLength::Integer =
    case lookupValue("MAX_CRITICAL_PATH_LENGTH", top.env) of
      [enumValueItem(enumItem(_, justExpr(realConstant(integerConstant(val, _, _)))))] -> toInt(val)
    | _ -> error("Failed to look up env value")
    end;
  local numInputs::Integer = numDirectInputs + numStaticChannels;
  local numOutputs::Integer = numDirectOutputs + numStaticChannels;
  local numChannels::Integer = numInputs + numGates;
  local numInputWords::Integer = numDirectInputs / wordSize;
  local numStaticChannelWords::Integer = numStaticChannels / wordSize;
  
  id.logicFunctionEnv = top.env.logicFunctions;
  local flowGraph::FlowGraph = id.logicFunctionItem.flowGraph;
  local nandFlowGraph::NANDFlowGraph = flowGraph.nandFlowGraph;
  nandFlowGraph.numDirectInputs = numDirectInputs;
  nandFlowGraph.numStaticChannels = numStaticChannels;
  local numGatesRequired::Integer = nandFlowGraph.numGatesRequired;
  local criticalPathLength::Integer = nandFlowGraph.criticalPathLength;
  
  local stats::String =
s"""Translation stats for logic function ${id.name}:
# of NAND gates used: ${toString(numGatesRequired)}
Critical path length: ${toString(criticalPathLength)}

""";
  
  local initialChecks::[Message] =
    (if !null(lookupMisc("--xc-logic-soft", top.env)) || null(lookupMisc("--xc-logic-hard", top.env))
     then checkLogicSoftHInclude(id.location, top.env)
     else checkLogicHInclude(id.location, top.env)) ++ id.logicFunctionLookupCheck;
  local semanticErrors::[Message] =
    (if length(id.logicFunctionItem.parameterLogicTypes) > numInputWords
     then [err(id.location, s"Translation requires invoked logic function to have no more than ${toString(numInputWords)} parameters (got ${toString(length(id.logicFunctionItem.parameterLogicTypes))})")]
     else []) ++
    (if length(id.logicFunctionItem.staticParameterLogicTypes) > numStaticChannelWords
     then [err(id.location, s"Translation requires invoked logic function to have no more than ${toString(numStaticChannelWords)} static parameters (got ${toString(length(id.logicFunctionItem.staticParameterLogicTypes))})")]
     else []) ++
    concat(
      zipWith(
        \ i::Integer t::LogicType ->
          if t.width != wordSize
          then [err(id.location, s"Translation requires invoked logic function parameter ${toString(i)} to have width ${toString(wordSize)} (got ${toString(t.width)})")]
          else [],
        range(1, length(id.logicFunctionItem.parameterLogicTypes) + 1),
        id.logicFunctionItem.parameterLogicTypes) ++
      zipWith(
        \ i::Integer t::LogicType ->
          if t.width != wordSize
          then [err(id.location, s"Translation requires invoked logic function static parameter ${toString(i)} to have width ${toString(wordSize)} (got ${toString(t.width)})")]
          else [],
        range(1, length(id.logicFunctionItem.staticParameterLogicTypes) + 1),
        id.logicFunctionItem.staticParameterLogicTypes)) ++
    (if id.logicFunctionItem.resultLogicType.width != numDirectOutputs
     then [err(id.location, s"Translation requires invoked logic function result to have width ${toString(numDirectOutputs)} (got ${toString(id.logicFunctionItem.resultLogicType.width)})")]
     else []);
  local translationErrors::[Message] =
    (if numGatesRequired > numGates
     then [err(id.location, s"Insufficient gates available for translation (required ${toString(numGatesRequired)}, allowed ${toString(numGates)})")]
     else []) ++
    (if criticalPathLength > maxCriticalPathLength
     then [err(id.location, s"Critical path is too long (required ${toString(criticalPathLength)}, allowed ${toString(maxCriticalPathLength)})")]
     else []);
  local localErrors::[Message] =
    if !null(initialChecks)
    then initialChecks
    else if !null(semanticErrors)
    then semanticErrors
    else if id.logicFunctionItem.hasFlowGraph
    then translationErrors
    else [];
  
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
  
  forwards to
    if !null(localErrors) || !id.logicFunctionItem.hasFlowGraph
    then warnStmt(localErrors)
    else statsFwrd;
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
    directCallExpr(
      getLogicFunctionHostName(id),
      consExpr(
        mkIntConst(0, builtin),
        appendExprs(
          args.hostInvokeTrans,
          foldExpr(
            repeat(
              mkIntConst(0, builtin),
              length(id.logicFunctionItem.staticParameterLogicTypes))))),
      location=top.location);
  
  forwards to mkErrorCheck(localErrors, fwrd);
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
    (if !null(lookupMisc("--xc-logic-soft", top.env)) || null(lookupMisc("--xc-logic-hard", top.env))
     then checkLogicSoftHInclude(id.location, top.env)
     else checkLogicHInclude(id.location, top.env)) ++
    id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local softFwrd::Expr =
    directCallExpr(
      name("soft_invoke", location=builtin),
      case args of
        nilExpr() -> consExpr(mkIntConst(0, builtin), consExpr(mkIntConst(0, builtin), nilExpr()))
      | consExpr(e, nilExpr()) -> consExpr(e, consExpr(mkIntConst(0, builtin), nilExpr()))
      | _ -> args
      end,
      location=builtin);
  local hardFwrd::Expr =
    substExpr(
      [declRefSubstitution(
         "__a__",
         case args of
           consExpr(h, _) -> h
         | _ -> mkIntConst(0, builtin)
         end),
       declRefSubstitution(
         "__b__",
         case args of
           consExpr(_, consExpr(h, _)) -> h
         | _ -> mkIntConst(0, builtin)
         end)],
      parseExpr(s"""
({proto_typedef int32_t;
  int32_t _result;
  asm("lgi %0, %1, %2" :
      "=r" (_result) :
      "r" (__a__), "r" (__b__));
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

abstract production logicFunctionStaticInitStmt
top::Stmt ::= mode::LogicMode id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic ${mode.pp} static_init ${id.pp}(${ppImplode(cat(comma(), space()), args.pps)})";
  forwards to mode.staticInitProd(id, args);
}

abstract production hostLogicFunctionStaticInitStmt
top::Stmt ::= id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic host static_init ${id.pp}(${ppImplode(cat(comma(), space()), args.pps)})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  args.expectedLogicTypes = id.logicFunctionItem.staticParameterLogicTypes;
  args.expectedTypes =
    map(logicTypeToHostType(top.env, _), id.logicFunctionItem.staticParameterLogicTypes);
  args.argumentPosition = 1;
  args.callExpr =
    decorate directCallExpr(id, args, location=id.location)
    with {env = top.env; returnType = top.returnType;};
  args.callVariadic = false;
  
  local localErrors::[Message] = id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local fwrd::Stmt =
    exprStmt(
      directCallExpr(
        getLogicFunctionHostName(id),
        consExpr(
          mkIntConst(1, builtin),
          appendExprs(
            foldExpr(
              repeat(
                mkIntConst(0, builtin),
                length(id.logicFunctionItem.parameterLogicTypes))),
            args.hostInvokeTrans)),
        location=id.location));
  
  forwards to
    if !null(localErrors) || !id.logicFunctionItem.hasFlowGraph
    then warnStmt(localErrors)
    else fwrd;
}

abstract production transLogicFunctionStaticInitStmt
top::Stmt ::= id::Name args::Exprs
{
  propagate substituted;
  top.pp = pp"logic trans static_init ${id.pp}(${ppImplode(cat(comma(), space()), args.pps)})";
  
  id.logicFunctionEnv = top.env.logicFunctions;
  
  args.expectedLogicTypes = id.logicFunctionItem.staticParameterLogicTypes;
  args.expectedTypes =
    map(logicTypeToHostType(top.env, _), id.logicFunctionItem.staticParameterLogicTypes);
  args.argumentPosition = 1;
  args.callExpr =
    decorate directCallExpr(id, args, location=id.location)
    with {env = top.env; returnType = top.returnType;};
  args.callVariadic = false;
  
  local localErrors::[Message] =
    (if !null(lookupMisc("--xc-logic-soft", top.env)) || null(lookupMisc("--xc-logic-hard", top.env))
     then checkLogicSoftHInclude(id.location, top.env)
     else checkLogicHInclude(id.location, top.env)) ++
    id.logicFunctionLookupCheck ++ args.errors ++ args.argumentErrors;
  local softFwrd::Stmt = args.softStaticInitTrans;
  local hardFwrd::Stmt = args.hardStaticInitTrans;
  
  local fwrd::Stmt =
    if !null(lookupMisc("--xc-logic-soft", top.env))
    then softFwrd
    else if !null(lookupMisc("--xc-logic-hard", top.env))
    then hardFwrd
    else softFwrd;
  
  forwards to
    if !null(localErrors) || !id.logicFunctionItem.hasFlowGraph
    then warnStmt(localErrors)
    else fwrd;
}

attribute expectedLogicTypes occurs on Exprs;
synthesized attribute hostInvokeTrans::Exprs occurs on Exprs;
synthesized attribute softStaticInitTrans::Stmt occurs on Exprs;
synthesized attribute hardStaticInitTrans::Stmt occurs on Exprs;

aspect production consExpr
top::Exprs ::= h::Expr t::Exprs
{
  top.hostInvokeTrans = consExpr(bitTrimExpr(head(top.expectedLogicTypes).width, h), t);
  local staticRegister::Integer = top.argumentPosition - 1;
  top.softStaticInitTrans =
    seqStmt(
      exprStmt(
        directCallExpr(
          name("soft_set_static", location=builtin),
          consExpr(mkIntConst(staticRegister, builtin), consExpr(h, nilExpr())),
          location=builtin)),
      t.softStaticInitTrans);
  top.hardStaticInitTrans =
    seqStmt(
      substStmt(
        [declRefSubstitution("__a__", h)],
        parseStmt(s"""asm("lgmove ${toString(staticRegister)}, %0" : : "r" (__a__));""")),
      t.hardStaticInitTrans);
  t.expectedLogicTypes = tail(top.expectedLogicTypes);
}

aspect production nilExpr
top::Exprs ::=
{
  top.hostInvokeTrans = nilExpr();
  top.softStaticInitTrans = nullStmt();
  top.hardStaticInitTrans = nullStmt();
}

synthesized attribute initProd::(Stmt ::= Name);
synthesized attribute invokeProd::(Expr ::= Name Exprs Location);
synthesized attribute staticInitProd::(Stmt ::= Name Exprs);

nonterminal LogicMode with env, pp, errors, initProd, invokeProd, staticInitProd, location;

abstract production hostMode
top::LogicMode ::= 
{
  top.pp = pp"host";
  top.errors := [];
  top.initProd = \ id::Name -> nullStmt();
  top.invokeProd = hostLogicFunctionInvokeExpr(_, _, location=_);
  top.staticInitProd = hostLogicFunctionStaticInitStmt(_, _);
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
  top.staticInitProd = transLogicFunctionStaticInitStmt(_, _);
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

synthesized attribute hasFlowGraph::Boolean;
synthesized attribute flowGraph::FlowGraph;
synthesized attribute parameterLogicTypes::[LogicType];
synthesized attribute staticParameterLogicTypes::[LogicType];
synthesized attribute resultLogicType::LogicType;

nonterminal LogicFunctionDecl with logicFunctionEnv, isTopLevel, pp, host<Decl>, logicFunctionDefs, errors, hasFlowGraph, flowGraph, name, parameterLogicTypes, staticParameterLogicTypes, resultLogicType, sourceLocation;

abstract production logicFunctionDecl
top::LogicFunctionDecl ::= id::Name ret::LogicTypeExpr params::LogicParameters staticParams::LogicParameters body::LogicStmts result::LogicExpr
{
  top.pp =
    ppConcat([
      text("logic"), space(), ret.pp, space(),
      parens(
        ppConcat([
          ppImplode(text(", "), params.pps),
          space(), semi(), space(),
          ppImplode(text(", "), staticParams.pps)])),
      braces(cat(line(), nestlines(2, terminate(line(), body.pps ++ [pp"return ${result.pp};"]))))]);
  top.host =
    substDecl(
      [typedefSubstitution("__res_type__", ret.host),
       parametersSubstitution("__params__", appendParameters(params.host, staticParams.staticHost)),
       stmtSubstitution("__pre_decls__", declStmt(decls(body.hostPreDecls))),
       stmtSubstitution("__static_init__", staticParams.staticHostInit),
       stmtSubstitution("__body__", body.host),
       declRefSubstitution("__result__", result.host)],
      decls(parseDecls(s"""
proto_typedef bool, __res_type__, __params__;
${if top.isTopLevel then "static" else ""} inline __res_type__ _logic_function_${id.name}(bool staticArgsProvided, __params__) {
  __pre_decls__;
  __res_type__ _result;
  if (!staticArgsProvided) {
    __body__;
    _result = __result__;
  }
  __static_init__;
  return _result;
}
""")));
  top.logicFunctionDefs = [pair(id.name, logicFunctionItem(top))];
  top.errors :=
    ret.errors ++ params.errors ++ staticParams.errors ++ staticParams.staticErrors ++
    body.errors ++ result.errors;
  top.hasFlowGraph = null(top.errors) && body.hasFlowGraph;
  local bitPad::Pair<[FlowDef] [FlowExpr]> = ret.logicType.bitPad(result.flowExprs);
  top.flowGraph =
    makeFlowGraph(
      id.name,
      params.flowDefs ++ staticParams.flowDefs ++ body.flowDefs ++ result.flowDefs ++ bitPad.fst,
      bitPad.snd ++ staticParams.staticFlowExprs).simplified;
  
  top.name = id.name;
  top.parameterLogicTypes = params.logicTypes;
  top.staticParameterLogicTypes = staticParams.logicTypes;
  top.resultLogicType = ret.logicType;
  top.sourceLocation = id.location;
  
  params.logicValueEnv = emptyScope();
  params.bitIndex = 0;
  params.isStaticIn = false;
  staticParams.logicValueEnv = addScope(params.logicValueDefs, params.logicValueEnv);
  staticParams.bitIndex = 0;
  staticParams.isStaticIn = true;
  staticParams.staticFlowEnv = body.staticFlowEnvOut;
  body.logicValueEnv = addScope(staticParams.logicValueDefs, staticParams.logicValueEnv);
  body.logicFunctionEnv = openScope(top.logicFunctionEnv); -- In case we ever add nested logic functions I guess?
  body.staticFlowEnv = tm:empty(compareString);
  result.logicValueEnv = addScope(body.logicValueDefs, body.logicValueEnv);
  
  top.errors <- id.logicFunctionRedeclarationCheck;
  top.errors <-
    if result.logicType.width > ret.logicType.width
    then [err(result.location, s"Result type ${show(80, result.logicType.pp)} is wider than declared type ${show(80, ret.logicType.pp)}")]
    else [];
}

inherited attribute bitIndex::Integer; -- Initially 0

autocopy attribute isStaticIn::Boolean;
synthesized attribute staticHost<a>::a;
synthesized attribute staticHostInit::Stmt;
synthesized attribute staticErrors::[Message];
synthesized attribute staticFlowExprs::[FlowExpr];

nonterminal LogicParameters with logicValueEnv, bitIndex, isStaticIn, staticFlowEnv, pps, host<Parameters>, staticHost<Parameters>, staticHostInit, logicTypes, logicValueDefs, errors, staticErrors, flowDefs, staticFlowExprs;
flowtype LogicParameters = decorate {logicValueEnv, bitIndex, isStaticIn};

abstract production consLogicParameter
top::LogicParameters ::= h::LogicParameterDecl  t::LogicParameters
{
  top.pps = h.pp :: t.pps;
  top.host = consParameters(h.host, t.host);
  top.staticHost = consParameters(h.staticHost, t.staticHost);
  top.staticHostInit = seqStmt(h.staticHostInit, t.staticHostInit);
  top.logicTypes = h.logicType :: t.logicTypes;
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  top.staticErrors = h.staticErrors ++ t.staticErrors;
  top.flowDefs = h.flowDefs ++ t.flowDefs;
  top.staticFlowExprs = h.staticFlowExprs ++ t.staticFlowExprs;
  
  t.logicValueEnv = addScope(h.logicValueDefs, h.logicValueEnv);
  h.bitIndex = top.bitIndex;
  t.bitIndex = top.bitIndex + h.logicType.width;
}

abstract production nilLogicParameter
top::LogicParameters ::=
{
  top.pps = [];
  top.host = nilParameters();
  top.staticHost = nilParameters();
  top.staticHostInit = nullStmt();
  top.logicTypes = [];
  top.logicValueDefs = [];
  top.errors := [];
  top.staticErrors = [];
  top.flowDefs = [];
  top.staticFlowExprs = [];
}

nonterminal LogicParameterDecl with logicValueEnv, bitIndex, isStaticIn, staticFlowEnv, pp, name, sourceLocation, host<ParameterDecl>, staticHost<ParameterDecl>, staticHostInit, logicType, logicValueDefs, staticErrors, errors, flowIds, flowDefs, staticFlowExprs;
flowtype LogicParameterDecl = decorate {logicValueEnv, bitIndex, isStaticIn};

abstract production logicParameter
top::LogicParameterDecl ::= typeExpr::LogicTypeExpr id::Name
{
  top.pp = pp"${typeExpr.pp} ${id.pp}";
  top.name = id.name;
  top.sourceLocation = id.location;
  top.host = parameterDecl([], typeExpr.host, baseTypeExpr(), justName(id), nilAttribute());
  local staticId::Name = name("_static_" ++ id.name, location=builtin);
  top.staticHost = parameterDecl([], typeExpr.host, baseTypeExpr(), justName(staticId), nilAttribute());
  top.staticHostInit =
    exprStmt(
      eqExpr(
        declRefExpr(id, location=builtin),
        declRefExpr(staticId, location=builtin),
        location=builtin));
  top.logicType = typeExpr.logicType;
  top.logicValueDefs = [pair(id.name, parameterLogicValueItem(top))];
  top.errors := typeExpr.errors;
  top.staticErrors =
    if null(tm:lookup(id.name, top.staticFlowEnv))
    then [err(id.location, s"Missing update in body for static value ${id.name}")]
    else [];
  top.flowIds =
    map(
      \ i::Integer -> s"${id.name}${toString(i)}_${toString(genInt())}",
      range(0, typeExpr.logicType.width));
  top.flowDefs =
    zipWith(
      flowDef,
      top.flowIds,
      map(
        parameterFlowExpr(top.isStaticIn, _),
        range(top.bitIndex, top.bitIndex + typeExpr.logicType.width)));
  top.staticFlowExprs = head(tm:lookup(id.name, top.staticFlowEnv));
  
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
    if null(lookupValue("_logic_xh", env))
    then [err(loc, "Missing include of logic.xh")]
    else [];
}

function checkLogicHInclude
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
