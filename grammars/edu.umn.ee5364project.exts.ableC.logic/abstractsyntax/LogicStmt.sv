grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

-- Declarations of all variables, placed at the beginning of the function
synthesized attribute hostPreDecls::Decls;

-- Threaded environment containing flow expressions for static updates
autocopy attribute staticFlowEnv::tm:Map<String [FlowExpr]>;
synthesized attribute staticFlowEnvOut::tm:Map<String [FlowExpr]>;

nonterminal LogicStmts with logicValueEnv, logicFunctionEnv, staticFlowEnv, pps, hostPreDecls, host<Stmt>, logicValueDefs, errors, hasFlowGraph, flowDefs, staticFlowEnvOut;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  top.pps = h.pp :: t.pps;
  top.hostPreDecls = consDecl(h.hostPreDecl, t.hostPreDecls);
  top.host = seqStmt(h.host, t.host);
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  top.hasFlowGraph = h.hasFlowGraph && t.hasFlowGraph;
  top.flowDefs = h.flowDefs ++ t.flowDefs;
  
  t.logicValueEnv = addScope(h.logicValueDefs, top.logicValueEnv);
  
  t.staticFlowEnv = h.staticFlowEnvOut;
  top.staticFlowEnvOut = t.staticFlowEnvOut;
}

abstract production nilLogicStmt
top::LogicStmts ::= 
{
  top.pps = [];
  top.hostPreDecls = nilDecl();
  top.host = nullStmt();
  top.logicValueDefs = [];
  top.errors := [];
  top.hasFlowGraph = true;
  top.flowDefs = [];
  
  top.staticFlowEnvOut = top.staticFlowEnv;
}

synthesized attribute hostPreDecl::Decl;

nonterminal LogicStmt with logicValueEnv, logicFunctionEnv, staticFlowEnv, pp, hostPreDecl, host<Stmt>, logicValueDefs, hasFlowGraph, errors, flowDefs, staticFlowEnvOut;

abstract production valueDeclLogicStmt
top::LogicStmt ::= d::LogicValueDecl
{
  top.pp = d.pp;
  top.hostPreDecl = d.hostPreDecl;
  top.host = d.host;
  top.logicValueDefs = d.logicValueDefs;
  top.hasFlowGraph = null(top.errors) && d.hasFlowGraph;
  top.errors := d.errors;
  top.flowDefs = d.flowDefs;
  top.staticFlowEnvOut = top.staticFlowEnv;
}

abstract production staticUpdateLogicStmt
top::LogicStmt ::= id::Name value::LogicExpr
{
  top.pp = pp"${id.pp} := ${value.pp};";
  top.hostPreDecl =
    variableDecls(
      [staticStorageClass()], nilAttribute(),
      id.logicValueItem.logicType.logicTypeExpr.host,
      consDeclarator(
        declarator(id, baseTypeExpr(), nilAttribute(), nothingInitializer()),
        nilDeclarator()));
  top.host =
    exprStmt(
      eqExpr(
        declRefExpr(name("_static_" ++ id.name, location=builtin), location=builtin),
        value.host,
        location=builtin));
  top.logicValueDefs = [];
  top.hasFlowGraph = null(top.errors) && value.hasFlowGraph;
  top.errors := value.errors;
  top.flowDefs = value.flowDefs;
  
  top.staticFlowEnvOut = tm:add([pair(id.name, value.flowExprs)], top.staticFlowEnv);
  
  top.errors <- id.logicValueLookupCheck;
  top.errors <-
    if !id.logicValueItem.isStatic
    then [err(id.location, "Can only perform update on static logic values")]
    else [];
  top.errors <-
    if !null(tm:lookup(id.name, top.staticFlowEnv))
    then [err(id.location, s"An update for ${id.name} is already defined")] 
    else [];
}

nonterminal LogicValueDecl with logicValueEnv, logicFunctionEnv, pp, sourceLocation, hostPreDecl, host<Stmt>, logicValueDefs, logicType, hasFlowGraph, errors, flowIds, flowDefs;

abstract production logicValueDecl
top::LogicValueDecl ::= typeExpr::LogicTypeExpr id::Name value::LogicExpr
{
  top.pp = pp"${typeExpr.pp} ${id.pp} = ${value.pp};";
  top.sourceLocation = id.location;
  top.hostPreDecl =
    variableDecls(
      [], nilAttribute(),
      typeExpr.host,
      consDeclarator(
        declarator(id, baseTypeExpr(), nilAttribute(), nothingInitializer()),
        nilDeclarator()));
  top.host =
    exprStmt(
      eqExpr(
        declRefExpr(id, location=builtin),
        getHostCastProd(value.logicType, typeExpr.logicType)(value.host, builtin),
        location=builtin));
  top.logicValueDefs = [pair(id.name, declLogicValueItem(top))];
  top.logicType = typeExpr.logicType;
  top.hasFlowGraph = null(top.errors) && value.hasFlowGraph;
  top.errors := typeExpr.errors ++ value.errors;
  top.flowIds =
    map(
      \ i::Integer -> s"${id.name}${toString(i)}_${toString(genInt())}",
      range(0, typeExpr.logicType.width));
  local bitPad::Pair<[FlowDef] [FlowExpr]> = typeExpr.logicType.bitPad(value.flowExprs);
  top.flowDefs = value.flowDefs ++ bitPad.fst ++ zipWith(flowDef, top.flowIds, bitPad.snd);
  
  top.errors <- id.logicValueRedeclarationCheck;
  top.errors <-
    if value.logicType.width > typeExpr.logicType.width
    then [err(value.location, s"Value type ${show(80, value.logicType.pp)} is wider than declared ${show(80, typeExpr.logicType.pp)}")]
    else [];
}
