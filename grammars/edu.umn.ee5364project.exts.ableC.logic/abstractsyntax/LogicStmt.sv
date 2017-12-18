grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

autocopy attribute givenReturnLogicType::LogicType;

synthesized attribute hostPreDecls::Decls;

nonterminal LogicStmts with logicValueEnv, logicFunctionEnv, givenReturnLogicType, pps, hostPreDecls, host<Stmt>, logicValueDefs, errors, hasFlowGraph, flowDefs, flowExprs;

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
  top.flowExprs = t.flowExprs;
  
  t.logicValueEnv = addScope(h.logicValueDefs, top.logicValueEnv);
}

abstract production resultLogicStmt
top::LogicStmts ::= result::LogicExpr
{
  top.pps = [pp"return ${result.pp};"];
  top.hostPreDecls = nilDecl();
  top.host = returnStmt(justExpr(result.host));
  top.logicValueDefs = [];
  top.errors := result.errors;
  top.hasFlowGraph = null(top.errors) && result.hasFlowGraph;
  top.flowDefs = result.flowDefs;
  top.flowExprs = result.flowExprs;
  
  top.errors <-
    if result.logicType.width > top.givenReturnLogicType.width
    then [err(result.location, s"Result type ${show(80, result.logicType.pp)} is wider than declared type ${show(80, top.givenReturnLogicType.pp)}")]
    else [];
}

synthesized attribute hostPreDecl::Decl;

nonterminal LogicStmt with logicValueEnv, logicFunctionEnv, pp, hostPreDecl, host<Stmt>, logicValueDefs, logicType, hasFlowGraph, errors, flowIds, flowDefs;

abstract production declLogicStmt
top::LogicStmt ::= typeExpr::LogicTypeExpr id::Name value::LogicExpr
{
  top.pp = pp"${typeExpr.pp} ${id.pp} = ${value.pp};";
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
  top.logicValueDefs = [pair(id.name, declLogicValueItem(top, id.location))];
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
