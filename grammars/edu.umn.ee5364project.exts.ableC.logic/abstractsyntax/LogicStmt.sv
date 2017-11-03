grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

autocopy attribute givenReturnLogicType::LogicType;

nonterminal LogicStmts with logicValueEnv, logicFunctionEnv, givenReturnLogicType, pps, host<Stmt>, logicValueDefs, errors, flowDefs, flowResult;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  top.pps = h.pp :: t.pps;
  top.host = seqStmt(h.host, t.host);
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  top.flowDefs = h.flowDefs ++ t.flowDefs;
  top.flowResult = t.flowResult;
  
  t.logicValueEnv = addScope(h.logicValueDefs, top.logicValueEnv);
}

abstract production resultLogicStmt
top::LogicStmts ::= result::LogicExpr
{
  top.pps = [pp"return ${result.pp};"];
  top.host = returnStmt(justExpr(result.host));
  top.logicValueDefs = [];
  top.errors := result.errors;
  top.flowDefs = result.flowDefs;
  top.flowResult = result.flowResult;
  
  top.errors <-
    if result.logicType.width > top.givenReturnLogicType.width
    then [err(result.location, s"Result type ${show(80, result.logicType.pp)} is wider than declared type ${show(80, top.givenReturnLogicType.pp)}")]
    else [];
}

nonterminal LogicStmt with logicValueEnv, logicFunctionEnv, pp, host<Stmt>, logicValueDefs, logicType, errors, flowIds, flowDefs;

abstract production declLogicStmt
top::LogicStmt ::= typeExpr::LogicTypeExpr id::Name value::LogicExpr
{
  top.pp = pp"${typeExpr.pp} ${id.pp} = ${value.pp};";
  top.host =
    declStmt( 
      variableDecls(
        [], nilAttribute(),
        typeExpr.host,
        consDeclarator( 
          declarator(
            id,
            baseTypeExpr(),
            nilAttribute(),
            justInitializer(
              exprInitializer(
                explicitCastExpr(
                  typeName(typeExpr.host, baseTypeExpr()),
                  value.host,
                  location=builtin)))),
          nilDeclarator())));
  top.logicValueDefs = [pair(id.name, declLogicValueItem(top, id.location))];
  top.logicType = typeExpr.logicType;
  top.errors := typeExpr.errors ++ value.errors;
  top.flowIds =
    map(
      \ i::Integer -> s"${id.name}${toString(i)}_${toString(genInt())}",
      range(0, typeExpr.logicType.width));
  top.flowDefs =
    value.flowDefs ++ zipWith(pair, top.flowIds, value.flowResult);
  
  top.errors <- id.logicValueRedeclarationCheck;
  top.errors <-
    if value.logicType.width > typeExpr.logicType.width
    then [err(value.location, s"Value type ${show(80, value.logicType.pp)} is wider than declared ${show(80, typeExpr.logicType.pp)}")]
    else [];
}
