grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

autocopy attribute givenReturnLogicType::LogicType;

nonterminal LogicStmts with logicValueEnv, logicFunctionEnv, givenReturnLogicType, pps, host<Stmt>, logicValueDefs, errors;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  top.pps = h.pp :: t.pps;
  top.host = seqStmt(h.host, t.host);
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
  
  t.logicValueEnv = addScope(h.logicValueDefs, top.logicValueEnv);
}

abstract production resultLogicStmt
top::LogicStmts ::= result::LogicExpr
{
  top.pps = [pp"return ${result.pp};"];
  top.host = returnStmt(justExpr(result.host));
  top.logicValueDefs = [];
  top.errors := result.errors;
  top.errors <-
    if result.logicType.width > top.givenReturnLogicType.width
    then [err(result.location, s"Result type ${show(80, result.logicType.pp)} is wider than declared ${show(80, top.givenReturnLogicType.pp)}")]
    else [];
}

nonterminal LogicStmt with logicValueEnv, logicFunctionEnv, pp, host<Stmt>, logicValueDefs, errors;

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
  top.logicValueDefs = [pair(id.name, logicValueItem(typeExpr.logicType, id.location))];
  top.errors := typeExpr.errors ++ value.errors;
  
  top.errors <- id.logicValueRedeclarationCheck;
  top.errors <-
    if value.logicType.width > typeExpr.logicType.width
    then [err(value.location, s"Value type ${show(80, value.logicType.pp)} is wider than declared ${show(80, typeExpr.logicType.pp)}")]
    else [];
}