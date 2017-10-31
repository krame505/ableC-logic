grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

nonterminal LogicStmts with logicValueEnv, logicFunctionEnv, pps, host<Stmt>, logicValueDefs, errors;

abstract production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  top.pps = h.pp :: t.pps;
  top.host = seqStmt(h.host, t.host);
  top.logicValueDefs = h.logicValueDefs ++ t.logicValueDefs;
  top.errors := h.errors ++ t.errors;
}

abstract production resultLogicStmt
top::LogicStmts ::= result::LogicExpr
{
  top.pps = [pp"return ${result.pp};"];
  top.host = returnStmt(justExpr(result.host));
  top.logicValueDefs = [];
  top.errors := [];
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
            justInitializer(exprInitializer(value.host))), 
          nilDeclarator())));
  top.logicValueDefs = [pair(id.name, logicValueItem(typeExpr.logicType, id.location))];
  top.errors := typeExpr.errors ++ value.errors;
  
  top.errors <- id.logicValueRedeclarationCheck;
}