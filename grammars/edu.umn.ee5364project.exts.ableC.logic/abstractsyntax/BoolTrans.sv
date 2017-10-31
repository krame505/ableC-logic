grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;
{-
synthesized attribute boolTrans<a>::a;
attribute boolTrans<LogicStmts> occurs on LogicStmts;
attribute boolTrans<LogicStmt> occurs on LogicStmt;
attribute boolTrans<[LogicExpr]> occurs on LogicExpr;

aspect production consLogicStmt
top::LogicStmts ::= h::LogicStmt t::LogicStmts
{
  propagate boolTrans;
}


aspect production resultLogicStmt
top::LogicStmts ::= result::LogicExpr
{
  propagate boolTrans;
}-}