grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

nonterminal LogicStmts_c with ast<LogicStmts>;

concrete productions top::LogicStmts_c
| h::LogicStmt_c t::LogicStmts_c
  { top.ast = consLogicStmt(h.ast, t.ast); }
| 
  { top.ast = nilLogicStmt(); }

terminal New_t 'new';

nonterminal LogicStmt_c with ast<LogicStmt>;

concrete productions top::LogicStmt_c
| ty::LogicTypeExpr_c id::Identifier_t '=' e::LogicExpr_c ';'
  { top.ast = valueDeclLogicStmt(logicValueDecl(ty.ast, fromId(id), e.ast)); } 
| 'new' id::Identifier_t '=' e::LogicExpr_c ';'
  { top.ast = staticUpdateLogicStmt(fromId(id), e.ast); }
