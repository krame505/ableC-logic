grammar edu:umn:ee5364project:exts:ableC:logic:concretesyntax;

terminal Init_t       'init';
terminal Invoke_t     'invoke';
terminal Call_t       'call';
terminal StaticInit_t 'static_init';

terminal Host_t  'host';
terminal Trans_t 'trans';

concrete production logicFunctionCallExpr_c
top::PrimaryExpr_c ::= 'logic' mode::LogicMode_c 'call' id::Identifier_t '(' args::ArgumentExprList_c ')'
{
  top.ast = logicFunctionCallExpr(mode.ast, fromId(id), foldExpr(args.ast), location=top.location);
}

concrete production logicFunctionCallNoArgsExpr_c
top::PrimaryExpr_c ::= 'logic' mode::LogicMode_c 'call' id::Identifier_t '(' ')'
{
  top.ast = logicFunctionCallExpr(mode.ast, fromId(id), nilExpr(), location=top.location);
}

concrete production logicFunctionInitStmt_c
top::BlockItem_c ::= 'logic' mode::LogicMode_c 'init' id::Identifier_t ';'
{
  top.ast = [logicFunctionInitStmt(mode.ast, fromId(id))];
}

concrete production logicFunctionInvokeExpr_c
top::PrimaryExpr_c ::= 'logic' mode::LogicMode_c 'invoke' id::Identifier_t '(' args::ArgumentExprList_c ')'
{
  top.ast = logicFunctionInvokeExpr(mode.ast, fromId(id), foldExpr(args.ast), location=top.location);
}

concrete production logicFunctionInvokeNoArgsExpr_c
top::PrimaryExpr_c ::= 'logic' mode::LogicMode_c 'invoke' id::Identifier_t '(' ')'
{
  top.ast = logicFunctionInvokeExpr(mode.ast, fromId(id), nilExpr(), location=top.location);
}

concrete production logicFunctionStaticInitExpr_c
top::BlockItem_c ::= 'logic' mode::LogicMode_c 'static_init' id::Identifier_t '(' args::ArgumentExprList_c  ')'
{
  top.ast = [logicFunctionStaticInitStmt(mode.ast, fromId(id), foldExpr(args.ast))];
}

concrete production logicFunctionStaticInitNoArgsExpr_c
top::BlockItem_c ::= 'logic' mode::LogicMode_c 'static_init' id::Identifier_t '(' ')'
{
  top.ast = [logicFunctionStaticInitStmt(mode.ast, fromId(id), nilExpr())];
}

nonterminal LogicMode_c with ast<LogicMode>, location;

concrete productions top::LogicMode_c
| 'host'
  { top.ast = hostMode(location=top.location); }
| 'trans'
  { top.ast = transMode(location=top.location); }
| 'default'
  { top.ast = defaultMode(location=top.location); }
| 
  { top.ast = defaultMode(location=top.location); }
