grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

--import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
synthesized attribute logicFlow::[LogicFlowExpr];
synthesized attribute logicFlows::[[LogicFlowExpr]];
-- The complete flow graph computed for a logic function
synthesized attribute logicFlowGraph::([LogicFlowExpr] ::= [[LogicFlowExpr]]);

nonterminal LogicFlowExpr with pp;

abstract production constantLogicFlowExpr
top::LogicFlowExpr ::= b::Boolean
{
  top.pp = if b then pp"true" else pp"false";
}

abstract production refLogicFlowExpr
top::LogicFlowExpr ::= r::Decorated LogicFlowExpr -- n::String
{
  top.pp = brackets(r.pp); --text(n);
}

abstract production andLogicFlowExpr
top::LogicFlowExpr ::= e1::LogicFlowExpr e2::LogicFlowExpr
{
  top.pp = pp"(${e1.pp} & ${e2.pp})";
}

abstract production orLogicFlowExpr
top::LogicFlowExpr ::= e1::LogicFlowExpr e2::LogicFlowExpr
{
  top.pp = pp"(${e1.pp} | ${e2.pp})";
}

abstract production notLogicFlowExpr
top::LogicFlowExpr ::= e::LogicFlowExpr
{
  top.pp = pp"(!${e.pp})";
}

function decorateLogicFlow
[Decorated LogicFlowExpr] ::= logicFlow::[LogicFlowExpr]
{
  return map(\ lfe::LogicFlowExpr -> decorate lfe with {}, logicFlow);
}
