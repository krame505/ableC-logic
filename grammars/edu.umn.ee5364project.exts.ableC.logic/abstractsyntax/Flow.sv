grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
-- TODO: Rename these?
synthesized attribute flowResult::[FlowExpr];
synthesized attribute flowResults::[[FlowExpr]];
-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute flowDefs::[FlowDef];

-- Used to build the flowEnv Map
synthesized attribute flowContribs::[Pair<String Decorated FlowExpr>];

-- The flow graph provided to each element of the graph as a Map
autocopy attribute flowEnv::tm:Map<String Decorated FlowExpr>;

-- Functor and supporting attributes for function stitching
synthesized attribute renamed<a>::a;
autocopy attribute renameFn::(String ::= String);

synthesized attribute paramSubstituted<a>::a;
autocopy attribute parameters::[[FlowExpr]];

nonterminal FlowGraph with renameFn, parameters, pp, renamed<FlowGraph>, paramSubstituted<FlowGraph>, flowDefs, flowResult;
flowtype FlowGraph = decorate {};

abstract production flowGraph
top::FlowGraph ::= flowDefs::FlowDefs flowResult::FlowExprs
{
  propagate renamed, paramSubstituted;
  top.pp =
    ppConcat([terminate(line(), flowDefs.pps), pp"return ${ppImplode(pp", ", flowResult.pps)};"]);
  top.flowDefs = flowDefs.flowDefs;
  top.flowResult = flowResult.flowResult;

  flowDefs.flowEnv = tm:empty(compareString);
  flowResult.flowEnv = tm:add(flowDefs.flowContribs, flowDefs.flowEnv);
}

nonterminal FlowDefs with flowEnv, renameFn, parameters, pps, renamed<FlowDefs>, paramSubstituted<FlowDefs>, flowDefs, flowContribs;
flowtype FlowDefs = decorate {flowEnv};

abstract production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  propagate renamed, paramSubstituted;
  top.pps = h.pp :: t.pps;
  top.flowDefs = h :: t.flowDefs;
  top.flowContribs = h.flowContribs ++ t.flowContribs;
  
  t.flowEnv = tm:add(h.flowContribs, top.flowEnv);
}

abstract production nilFlowDef
top::FlowDefs ::= 
{
  propagate renamed, paramSubstituted;
  top.pps = [];
  top.flowDefs = [];
  top.flowContribs = [];
}

nonterminal FlowDef with flowEnv, renameFn, parameters, pp, renamed<FlowDef>, paramSubstituted<FlowDef>, flowContribs;
flowtype FlowDef = decorate {flowEnv};

abstract production flowDef
top::FlowDef ::= id::String fe::FlowExpr
{
  propagate paramSubstituted;
  top.pp = pp"${text(id)} = ${fe.pp};";
  top.renamed = flowDef(top.renameFn(id), fe.renamed);
  top.flowContribs = [pair(id, fe)];
}

nonterminal FlowExprs with flowEnv, renameFn, parameters, pps, renamed<FlowExprs>, paramSubstituted<FlowExprs>, flowResult;

abstract production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  propagate renamed, paramSubstituted;
  top.pps = h.pp :: t.pps;
  top.flowResult = h :: t.flowResult;
}

abstract production nilFlowExpr
top::FlowExprs ::= 
{
  propagate renamed, paramSubstituted;
  top.pps = [];
  top.flowResult = [];
}

nonterminal FlowExpr with flowEnv, renameFn, parameters, pp, renamed<FlowExpr>, paramSubstituted<FlowExpr>;
flowtype FlowExpr = decorate {flowEnv};

abstract production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  propagate renamed, paramSubstituted;
  top.pp = if b then pp"true" else pp"false";
}

abstract production parameterFlowExpr
top::FlowExpr ::= paramIndex::Integer bitIndex::Integer
{
  propagate renamed;
  top.pp = cat(braces(text(toString(paramIndex))), brackets(text(toString(bitIndex))));
  top.paramSubstituted = head(drop(bitIndex, head(drop(paramIndex, top.parameters))));
}

abstract production nodeFlowExpr
top::FlowExpr ::= id::String
{
  propagate paramSubstituted;
  top.pp = text(id);
  top.renamed = nodeFlowExpr(top.renameFn(id));
  
  production refNode::Decorated FlowExpr = head(tm:lookup(id, top.flowEnv));
}

abstract production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
}

abstract production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
}

abstract production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  propagate renamed, paramSubstituted;
  top.pp = pp"(!${e.pp})";
}

-- Utility functions
function renameFlowGraph
FlowGraph ::= renameFn::(String ::= String) fg::FlowGraph
{
  fg.renameFn = renameFn;
  return fg.renamed;
}

function subParamsFlowGraph
FlowGraph ::= parameters::[[FlowExpr]] fg::FlowGraph
{
  fg.parameters = parameters;
  return fg.paramSubstituted;
}

function buildFlowGraph
FlowGraph ::= flowDefs::[FlowDef] flowResult::[FlowExpr]
{
  return
    flowGraph(
      foldr(consFlowDef, nilFlowDef(), flowDefs),
      foldr(consFlowExpr, nilFlowExpr(), flowResult));
}
