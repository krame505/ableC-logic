grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every bit of a logic expression
synthesized attribute flowExprs::[FlowExpr];
-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute flowDefs::[FlowDef];

-- Used to build the flowEnv Map
synthesized attribute flowContribs::[Pair<String Decorated FlowExpr>];

-- The flow graph provided to each element of the graph as a Map
autocopy attribute flowEnv::tm:Map<String Decorated FlowExpr>;

-- Functor and supporting attributes for function stitching
-- Apply a renaming function to every node id in the graph
synthesized attribute renamed<a>::a;
autocopy attribute renameFn::(String ::= String);

-- Subsitute all parameterFlowExprs for a parameter from the provided list
synthesized attribute paramSubstituted<a>::a;
autocopy attribute parameters::[FlowExpr];

-- Collapse together nodes with only one reference, remove unused nodes
synthesized attribute collapsed<a>::a;
synthesized attribute referencedNodes::[String];
synthesized attribute hasMultipleReferences::Boolean;
autocopy attribute referenceEnv::tm:Map<String Unit>;

nonterminal FlowGraph with renameFn, parameters, pp, flowDefs, flowExprs, renamed<FlowGraph>, paramSubstituted<FlowGraph>, collapsed<FlowGraph>;
flowtype FlowGraph = decorate {};

abstract production flowGraph
top::FlowGraph ::= flowDefs::FlowDefs flowExprs::FlowExprs
{
  propagate renamed, paramSubstituted, collapsed;
  top.pp =
    ppConcat([terminate(line(), flowDefs.pps), pp"return ${ppImplode(pp", ", flowExprs.pps)};"]);
  top.flowDefs = flowDefs.flowDefs;
  top.flowExprs = flowExprs.flowExprs;

  flowDefs.flowEnv = tm:empty(compareString);
  flowDefs.referenceEnv =
    tm:add(
      map(pair(_, unit()), flowDefs.referencedNodes ++ flowExprs.referencedNodes),
      tm:empty(compareString));
  flowExprs.flowEnv = tm:add(flowDefs.flowContribs, flowDefs.flowEnv);
  flowExprs.referenceEnv = flowDefs.referenceEnv;
}

nonterminal FlowDefs with flowEnv, renameFn, parameters, referenceEnv, pps, flowDefs, flowContribs, renamed<FlowDefs>, paramSubstituted<FlowDefs>, collapsed<FlowDefs>, referencedNodes;
flowtype FlowDefs = decorate {flowEnv, referenceEnv};

abstract production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  propagate renamed, paramSubstituted;
  top.pps = h.pp :: t.pps;
  top.flowDefs = h :: t.flowDefs;
  top.flowContribs = h.flowContribs ++ t.flowContribs;
  top.collapsed =
    if h.hasMultipleReferences then consFlowDef(h.collapsed, t.collapsed) else t.collapsed;
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
  
  t.flowEnv = tm:add(h.flowContribs, top.flowEnv);
}

abstract production nilFlowDef
top::FlowDefs ::= 
{
  propagate renamed, paramSubstituted, collapsed;
  top.pps = [];
  top.flowDefs = [];
  top.flowContribs = [];
  top.referencedNodes = [];
}

nonterminal FlowDef with flowEnv, renameFn, parameters, referenceEnv, pp, flowContribs, renamed<FlowDef>, paramSubstituted<FlowDef>, collapsed<FlowDef>, referencedNodes, hasMultipleReferences;
flowtype FlowDef = decorate {flowEnv, referenceEnv};

abstract production flowDef
top::FlowDef ::= id::String fe::FlowExpr
{
  propagate paramSubstituted, collapsed;
  top.pp = pp"${text(id)} = ${fe.pp};";
  top.flowContribs = [pair(id, fe)];
  top.renamed = flowDef(top.renameFn(id), fe.renamed);
  top.referencedNodes = fe.referencedNodes;
  top.hasMultipleReferences = length(tm:lookup(id, top.referenceEnv)) > 1;
}

nonterminal FlowExprs with flowEnv, renameFn, parameters, referenceEnv, pps, flowExprs, renamed<FlowExprs>, paramSubstituted<FlowExprs>, collapsed<FlowExprs>, referencedNodes;
flowtype FlowExprs = decorate {flowEnv, referenceEnv};

abstract production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  propagate renamed, paramSubstituted, collapsed;
  top.pps = h.pp :: t.pps;
  top.flowExprs = h :: t.flowExprs;
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
}

abstract production nilFlowExpr
top::FlowExprs ::= 
{
  propagate renamed, paramSubstituted, collapsed;
  top.pps = [];
  top.flowExprs = [];
  top.referencedNodes = [];
}

nonterminal FlowExpr with flowEnv, renameFn, parameters, referenceEnv, pp, renamed<FlowExpr>, paramSubstituted<FlowExpr>, collapsed<FlowExpr>, referencedNodes;
flowtype FlowExpr = decorate {flowEnv, referenceEnv};

abstract production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  propagate renamed, paramSubstituted, collapsed;
  top.pp = if b then pp"true" else pp"false";
  top.referencedNodes = [];
}

abstract production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  propagate renamed, collapsed;
  top.pp = brackets(text(toString(i)));
  top.paramSubstituted = head(drop(i, top.parameters));
  top.referencedNodes = [];
}

abstract production nodeFlowExpr
top::FlowExpr ::= id::String
{
  propagate paramSubstituted;
  top.pp = text(id);
  top.renamed = nodeFlowExpr(top.renameFn(id));
  top.collapsed =
    if length(tm:lookup(id, top.referenceEnv)) <= 1 then refNode.collapsed else nodeFlowExpr(id);
  top.referencedNodes = [id];
  
  production refNode::Decorated FlowExpr = head(tm:lookup(id, top.flowEnv));
}

abstract production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate renamed, paramSubstituted, collapsed;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate renamed, paramSubstituted, collapsed;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  propagate renamed, paramSubstituted, collapsed;
  top.pp = pp"(!${e.pp})";
  top.referencedNodes = e.referencedNodes;
}

-- Utility functions
function renameFlowGraph
FlowGraph ::= renameFn::(String ::= String) fg::FlowGraph
{
  fg.renameFn = renameFn;
  return fg.renamed;
}

function subParamsFlowGraph
FlowGraph ::= parameters::[FlowExpr] fg::FlowGraph
{
  fg.parameters = parameters;
  return fg.paramSubstituted;
}

function buildFlowGraph
FlowGraph ::= flowDefs::[FlowDef] flowExprs::[FlowExpr]
{
  return
    flowGraph(
      foldr(consFlowDef, nilFlowDef(), flowDefs),
      foldr(consFlowExpr, nilFlowExpr(), flowExprs));
}
