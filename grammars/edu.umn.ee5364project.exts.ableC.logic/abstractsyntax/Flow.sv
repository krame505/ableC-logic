grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute flowDefs::[FlowDef];
-- The flow computed for every bit of a logic expression
synthesized attribute flowExprs::[FlowExpr];

-- Used to build the flowEnv Map
synthesized attribute flowContribs::[Pair<String Decorated FlowExpr>];

-- The flow graph provided to each element of the graph as a Map
autocopy attribute flowEnv::tm:Map<String Decorated FlowExpr>;

-- Function application
synthesized attribute appliedFlowDefs::[FlowDef];
synthesized attribute appliedFlowExprs::[FlowExpr];

-- Functor and supporting attributes for function stitching
synthesized attribute applied<a>::a;
autocopy attribute callId::String; -- An identifier unique to each particular call
autocopy attribute arguments::[FlowExpr]; -- FlowExprs to substitute for all parameterFlowExprs
autocopy attribute renameFn::(String ::= String); -- Renaming function to apply on every node id in the graph

-- Graph simplification
autocopy attribute referenceEnv::tm:Map<String Unit>; -- Map that contains an entry for every time an id is referenced
synthesized attribute collapsed<a>::a; -- Collapse together nodes with only one reference, remove unused nodes
synthesized attribute referencedNodes::[String]; -- The list of nodes referenced in a logic expr or def
synthesized attribute canCollapse::Boolean; -- True if a def can be removed
synthesized attribute isSimple::Boolean; -- True if an expression may be duplicated without introducing extra logic

nonterminal FlowGraph with callId, arguments, pp, flowDefs, flowExprs, appliedFlowDefs, appliedFlowExprs, collapsed<FlowGraph>;
flowtype FlowGraph = decorate {};

abstract production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  propagate collapsed;
  top.pp =
    ppConcat([
      text(name), space(),
      braces(nestlines(2, ppConcat([terminate(line(), flowDefs.pps), pp"return ${ppImplode(pp", ", flowExprs.pps)};"])))]);
  top.flowDefs = flowDefs.flowDefs;
  top.flowExprs = flowExprs.flowExprs;

  flowDefs.flowEnv = tm:empty(compareString);
  flowExprs.flowEnv = tm:add(flowDefs.flowContribs, flowDefs.flowEnv);
  
  -- Function application
  top.appliedFlowDefs = flowDefs.appliedFlowDefs;
  top.appliedFlowExprs = flowExprs.appliedFlowExprs;
  flowDefs.renameFn = \ n::String -> s"${name}_${n}_${top.callId}";
  flowExprs.renameFn = flowDefs.renameFn;
  
  -- Graph simplification
  flowDefs.referenceEnv =
    tm:add(
      map(pair(_, unit()), flowDefs.referencedNodes ++ flowExprs.referencedNodes),
      tm:empty(compareString));
  flowExprs.referenceEnv = flowDefs.referenceEnv;
}

nonterminal FlowDefs with flowEnv, renameFn, arguments, referenceEnv, pps, flowDefs, flowContribs, appliedFlowDefs, collapsed<FlowDefs>, referencedNodes;
flowtype FlowDefs = decorate {flowEnv, referenceEnv};

abstract production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  top.pps = h.pp :: t.pps;
  top.flowDefs = h :: t.flowDefs;
  top.flowContribs = h.flowContribs ++ t.flowContribs;
  top.appliedFlowDefs = h.applied :: t.appliedFlowDefs;
  top.collapsed = if h.canCollapse then t.collapsed else consFlowDef(h.collapsed, t.collapsed);
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
  
  t.flowEnv = tm:add(h.flowContribs, top.flowEnv);
}

abstract production nilFlowDef
top::FlowDefs ::= 
{
  propagate collapsed;
  top.pps = [];
  top.flowDefs = [];
  top.flowContribs = [];
  top.appliedFlowDefs = [];
  top.referencedNodes = [];
}

nonterminal FlowDef with flowEnv, renameFn, arguments, referenceEnv, pp, flowContribs, applied<FlowDef>, collapsed<FlowDef>, referencedNodes, canCollapse;
flowtype FlowDef = decorate {flowEnv, referenceEnv};

abstract production flowDef
top::FlowDef ::= id::String fe::FlowExpr
{
  propagate collapsed;
  top.pp = pp"${text(id)} = ${fe.pp};";
  top.flowContribs = [pair(id, fe)];
  top.applied = flowDef(top.renameFn(id), fe.applied);
  top.referencedNodes = fe.referencedNodes;
  top.canCollapse = fe.isSimple || length(tm:lookup(id, top.referenceEnv)) <= 1;
}

nonterminal FlowExprs with flowEnv, renameFn, arguments, referenceEnv, pps, flowExprs, appliedFlowExprs, collapsed<FlowExprs>, referencedNodes;
flowtype FlowExprs = decorate {flowEnv, referenceEnv};

abstract production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  propagate collapsed;
  top.pps = h.pp :: t.pps;
  top.flowExprs = h :: t.flowExprs;
  top.appliedFlowExprs = h.applied :: t.appliedFlowExprs;
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
}

abstract production nilFlowExpr
top::FlowExprs ::= 
{
  propagate collapsed;
  top.pps = [];
  top.flowExprs = [];
  top.appliedFlowExprs = [];
  top.referencedNodes = [];
}

nonterminal FlowExpr with flowEnv, renameFn, arguments, referenceEnv, pp, applied<FlowExpr>, collapsed<FlowExpr>, referencedNodes, isSimple;
flowtype FlowExpr = decorate {flowEnv, referenceEnv};

aspect default production
top::FlowExpr ::=
{
  top.isSimple = false;
}

abstract production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  propagate applied, collapsed;
  top.pp = if b then pp"true" else pp"false";
  top.referencedNodes = [];
  top.isSimple = true;
}

-- Invariant: A given parameter is only referenced in a flow graph once
abstract production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  propagate collapsed;
  top.pp = brackets(text(toString(i)));
  top.applied = head(drop(i, top.arguments));
  top.referencedNodes = [];
  top.isSimple = false; -- NOT simple, since we don't know if what will be substituted in is simple
}

abstract production nodeFlowExpr
top::FlowExpr ::= id::String
{
  top.pp = text(id);
  top.applied = nodeFlowExpr(top.renameFn(id));
  
  production refNode::Decorated FlowExpr = head(tm:lookup(id, top.flowEnv));
  local canCollapse::Boolean = refNode.isSimple || length(tm:lookup(id, top.referenceEnv)) <= 1;
  top.collapsed = if canCollapse then refNode.collapsed else nodeFlowExpr(id);
  top.referencedNodes = [id];
  top.isSimple = if canCollapse then refNode.isSimple else true;
}

abstract production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate applied, collapsed;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate applied, collapsed;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  propagate applied, collapsed;
  top.pp = pp"(!${e.pp})";
  top.referencedNodes = e.referencedNodes;
}

-- Utility functions
function buildFlowGraph
FlowGraph ::= name::String flowDefs::[FlowDef] flowExprs::[FlowExpr]
{
  return
    flowGraph(
      name,
      foldr(consFlowDef, nilFlowDef(), flowDefs),
      foldr(consFlowExpr, nilFlowExpr(), flowExprs));
}
