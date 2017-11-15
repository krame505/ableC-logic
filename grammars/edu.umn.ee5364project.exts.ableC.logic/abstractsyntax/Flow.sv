grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import silver:util:raw:treemap as tm;

-- The flow computed for every named bit, used to build the overall flow graph
synthesized attribute flowDefs::[FlowDef];
-- The flow computed for every bit of a logic expression
synthesized attribute flowExprs::[FlowExpr];

-- Used to build the flowEnv Map
synthesized attribute flowContribs::[Pair<String Decorated FlowDef>];

-- The flow graph provided to each element of the graph as a Map
autocopy attribute flowEnv::tm:Map<String Decorated FlowDef>;

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
synthesized attribute simplified<a>::a; -- Collapse together nodes with only one reference, remove unused nodes
synthesized attribute canCollapse::Boolean; -- True if a def can be removed
synthesized attribute isSimple::Boolean; -- True if an expression may be duplicated without introducing extra logic
synthesized attribute referencedNodes::[String]; -- The list of nodes referenced in a logic expr or def

nonterminal FlowGraph with callId, arguments, pp, flowDefs, flowExprs, appliedFlowDefs, appliedFlowExprs, simplified<FlowGraph>;
flowtype FlowGraph = decorate {};

abstract production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  propagate simplified;
  top.pp =
    ppConcat([
      text(name), space(),
      braces(nestlines(2, ppConcat([terminate(line(), flowDefs.pps), pp"return ${ppImplode(pp", ", flowExprs.pps)};"])))]);
  top.flowDefs = flowDefs.flowDefs;
  top.flowExprs = flowExprs.flowExprs;
  
  flowExprs.position = 0;

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

nonterminal FlowDefs with flowEnv, renameFn, arguments, referenceEnv, pps, flowDefs, flowContribs, appliedFlowDefs, simplified<FlowDefs>, referencedNodes;
flowtype FlowDefs = decorate {flowEnv, referenceEnv};

abstract production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  top.pps = h.pp :: t.pps;
  top.flowDefs = h :: t.flowDefs;
  top.flowContribs = h.flowContribs ++ t.flowContribs;
  top.appliedFlowDefs = h.applied :: t.appliedFlowDefs;
  top.simplified = if h.canCollapse then t.simplified else consFlowDef(h.simplified, t.simplified);
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
  
  t.flowEnv = tm:add(h.flowContribs, top.flowEnv);
}

abstract production nilFlowDef
top::FlowDefs ::= 
{
  propagate simplified;
  top.pps = [];
  top.flowDefs = [];
  top.flowContribs = [];
  top.appliedFlowDefs = [];
  top.referencedNodes = [];
}

synthesized attribute simplifiedFlowExpr::FlowExpr;

nonterminal FlowDef with flowEnv, renameFn, arguments, referenceEnv, pp, flowContribs, applied<FlowDef>, simplified<FlowDef>, simplifiedFlowExpr, canCollapse, referencedNodes;
flowtype FlowDef = decorate {flowEnv, referenceEnv};

abstract production flowDef
top::FlowDef ::= id::String e::FlowExpr
{
  propagate simplified;
  top.pp = pp"${text(id)} = ${e.pp};";
  top.flowContribs = [pair(id, top)];
  top.applied = flowDef(top.renameFn(id), e.applied);
  top.simplifiedFlowExpr = e.simplified;
  top.canCollapse = e.simplified.isSimple || length(tm:lookup(id, e.referenceEnv)) <= 1;
  top.referencedNodes = e.referencedNodes;
}

inherited attribute position::Integer; -- Initially 0

nonterminal FlowExprs with position, flowEnv, renameFn, arguments, referenceEnv, pps, flowExprs, appliedFlowExprs, simplified<FlowExprs>, referencedNodes;
flowtype FlowExprs = decorate {position, flowEnv, referenceEnv};

abstract production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  propagate simplified;
  top.pps = h.pp :: t.pps;
  top.flowExprs = h :: t.flowExprs;
  top.appliedFlowExprs = h.applied :: t.appliedFlowExprs;
  top.referencedNodes = h.referencedNodes ++ t.referencedNodes;
  
  t.position = top.position + 1;
}

abstract production nilFlowExpr
top::FlowExprs ::= 
{
  propagate simplified;
  top.pps = [];
  top.flowExprs = [];
  top.appliedFlowExprs = [];
  top.referencedNodes = [];
}

nonterminal FlowExpr with flowEnv, renameFn, arguments, referenceEnv, pp, applied<FlowExpr>, simplified<FlowExpr>, referencedNodes, isSimple;
flowtype FlowExpr = decorate {flowEnv, referenceEnv};

aspect default production
top::FlowExpr ::=
{
  top.isSimple = false;
}

abstract production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  propagate applied, simplified;
  top.pp = if b then pp"true" else pp"false";
  top.referencedNodes = [];
  top.isSimple = true;
}

-- Invariant: A given parameter is only referenced in a flow graph at most once
abstract production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  propagate simplified;
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
  
  production refNode::Decorated FlowDef = head(tm:lookup(id, top.flowEnv));
  top.simplified = if refNode.canCollapse then refNode.simplifiedFlowExpr else nodeFlowExpr(id);
  top.referencedNodes = [id];
  top.isSimple = true;
}

abstract production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate applied;
  top.pp = pp"(${e1.pp} & ${e2.pp})";
  top.simplified =
    case e1.simplified, e2.simplified of
      constantFlowExpr(false), _ -> constantFlowExpr(false)
    | _, constantFlowExpr(false) -> constantFlowExpr(false)
    | constantFlowExpr(true), s -> s
    | s, constantFlowExpr(true) -> s
    | notFlowExpr(s1), notFlowExpr(s2) -> notFlowExpr(orFlowExpr(s1, s2))
    | s1, s2 -> andFlowExpr(s1, s2)
    end;
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  propagate applied;
  top.pp = pp"(${e1.pp} | ${e2.pp})";
  top.simplified =
    case e1.simplified, e2.simplified of
      constantFlowExpr(false), s -> s
    | s, constantFlowExpr(false) -> s
    | constantFlowExpr(true), _ -> constantFlowExpr(true)
    | _, constantFlowExpr(true) -> constantFlowExpr(true)
    | notFlowExpr(s1), notFlowExpr(s2) -> notFlowExpr(andFlowExpr(s1, s2))
    | s1, s2 -> orFlowExpr(s1, s2)
    end;
  top.referencedNodes = e1.referencedNodes ++ e2.referencedNodes;
}

abstract production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  propagate applied;
  top.pp = pp"(!${e.pp})";
  top.simplified =
    case e.simplified of 
      constantFlowExpr(b) -> constantFlowExpr(!b)
    | notFlowExpr(s) -> s
    | s -> notFlowExpr(s)
    end;
  top.referencedNodes = e.referencedNodes;
}

-- Flow constructor functions
function makeNegateFlowExprs
Pair<[FlowDef] [FlowExpr]> ::= logicFunctionEnv::Scopes<LogicFunctionItem> fes::[FlowExpr]
{
  return
    makeAddFlowExprs(
      logicFunctionEnv,
      map(notFlowExpr, fes),
      map(constantFlowExpr, repeat(false, length(fes) - 1) ++ [true]));
}

function makeAddFlowExprs
Pair<[FlowDef] [FlowExpr]> ::= logicFunctionEnv::Scopes<LogicFunctionItem> lhs::[FlowExpr] rhs::[FlowExpr]
{
  local halfAddFlowGraph::FlowGraph = head(lookupScope("halfAdd", logicFunctionEnv)).flowGraph;
  local fullAddFlowGraph::FlowGraph = head(lookupScope("fullAdd", logicFunctionEnv)).flowGraph;
  local buildAdder::(Pair<[FlowDef] [FlowExpr]> ::= [FlowExpr] [FlowExpr]) =
    \ lhs::[FlowExpr] rhs::[FlowExpr] ->
      case lhs, rhs of
        h1 :: t1, h2 :: t2 ->
          let rest::Pair<[FlowDef] [FlowExpr]> = buildAdder(t1, t2)
          in let applyRes::Pair<[FlowDef] [FlowExpr]> = applyFlowGraph(fullAddFlowGraph, [h1, h2, head(rest.snd)])
             in pair(rest.fst ++ applyRes.fst, applyRes.snd ++ tail(rest.snd))
             end
          end
      | [h1], [h2] -> applyFlowGraph(halfAddFlowGraph, [h1, h2])
      | _, _ -> error(s"Invalid adder inputs ${hackUnparse(lhs)} and ${hackUnparse(rhs)}")
      end;
  local adder::Pair<[FlowDef] [FlowExpr]> = buildAdder(lhs, rhs);
  return pair(adder.fst, tail(adder.snd)); -- Throw away the carry bit so output is the same width
}

function makeSubFlowExprs
Pair<[FlowDef] [FlowExpr]> ::= logicFunctionEnv::Scopes<LogicFunctionItem> lhs::[FlowExpr] rhs::[FlowExpr]
{
  local negateResult::Pair<[FlowDef] [FlowExpr]> = makeNegateFlowExprs(logicFunctionEnv, rhs);
  local addResult::Pair<[FlowDef] [FlowExpr]> = makeAddFlowExprs(logicFunctionEnv, lhs, negateResult.snd);
  return pair(negateResult.fst ++ addResult.fst, addResult.snd);
}

-- Utility functions
-- Construct a flow graph from lists of flow defs and flow exprs
function makeFlowGraph
FlowGraph ::= name::String flowDefs::[FlowDef] flowExprs::[FlowExpr]
{
  return
    flowGraph(
      name,
      foldr(consFlowDef, nilFlowDef(), flowDefs),
      foldr(consFlowExpr, nilFlowExpr(), flowExprs));
}

-- Get the lists of flow defs and flow exprs from applying a flow graph to input arguments
function applyFlowGraph
Pair<[FlowDef] [FlowExpr]> ::= flowGraph::FlowGraph arguments::[FlowExpr]
{
  flowGraph.callId = toString(genInt());
  flowGraph.arguments = arguments;
  return pair(flowGraph.appliedFlowDefs, flowGraph.appliedFlowExprs);
}

