grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import core:monad;
import silver:util:raw:treemap as tm;

type ChannelId = Integer;

synthesized attribute channelContribs::[Pair<ChannelId ChannelItem>];
autocopy attribute channelEnv::tm:Map<ChannelId ChannelItem>;

nonterminal ChannelItem with pp, criticalPathLength;

abstract production inputChannelItem
top::ChannelItem ::= i::ChannelId
{
  top.pp = pp"input ${text(toString(i))}";
  top.criticalPathLength = 0;
}

abstract production gateChannelItem
top::ChannelItem ::= g::Decorated NANDGate
{
  top.pp = pp"gate ${g.pp}";
  top.criticalPathLength = g.criticalPathLength;
}

synthesized attribute numGatesRequired::Integer;
synthesized attribute criticalPathLength::Integer;
synthesized attribute softHostInitTrans::Stmt;

nonterminal NANDFlowGraph with numInputs, pp, numGatesRequired, criticalPathLength, softHostInitTrans;

abstract production nandFlowGraph
top::NANDFlowGraph ::= gateConfig::NANDGates outputChannels::OutputChannels
{
  top.pp = terminate(line(), gateConfig.pps ++ outputChannels.pps);
  top.numGatesRequired = gateConfig.numGatesRequired;
  top.criticalPathLength = outputChannels.criticalPathLength;
  top.softHostInitTrans = seqStmt(gateConfig.softHostInitTrans, outputChannels.softHostInitTrans);
  
  gateConfig.channelEnv =
    tm:add(
      zipWith(pair, range(0, top.numInputs), map(inputChannelItem, range(0, top.numInputs))) ++
      gateConfig.channelContribs,
      tm:empty(compareInteger));
  outputChannels.channelEnv = gateConfig.channelEnv;
}

nonterminal NANDGates with channelEnv, pps, channelContribs, numGatesRequired, softHostInitTrans;

abstract production consNANDGate
top::NANDGates ::= h::NANDGate t::NANDGates
{
  top.pps = h.pp :: t.pps;
  top.channelContribs = h.channelContribs ++ t.channelContribs;
  top.numGatesRequired = 1 + t.numGatesRequired;
  top.softHostInitTrans = seqStmt(h.softHostInitTrans, t.softHostInitTrans);
}

abstract production nilNANDGate
top::NANDGates ::=
{
  top.pps = [];
  top.channelContribs = [];
  top.numGatesRequired = 0;
  top.softHostInitTrans = nullStmt();
}

nonterminal NANDGate with channelEnv, pp, channelContribs, criticalPathLength, softHostInitTrans;

abstract production nandGate
top::NANDGate ::= channel::ChannelId input1::ChannelId input2::ChannelId
{
  top.pp = pp"${text(toString(channel))} = !(${text(toString(input1))} & ${text(toString(input2))});";
  top.channelContribs = [pair(channel, gateChannelItem(top))];
  local input1Ref::ChannelItem = head(tm:lookup(input1, top.channelEnv));
  local input2Ref::ChannelItem = head(tm:lookup(input2, top.channelEnv));
  top.criticalPathLength = 1 + max(input1Ref.criticalPathLength, input2Ref.criticalPathLength);
  top.softHostInitTrans =
    exprStmt(
      directCallExpr(
        name("soft_gate_config", location=builtin),
        foldExpr(map(mkIntConst(_, builtin), [channel, input1, input2])),
        location=builtin));
}

nonterminal OutputChannels with channelEnv, pps, criticalPathLength, softHostInitTrans;

abstract production consOutputChannel
top::OutputChannels ::= h::OutputChannel t::OutputChannels
{
  top.pps = h.pp :: t.pps;
  top.criticalPathLength = max(h.criticalPathLength, t.criticalPathLength);
  top.softHostInitTrans = seqStmt(h.softHostInitTrans, t.softHostInitTrans);
}

abstract production nilOutputChannel
top::OutputChannels ::=
{
  top.pps = [];
  top.criticalPathLength = 0;
  top.softHostInitTrans = nullStmt();
}

nonterminal OutputChannel with channelEnv, pp, criticalPathLength, softHostInitTrans;

abstract production outputChannel
top::OutputChannel ::= output::ChannelId channel::ChannelId
{
  top.pp = pp"output ${text(toString(output))} = ${text(toString(channel))};";
  local channelRef::ChannelItem = head(tm:lookup(channel, top.channelEnv));
  top.criticalPathLength = channelRef.criticalPathLength;
  top.softHostInitTrans =
    exprStmt(
      directCallExpr(
        name("soft_output_config", location=builtin),
        foldExpr(map(mkIntConst(_, builtin), [output, channel])),
        location=builtin));
}

inherited attribute numInputs::Integer occurs on FlowGraph;
inherited attribute numOutputs::Integer occurs on FlowGraph;
synthesized attribute nandFlowGraph::NANDFlowGraph occurs on FlowGraph;

synthesized attribute transChannelContribs::[Pair<String ChannelId>] occurs on FlowDefs, FlowDef;
autocopy attribute transChannelEnv::tm:Map<String ChannelId> occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

synthesized attribute transChannel::ChannelId occurs on FlowExpr;
synthesized attribute transChannels::[ChannelId] occurs on FlowExprs;

inherited attribute isNegated::Boolean occurs on FlowExpr;

type ChannelAssignments = Pair<ChannelId tm:Map<ChannelId tm:Map<ChannelId ChannelId>>>; 
inherited attribute channelAssignmentsIn::ChannelAssignments occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;
synthesized attribute channelAssignmentsOut::ChannelAssignments occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

aspect production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  flowDefs.channelAssignmentsIn = pair(top.numInputs, tm:empty(compareInteger));
  flowExprs.channelAssignmentsIn = flowDefs.channelAssignmentsOut;
  
  local gateConfig::[NANDGate] =
    do (bindList, returnList) {
      entry1::Pair<ChannelId tm:Map<ChannelId ChannelId>> <-
        tm:toList(flowExprs.channelAssignmentsOut.snd);
      entry2::Pair<ChannelId ChannelId> <- tm:toList(entry1.snd);
      return nandGate(entry2.snd, entry1.fst, entry2.fst);
    };
  local outputChannels::[OutputChannel] =
    zipWith(outputChannel, range(0, top.numOutputs), flowExprs.transChannels);
  top.nandFlowGraph =
    nandFlowGraph(
      foldr(consNANDGate, nilNANDGate(), gateConfig),
      foldr(consOutputChannel, nilOutputChannel(), outputChannels));
  
  flowDefs.transChannelEnv = tm:empty(compareString);
  flowExprs.transChannelEnv = tm:add(flowDefs.transChannelContribs, flowDefs.transChannelEnv);
}

aspect production consFlowDef
top::FlowDefs ::= h::FlowDef t::FlowDefs
{
  top.transChannelContribs = h.transChannelContribs ++ t.transChannelContribs;
  t.transChannelEnv = tm:add(h.transChannelContribs, top.transChannelEnv);
  
  h.channelAssignmentsIn = top.channelAssignmentsIn;
  t.channelAssignmentsIn = h.channelAssignmentsOut;
  top.channelAssignmentsOut = t.channelAssignmentsOut;
}

aspect production nilFlowDef
top::FlowDefs ::= 
{
  top.transChannelContribs = [];
  
  top.channelAssignmentsOut = top.channelAssignmentsIn;
}

aspect production flowDef
top::FlowDef ::= id::String e::FlowExpr
{
  top.transChannelContribs = [pair(id, e.transChannel)];
  
  e.isNegated = false;
  
  e.channelAssignmentsIn = top.channelAssignmentsIn;
  top.channelAssignmentsOut = e.channelAssignmentsOut;
}

aspect production consFlowExpr
top::FlowExprs ::= h::FlowExpr t::FlowExprs
{
  top.transChannels = h.transChannel :: t.transChannels;
  
  h.isNegated = false;
  
  h.channelAssignmentsIn = top.channelAssignmentsIn;
  t.channelAssignmentsIn = h.channelAssignmentsOut;
  top.channelAssignmentsOut = t.channelAssignmentsOut;
}

aspect production nilFlowExpr
top::FlowExprs ::= 
{
  top.transChannels = [];
  
  top.channelAssignmentsOut = top.channelAssignmentsIn;
}

aspect production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  local gate1::Pair<ChannelId ChannelAssignments> = addGate(0, 0, top.channelAssignmentsIn);
  local gate2::Pair<ChannelId ChannelAssignments> = addGate(gate1.fst, 0, gate1.snd);
  local gate3::Pair<ChannelId ChannelAssignments> = addGate(gate2.fst, gate2.fst, gate2.snd);
  top.transChannel = if b != top.isNegated then gate2.fst else gate3.fst;
  top.channelAssignmentsOut = if b != top.isNegated then gate2.snd else gate3.snd;
}

aspect production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  local gate1::Pair<ChannelId ChannelAssignments> = addGate(i, i, top.channelAssignmentsIn);
  top.transChannel = if top.isNegated then gate1.fst else i;
  top.channelAssignmentsOut = if top.isNegated then gate1.snd else top.channelAssignmentsIn;
}

aspect production nodeFlowExpr
top::FlowExpr ::= id::String
{
  local refChannel::ChannelId = head(tm:lookup(id, top.transChannelEnv));
  local gate1::Pair<ChannelId ChannelAssignments> =
    addGate(refChannel, refChannel, top.channelAssignmentsIn);
  top.transChannel = if top.isNegated then gate1.fst else refChannel;
  top.channelAssignmentsOut = if top.isNegated then gate1.snd else top.channelAssignmentsIn;
}

aspect production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  e1.channelAssignmentsIn = top.channelAssignmentsIn;
  e2.channelAssignmentsIn = e1.channelAssignmentsOut;
  local gate1::Pair<ChannelId ChannelAssignments> =
    addGate(e1.transChannel, e2.transChannel, e2.channelAssignmentsOut);
  local gate2::Pair<ChannelId ChannelAssignments> = addGate(gate1.fst, gate1.fst, gate1.snd);
  top.transChannel = if top.isNegated then gate1.fst else gate2.fst;
  top.channelAssignmentsOut = if top.isNegated then gate1.snd else gate2.snd;
  
  e1.isNegated = false;
  e2.isNegated = false;
}

aspect production orFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  e1.channelAssignmentsIn = top.channelAssignmentsIn;
  e2.channelAssignmentsIn = e1.channelAssignmentsOut;
  local gate1::Pair<ChannelId ChannelAssignments> =
    addGate(e1.transChannel, e2.transChannel, e2.channelAssignmentsOut);
  local gate2::Pair<ChannelId ChannelAssignments> = addGate(gate1.fst, gate1.fst, gate1.snd);
  top.transChannel = if top.isNegated then gate2.fst else gate1.fst;
  top.channelAssignmentsOut = if top.isNegated then gate2.snd else gate1.snd;
  
  e1.isNegated = true;
  e2.isNegated = true;
}

aspect production notFlowExpr
top::FlowExpr ::= e::FlowExpr
{
  e.channelAssignmentsIn = top.channelAssignmentsIn;
  top.transChannel = e.transChannel;
  top.channelAssignmentsOut = e.channelAssignmentsOut;
  
  e.isNegated = !top.isNegated;
}

function addGate
Pair<ChannelId ChannelAssignments> ::= input1::ChannelId input2::ChannelId cas::ChannelAssignments
{
  local key1::ChannelId = if input1 < input2 then input1 else input2;
  local key2::ChannelId = if input1 > input2 then input1 else input2;
  local nextChannel::ChannelId = cas.fst;
  return
    case tm:lookup(key1, cas.snd) of
      [entry] ->
        case tm:lookup(key2, entry) of
        -- Case 1: That gate already exists, return its output channel
          [output] -> pair(output, cas)
        -- Case 2: A gate with the same key1 already exists, create the gate and add it to the inner map
        | [] ->
          pair(
            nextChannel,
            pair(
              nextChannel + 1,
              tm:update(key1, [tm:add([pair(key2, nextChannel)], entry)], cas.snd)))
        end
    -- Case 3: A gate with the same key1 does not exist, create a new inner map with the new gate
    | [] ->
      pair(
        nextChannel,
        pair(
          nextChannel + 1,
          tm:add([pair(key1, tm:add([pair(key2, nextChannel)], tm:empty(compareInteger)))], cas.snd)))
    end;
}

-- TODO: Move to core?
function compareInteger
Integer ::= l::Integer  r::Integer
{
  return if l <= r then if l == r then 0 else -1 else 1;
}
