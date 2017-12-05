grammar edu:umn:ee5364project:exts:ableC:logic:abstractsyntax;

import core:monad;
import silver:util:raw:treemap as tm;

type ChannelId = String;

-- The environment on a nand flow graph mapping channel identifiers to channel items (inputs or gates)
synthesized attribute channelContribs::[Pair<ChannelId ChannelItem>];
autocopy attribute channelEnv::tm:Map<ChannelId ChannelItem>;

nonterminal ChannelItem with pp, channelIndex, criticalPathLength;

abstract production inputChannelItem
top::ChannelItem ::= i::Integer
{
  top.pp = pp"input ${text(toString(i))}";
  top.channelIndex = i;
  top.criticalPathLength = 0;
}

abstract production gateChannelItem
top::ChannelItem ::= g::Decorated NANDGate
{
  top.pp = pp"gate ${g.pp}";
  top.channelIndex = g.channelIndex;
  top.criticalPathLength = g.criticalPathLength;
}

inherited attribute numInputs::Integer;
--inherited attribute numOutputs::Integer;

-- Analyses perfomed on a NANDFlowGraph
synthesized attribute numGatesRequired::Integer;
synthesized attribute criticalPathLength::Integer;
synthesized attribute softHostInitTrans::Stmt;
synthesized attribute hardHostInitTrans::Stmt;

nonterminal NANDFlowGraph with numInputs, pp, numGatesRequired, criticalPathLength, softHostInitTrans, hardHostInitTrans;

abstract production nandFlowGraph
top::NANDFlowGraph ::= gateConfig::NANDGates outputChannels::OutputChannels
{
  top.pp = terminate(line(), gateConfig.pps ++ outputChannels.pps);
  top.numGatesRequired = gateConfig.numGatesRequired;
  top.criticalPathLength = outputChannels.criticalPathLength;
  top.softHostInitTrans = seqStmt(gateConfig.softHostInitTrans, outputChannels.softHostInitTrans);
  top.hardHostInitTrans = seqStmt(gateConfig.hardHostInitTrans, outputChannels.hardHostInitTrans);
  
  gateConfig.channelEnv =
    tm:add(
      map(
        \ i::Integer -> pair(inputChannelId(i), inputChannelItem(i)),
        range(0, top.numInputs)),
      tm:empty(compareString));
  outputChannels.channelEnv = tm:add(gateConfig.channelContribs, gateConfig.channelEnv);
  gateConfig.nextChannelIndex = top.numInputs;
}

inherited attribute nextChannelIndex::Integer;

nonterminal NANDGates with channelEnv, nextChannelIndex, pps, channelContribs, numGatesRequired, softHostInitTrans, hardHostInitTrans;

abstract production consNANDGate
top::NANDGates ::= h::NANDGate t::NANDGates
{
  top.pps = h.pp :: t.pps;
  top.channelContribs = h.channelContribs ++ t.channelContribs;
  top.numGatesRequired = 1 + t.numGatesRequired;
  top.softHostInitTrans = seqStmt(h.softHostInitTrans, t.softHostInitTrans);
  top.hardHostInitTrans = seqStmt(h.hardHostInitTrans, t.hardHostInitTrans);
  
  t.channelEnv = tm:add(h.channelContribs, top.channelEnv);
  h.nextChannelIndex = top.nextChannelIndex;
  t.nextChannelIndex = top.nextChannelIndex + 1;
}

abstract production nilNANDGate
top::NANDGates ::=
{
  top.pps = [];
  top.channelContribs = [];
  top.numGatesRequired = 0;
  top.softHostInitTrans = nullStmt();
  top.hardHostInitTrans = nullStmt();
}

synthesized attribute channelIndex::Integer;

nonterminal NANDGate with channelEnv, nextChannelIndex, pp, channelIndex, channelContribs, criticalPathLength, softHostInitTrans, hardHostInitTrans;

abstract production nandGate
top::NANDGate ::= channel::ChannelId input1::ChannelId input2::ChannelId
{
  top.pp = pp"${text(toString(channel))} = !(${text(toString(input1))} & ${text(toString(input2))});";
  top.channelIndex = top.nextChannelIndex;
  top.channelContribs = [pair(channel, gateChannelItem(top))];
  local input1Ref::ChannelItem = head(tm:lookup(input1, top.channelEnv));
  local input2Ref::ChannelItem = head(tm:lookup(input2, top.channelEnv));
  top.criticalPathLength = 1 + max(input1Ref.criticalPathLength, input2Ref.criticalPathLength);
  top.softHostInitTrans =
    exprStmt(
      directCallExpr(
        name("soft_gate_config", location=builtin),
        foldExpr(
          map(mkIntConst(_, builtin),
          [top.channelIndex, input1Ref.channelIndex, input2Ref.channelIndex])),
        location=builtin));
  top.hardHostInitTrans = parseStmt(s"""
asm("lgcg ${toString(top.channelIndex)},${toString(input1Ref.channelIndex)},${toString(input2Ref.channelIndex)}");
""");
}

nonterminal OutputChannels with channelEnv, pps, criticalPathLength, softHostInitTrans, hardHostInitTrans;

abstract production consOutputChannel
top::OutputChannels ::= h::OutputChannel t::OutputChannels
{
  top.pps = h.pp :: t.pps;
  top.criticalPathLength = max(h.criticalPathLength, t.criticalPathLength);
  top.softHostInitTrans = seqStmt(h.softHostInitTrans, t.softHostInitTrans);
  top.hardHostInitTrans = seqStmt(h.hardHostInitTrans, t.hardHostInitTrans);
}

abstract production nilOutputChannel
top::OutputChannels ::=
{
  top.pps = [];
  top.criticalPathLength = 0;
  top.softHostInitTrans = nullStmt();
  top.hardHostInitTrans = nullStmt();
}

nonterminal OutputChannel with channelEnv, pp, criticalPathLength, softHostInitTrans, hardHostInitTrans;

abstract production outputChannel
top::OutputChannel ::= output::Integer channel::ChannelId
{
  top.pp = pp"output ${text(toString(output))} = ${text(toString(channel))};";
  local channelRef::ChannelItem = head(tm:lookup(channel, top.channelEnv));
  top.criticalPathLength = channelRef.criticalPathLength;
  top.softHostInitTrans =
    exprStmt(
      directCallExpr(
        name("soft_output_config", location=builtin),
        foldExpr(map(mkIntConst(_, builtin), [output, channelRef.channelIndex])),
        location=builtin));
  top.hardHostInitTrans = parseStmt(s"""
asm("lgco ${toString(output)},${toString(channelRef.channelIndex)}");
""");
}

synthesized attribute nandFlowGraph::NANDFlowGraph occurs on FlowGraph;

-- The environment mapping flow graph node ids to channel identifers
synthesized attribute transChannelContribs::[Pair<String ChannelId>] occurs on FlowDefs, FlowDef;
autocopy attribute transChannelEnv::tm:Map<String ChannelId> occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

synthesized attribute transChannel::ChannelId occurs on FlowExpr;

synthesized attribute outputChannels::[OutputChannel] occurs on FlowExprs;

inherited attribute isNegated::Boolean occurs on FlowExpr;

-- An environment threaded through the flow graph, mapping existing gate inputs to their outputs
type ChannelAssignments = Pair<[NANDGate] tm:Map<ChannelId tm:Map<ChannelId ChannelId>>>; 
inherited attribute channelAssignmentsIn::ChannelAssignments occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;
synthesized attribute channelAssignmentsOut::ChannelAssignments occurs on FlowDefs, FlowDef, FlowExprs, FlowExpr;

aspect production flowGraph
top::FlowGraph ::= name::String flowDefs::FlowDefs flowExprs::FlowExprs
{
  flowDefs.channelAssignmentsIn = pair([], tm:empty(compareString));
  flowExprs.channelAssignmentsIn = flowDefs.channelAssignmentsOut;
  
  local gateConfig::[NANDGate] = reverse(flowExprs.channelAssignmentsOut.fst);
  local outputChannels::[OutputChannel] = flowExprs.outputChannels;
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
  top.outputChannels = outputChannel(top.position, h.transChannel) :: t.outputChannels;
  
  h.isNegated = false;
  
  h.channelAssignmentsIn = top.channelAssignmentsIn;
  t.channelAssignmentsIn = h.channelAssignmentsOut;
  top.channelAssignmentsOut = t.channelAssignmentsOut;
}

aspect production nilFlowExpr
top::FlowExprs ::= 
{
  top.outputChannels = [];
  
  top.channelAssignmentsOut = top.channelAssignmentsIn;
}

aspect production constantFlowExpr
top::FlowExpr ::= b::Boolean
{
  local baseChannelId::ChannelId = "input_0";
  local gate1::Pair<ChannelId ChannelAssignments> =
    gateChannelId(baseChannelId, baseChannelId, top.channelAssignmentsIn);
  local gate2::Pair<ChannelId ChannelAssignments> =
    gateChannelId(gate1.fst, baseChannelId, gate1.snd);
  local gate3::Pair<ChannelId ChannelAssignments> = gateChannelId(gate2.fst, gate2.fst, gate2.snd);
  top.transChannel = if b != top.isNegated then gate2.fst else gate3.fst;
  top.channelAssignmentsOut = if b != top.isNegated then gate2.snd else gate3.snd;
}

aspect production parameterFlowExpr
top::FlowExpr ::= i::Integer
{
  local paramChannelId::ChannelId = inputChannelId(i);
  local gate1::Pair<ChannelId ChannelAssignments> =
    gateChannelId(paramChannelId, paramChannelId, top.channelAssignmentsIn);
  top.transChannel = if top.isNegated then gate1.fst else paramChannelId;
  top.channelAssignmentsOut = if top.isNegated then gate1.snd else top.channelAssignmentsIn;
}

aspect production nodeFlowExpr
top::FlowExpr ::= id::String
{
  local refChannel::ChannelId = head(tm:lookup(id, top.transChannelEnv));
  local gate1::Pair<ChannelId ChannelAssignments> =
    gateChannelId(refChannel, refChannel, top.channelAssignmentsIn);
  top.transChannel = if top.isNegated then gate1.fst else refChannel;
  top.channelAssignmentsOut = if top.isNegated then gate1.snd else top.channelAssignmentsIn;
}

aspect production andFlowExpr
top::FlowExpr ::= e1::FlowExpr e2::FlowExpr
{
  e1.channelAssignmentsIn = top.channelAssignmentsIn;
  e2.channelAssignmentsIn = e1.channelAssignmentsOut;
  local gate1::Pair<ChannelId ChannelAssignments> =
    gateChannelId(e1.transChannel, e2.transChannel, e2.channelAssignmentsOut);
  local gate2::Pair<ChannelId ChannelAssignments> = gateChannelId(gate1.fst, gate1.fst, gate1.snd);
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
    gateChannelId(e1.transChannel, e2.transChannel, e2.channelAssignmentsOut);
  local gate2::Pair<ChannelId ChannelAssignments> = gateChannelId(gate1.fst, gate1.fst, gate1.snd);
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

function inputChannelId
ChannelId ::= i::Integer
{
  return s"input_${toString(i)}";
}

function gateChannelId
Pair<ChannelId ChannelAssignments> ::= input1::ChannelId input2::ChannelId cas::ChannelAssignments
{
  local key1::ChannelId = if input1 < input2 then input1 else input2;
  local key2::ChannelId = if input1 > input2 then input1 else input2;
  local nextChannel::ChannelId = s"gate_${toString(genInt())}";
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
                nandGate(nextChannel, input1, input2) :: cas.fst,
                tm:update(key1, [tm:add([pair(key2, nextChannel)], entry)], cas.snd)))
        end
    -- Case 3: A gate with the same key1 does not exist, create a new inner map with the new gate
    | [] ->
      pair(
        nextChannel,
        pair(
          nandGate(nextChannel, input1, input2) :: cas.fst,
          tm:add(
            [pair(key1, tm:add([pair(key2, nextChannel)], tm:empty(compareString)))],
            cas.snd)))
    end;
}
