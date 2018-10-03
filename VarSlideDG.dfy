include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// VarSlideDG Definitions:
datatype VarSlideTag = Phi | Regular
type VarSlide = (Variable, VarSlideTag)
type VarEdge = (VarSlide, VarSlide, set<Variable>)
type VarSlideDG = (Statement, set<VarSlide>, map<VarSlide, set<VarSlide>>) // map from node to it's predecssors

method ComputeVarSlideDG(S: Statement) returns (varSlideDG: VarSlideDG)
	ensures VarSlideDGOf(varSlideDG, S)

predicate VarSlideDGOf(varSlideDG: VarSlideDG, S: Statement)

/*
method ComputeVarSlideDG(S: Statement, pdgN: set<PDGNode>, pdgE: set<PDGEdge>) returns (varSlideDG: VarSlideDG)
{
	var N := ComputeVarSlideDGNodes(S, pdgN);
	var E := ComputeVarSlideDGEdges(S, N);
	var m : map<VarSlide, set<VarSlide>>; // TODO

	//varSlideDG := (S, N, E, m);
}

method ComputeVarSlideDGNodes(S: Statement, pdgN: set<PDGNode>) returns (slides: set<VarSlide>)
{

}

method ComputeVarSlideDGEdges(S: Statement, Slides: set<SSASlide>) returns (edges: set<VarEdge>)
{

}*/

function varSlidesOf(S: Statement, V: set<Variable>) : set<VarSlide>

datatype VarSlideDGPath = Empty | Extend(VarSlideDGPath, VarSlide)

predicate VarSlideDGReachable(varSlideDG: VarSlideDG, from: VarSlide, to: VarSlide, S: set<VarSlide>)
	//requires null !in S
	//reads S
{
	exists via: VarSlideDGPath :: VarSlideDGReachableVia(varSlideDG, from, via, to, S)
}

predicate VarSlideDGReachableVia(varSlideDG: VarSlideDG, from: VarSlide, via: VarSlideDGPath, to: VarSlide, S: set<VarSlide>)
	//requires null !in S
	//reads S
	decreases via
{
	match via
	case Empty => from == to
	case Extend(prefix, n) => n in S && to in VarSlideDGNeighbours(varSlideDG, n) && VarSlideDGReachableVia(varSlideDG, from, prefix, n, S)
}

function VarSlideDGNeighbours(varSlideDG: VarSlideDG, n: VarSlide) : set<VarSlide>

predicate VarSlideDGReachablePhi(varSlideDG: VarSlideDG, from: VarSlide, to: VarSlide, S: set<VarSlide>)
	//requires null !in S
	//reads S
{
	exists via: VarSlideDGPath :: VarSlideDGReachableViaPhi(varSlideDG, from, via, to, S)
}

predicate VarSlideDGReachableViaPhi(varSlideDG: VarSlideDG, from: VarSlide, via: VarSlideDGPath, to: VarSlide, S: set<VarSlide>)
	//requires null !in S
	//reads S
	decreases via
{
	match via
	case Empty => from == to
	case Extend(prefix, n) => n in S && to in VarSlideDGNeighbours(varSlideDG, n) && n.1 == Phi && VarSlideDGReachableVia(varSlideDG, from, prefix, n, S)
}