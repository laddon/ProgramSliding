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

predicate VarSlideDGReachable(from: VarSlide, to: VarSlide, S: set<VarSlide>)
