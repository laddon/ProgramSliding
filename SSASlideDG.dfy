include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// SSASlideDG Definitions:
datatype SSASlideTag = Phi | Regular
type SSASlide = (SSASlideTag, CFGNode, Variable, set<CFGNode>)
type SSAEdge = (SSASlide, SSASlide, set<Variable>)
type SSASlideDG = (Statement, set<SSASlide>, map<SSASlide, set<SSASlide>>) // map from node to it's predecssors

method ComputeSSASlideDG(S: Statement, pdgN: set<PDGNode>, pdgE: set<PDGEdge>) returns (ssaSlideDG: SSASlideDG)
{
	var N := ComputeSSASlideDGNodes(S, pdgN);
	var E := ComputeSSASlideDGEdges(S, N);
	var m : map<SSASlide, set<SSASlide>>; // TODO

	//ssaSlideDG := (S, N, E, m);
}

method ComputeSSASlideDGNodes(S: Statement, pdgN: set<PDGNode>) returns (slides: set<SSASlide>)
{

}

method ComputeSSASlideDGEdges(S: Statement, Slides: set<SSASlide>) returns (edges: set<SSAEdge>)
{

}