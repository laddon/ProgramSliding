include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// VarSlideDG Definitions:
datatype VarSlideTag = Phi | Regular
type VarSlide = (Variable, VarSlideTag, Label)
type VarEdge = (VarSlide, VarSlide, set<Variable>)
type VarSlideDG = (Statement, set<VarSlide>, map<VarSlide, set<VarSlide>>) // map from node to it's predecssors

function method VarSlideVariable(s: VarSlide): Variable
{
	s.0
}

function method VarSlideTag(s: VarSlide): VarSlideTag
{
	s.1
}

function method VarSlideLabel(s: VarSlide): Label
{
	s.2
}

function method VarSlideDGStatement(varSlideDG: VarSlideDG): Statement
{
	varSlideDG.0
}

function method VarSlideDGVarSlides(varSlideDG: VarSlideDG): set<VarSlide>
{
	varSlideDG.1
}
function method VarSlideDGMap(varSlideDG: VarSlideDG): map<VarSlide, set<VarSlide>>
{
	varSlideDG.2
}

method ComputeVarSlideDG(S: Statement) returns (varSlideDG: VarSlideDG)
	ensures IsVarSlideDGOf(varSlideDG, S)

predicate IsVarSlideDGOf(varSlideDG: VarSlideDG, S: Statement)

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

predicate IsEmptyVarSlideDGPath(path: VarSlideDGPath)
{
	match path
	case Empty => true
	case Extend(prefix, n) => false
}

predicate IsExtendVarSlideDGPath(path: VarSlideDGPath)
{
	match path
	case Empty => false
	case Extend(prefix, n) => true
}

function GetPrefixVarSlideDGPath(path: VarSlideDGPath): VarSlideDGPath
	requires IsExtendVarSlideDGPath(path)
{
	match path {
	case Extend(prefix, n) => prefix
	}
}

function GetNVarSlideDGPath(path: VarSlideDGPath): VarSlide
	requires IsExtendVarSlideDGPath(path)
{
	match path {
	case Extend(prefix, n) => n
	}
}

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


////////// VarSlide Dependence: ////////////

predicate VarSlideDependence(m: VarSlide, n: VarSlide, S: Statement)
	reads *
	requires Valid(S) && Core(S)
{
	VarSlideVariable(m) in UsedVars(S, VarSlideLabel(n))
}