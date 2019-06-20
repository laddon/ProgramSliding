include "Definitions.dfy"
include "Util.dfy"
include "SlideDG.dfy"


// VarSlideDG Definitions:
datatype VarSlideTag = Phi | Regular
type VarSlide = (Variable, VarSlideTag)//, Label) // label removed
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

function method VarSlideLabels2(S': Statement, s: VarSlide): set<Label>
{
	VarSlideLabelsRec(S', s, [])
}

function method VarSlideLabelsRec(S': Statement, s: VarSlide, l: Label): set<Label>
{
	match S' {
	case Skip =>				{}
	case Assignment(LHS,RHS) =>	if VarSlideVariable(s) in setOf(LHS) then {l} else {}
	case SeqComp(S1,S2) =>		VarSlideLabelsRec(S1, s, [1] + l) + VarSlideLabelsRec(S2, s, [2] + l)	
	case IF(B0,Sthen,Selse) =>	VarSlideLabelsRec(Sthen, s, [1] + l) + VarSlideLabelsRec(Selse, s, [2] + l)	
	case DO(B,Sloop) =>			VarSlideLabelsRec(Sloop, s, [1] + l)	
	}
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
{
	varSlideDG == VarSlideDGOf(S)
}

function VarSlideDGOf(T: Statement): VarSlideDG /// T is in fact S' (SSA)
	requires Valid(T) && Core(T)
{
	var varSlides := varSlidesOf(T, def(T));
	var m := map s | s in varSlides :: VarSlideDependencePredecessorsOf(s, T);

	(T, varSlides, m)
}

function VarSlideDependencePredecessorsOf(Sn: VarSlide, T: Statement): set<VarSlide>
	requires Valid(T) && Core(T)
	requires Sn in varSlidesOf(T, def(T))
{
	set Sm | Sm in varSlidesOf(T, def(T)) && VarSlideDependence(Sm, Sn, T)
}

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

function varSlidesOf(S': Statement, V: set<Variable>): set<VarSlide>
	reads *
	requires Valid(S') && Core(S')
{
	//set s | s in slidesOf(S, V) :: VarSlideOf(S, S', s)

	match S'
	case Skip =>
		{}	
	case Assignment(LHS,RHS) =>
		set v | v in setOf(LHS) :: (v, Regular)
	case SeqComp(S1,S2) =>
		if IsDO(S2) then
			assert IsAssignment(S1);
			match S1
			case Assignment(LHS,RHS) => (set v | v in setOf(LHS) :: (v, Phi)) + varSlidesOf(S2, V)
		else
			varSlidesOf(S1, V) + varSlidesOf(S2, V)
	case IF(B0,Sthen,Selse) =>
		assert IsSeqComp(Sthen);
		match Sthen
		case SeqComp(S1,S2) =>
			assert IsAssignment(S2);
			match S2
			case Assignment(LHS,RHS) =>
				((set v | v in setOf(LHS) :: (v, Phi)) + varSlidesOf(S1, V) +
				assert IsSeqComp(Selse);
				match Selse
				case SeqComp(S1',S2') =>
					assert IsAssignment(S2');
					match S2'
					case Assignment(LHS',RHS') =>
						(set v | v in setOf(LHS') :: (v, Phi)) + varSlidesOf(S1', V))
	case DO(B,Sloop) =>	
		assert IsSeqComp(Sloop);
		match Sloop
		case SeqComp(S1,S2) =>
			assert IsAssignment(S2);
			match S2
			case Assignment(LHS,RHS) => (set v | v in setOf(LHS) :: (v, Phi)) + varSlidesOf(S1, V)
}


function {:verify false}VarLabelOfSlide(S: Statement, S': Statement, slide: Slide): Label
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
{
	VarLabelOf(S, S', SlideLabel(slide))
}

function {:verify false}VarSlideOf(S: Statement, S': Statement, slide: Slide): VarSlide
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
{
	var l := SlideLabel(slide);
	var varLabel := VarLabelOf(S, S', l);
	var i := InstanceOf(S', varLabel);
	(i, Regular)//, varLabel)
}

function VarLabelOf(S: Statement, S': Statement, l: Label): Label
	//requires S == RemoveEmptyAssignments(Rename(S', XLs, X))
	reads *
	requires Valid(S)
	requires Valid(S')
	requires Core(S)
	requires Core(S')
	requires ValidLabel(l, S)
	//ensures |VarLabelOf(S, S', l)| >= 1 && |VarLabelOf(S, S', l)| <= maxLabelSize(S')
	ensures ValidLabel(VarLabelOf(S, S', l), S')
{
	match S {
	case Skip =>				assume IsSkip(S');
								assert l == [];
								[]	
	case Assignment(LHS,RHS) =>	assume IsAssignment(S');
								assert l == [];
								[]
	case SeqComp(S1,S2) =>		if l == [] then [] else
								assume IsSeqComp(S');
								match S' {
								case SeqComp(S1',S2') => if l[0] == 1 then [1] + VarLabelOf(S1, S1', l[1..]) else [2] + VarLabelOf(S2, S2', l[1..])
								}	
	case IF(B0,Sthen,Selse) =>	if l == [] then [] else
								assume IsIF(S');
								match S' {							
								case IF(B0',Sthen',Selse') => if l[0] == 1 then [1,1] + VarLabelOf(Sthen, Sthen', l[1..]) else [2,1] + VarLabelOf(Selse, Selse', l[1..])
								}
	case DO(B,Sloop) =>			if l == [] then [2] else
								assume IsSeqComp(S');
								match S' {
								// S1' is the phi assignment and S2' is the DO
								// we should add another [2] in order to go to the loop
								case SeqComp(S1',S2') => assume IsDO(S2');
														 match S2' {
														 case DO(B',Sloop') => assume Valid(Sloop') && Core(Sloop'); [2,1,1] + VarLabelOf(Sloop, Sloop', l[1..])
														 }
								}
	}
}

function {:verify false}InstanceOf(S': Statement, varLabel: Label): Variable
/////////////////////////// Should add v: Variable to the function and return LHS' * vsSSA.getInstancesOf(v).
	reads *
	requires Valid(S')
	requires Core(S')
	//requires |varLabel| >= 1 && |varLabel| <= maxLabelSize(S')
{
	match S' {
	case Skip =>					""
	case Assignment(LHS',RHS') =>	assume |LHS'| >= 1; LHS'[0]
	case SeqComp(S1',S2') =>		if varLabel[0] == 1 then InstanceOf(S1', varLabel[1..]) else InstanceOf(S2', varLabel[1..])
	case IF(B0',Sthen',Selse') =>	""//if varLabel[0] == 1 then InstanceOf(Sthen', varLabel[1..]) else InstanceOf(Selse', varLabel[1..])
	case DO(B',Sloop') =>			""//InstanceOf(Sloop', varLabel[1..])
	}
}

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
	requires n in VarSlideDGMap(varSlideDG)
{
	VarSlideDGMap(varSlideDG)[n]
}


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

predicate VarSlideDependence(Sm: VarSlide, Sn: VarSlide, S: Statement) // S is S'
	reads *
	requires Valid(S) && Core(S)
{
	var v := VarSlideVariable(Sm);
	exists l :: l in VarSlideLabels(Sn, S) && 
	v in UsedVars(S, l)
}

function VarSlideLabels(s: VarSlide, S: Statement): set<Label>
	requires Valid(S) && Core(S)
	requires s in varSlidesOf(S, def(S))
{
	set l | l == VarSlideLabel(s) ||
	(l < VarSlideLabel(s) && (IsDO(slipOf(S, l)) || IsIF(slipOf(S, l))))
}