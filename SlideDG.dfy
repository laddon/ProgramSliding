include "PDG.dfy"
//include "ProofUtil.dfy"

// SlideDG Definitions:
type Slide = (Label, Variable)
type Edge = (Slide, Slide, set<Variable>)
type SlideDG = (Statement, set<Slide>, map<Slide, set<Slide>>) // map from node to it's predecssors

function method SlideLabel(s: Slide): Label
{
	s.0
}

function method SlideVariable(s: Slide): Variable
{
	s.1
}

function method SlideDGStatement(slideDG: SlideDG): Statement
{
	slideDG.0
}

function method SlideDGSlides(slideDG: SlideDG): set<Slide>
{
	slideDG.1
}

function method SlideDGMap(slideDG: SlideDG): map<Slide, set<Slide>>
{
	slideDG.2
}

predicate ExistsEdge(slide1: Slide, slide2: Slide, slideDG: SlideDG)
{
	slide2 in SlideDGMap(slideDG) && slide1 in SlideDGMap(slideDG)[slide2]
}

method ComputeSlideDG(S: Statement, labels: set<Label>) returns (slideDG: SlideDG) // labels should be all labels of S of Assignment, IF and DO (NOT SeqComp and Skip)
	requires Core(S)
	//ensures SlideDGOf(S, labels) == ComputeSlideDG(S, labels)
	//ensures IsSlideDGOf(slideDG, S)
{
	var N := ComputeSlideDGNodes(S, labels);
	var E := ComputeSlideDGEdges(S, N);
	var m : map<Slide, set<Slide>>; // TODO

	slideDG := (S, N, m);
}

predicate IsSlideDGOf(slideDG: SlideDG, S: Statement)
{
	SlideDGOf(S) == slideDG
}

lemma ExistsSlideDependence(slideDG: SlideDG, S: Statement, Sm: Slide, Sn: Slide)
	requires IsSlideDGOf(slideDG, S)
	requires Sm in SlideDGSlides(slideDG)
	requires Sn in SlideDGSlides(slideDG)
	//ensures exists e: Edge :: e in EdgesOf(slideDG) && e.0 == Sm && e.1 == Sn <==> SlideDependence(Sm, Sn, S)

function SlideDGOf(S: Statement): SlideDG
	requires Valid(S) && Core(S)
{
	var slides := slidesOf(S, def(S));
	var m := map s | s in slides :: SlideDependencePredecessorsOf(s, S);

	(S, slides, m)
}

function SlideDependencePredecessorsOf(Sn: Slide, S: Statement): set<Slide>
	requires Valid(S) && Core(S)
	requires Sn in slidesOf(S, def(S))
{
	set Sm | Sm in slidesOf(S, def(S)) && SlideDependence(Sm, Sn, S)
}

method {:verify false}ComputeSlideDGNodes(S: Statement, labels: set<Label>) returns (slides: set<Slide>)
	requires Core(S)
/*{
	slides := {};

	var tempLabels := labels;
	while (|tempLabels| > 0)
	{
		var l :| l in labels;
		tempLabels := tempLabels - {l};
		var subS := slipOf(S, l);
		match subS {
			case Assignment(LHS,RHS) =>
				var v: Variable;
				var slide := ComputeSlide(S, v /* LHS? */, l);
				slides := slides + {slide};
		}
	}
}*/

method ComputeSlideDGEdges(S: Statement, Slides: set<Slide>) returns (edges: set<Edge>)
	requires Core(S)
{
	edges := {};
	var copySlides := Slides;

	while (|copySlides| > 0)
	{
		var Sm :| Sm in copySlides;
		copySlides := copySlides - {Sm};		
		var slideDepSlides := ComputeSlideDependence(Slides, Sm);
		
		while (|slideDepSlides| > 0)
		{
			var slideDep :| slideDep in slideDepSlides;
			slideDepSlides := slideDepSlides - {slideDep};	
			var edge := (Sm, slideDep.0, slideDep.1);
			edges := edges + {edge};
		}
	}

	// for each slide 
	//		get all slide dependence slides from Slides
	//		for each slide dependence create and label the edges
}

method ComputeSlideDependence(Slides: set<Slide>, Sm: Slide) returns (slideDepSlides: set<(Slide, set<Variable>)>)

method ComputeSlide(S: Statement, v: Variable, l: Label) returns (n: Slide)

function slipOf(S: Statement, l: Label): Statement
	reads *
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
	ensures Valid(slipOf(S, l)) && Core(slipOf(S, l))
	ensures l == [] ==> slipOf(S, l) == S
	ensures l != [] ==> slipOf(S, l) < S
	decreases l
{
	if l == [] then S
	else
		match S {
			case Assignment(LHS,RHS) => Skip//assert false - Doesn't work!!!
			case SeqComp(S1,S2) =>		if l[0] == 1 then slipOf(S1, l[1..]) else slipOf(S2, l[1..])
			case IF(B0,Sthen,Selse) =>	if l[0] == 1 then slipOf(Sthen, l[1..]) else slipOf(Selse, l[1..])
			case DO(B,S1) =>			slipOf(S1, l[1..])
			case Skip =>				Skip//assert false - Doesn't work!!!
		}
}

function allSlidesOf(S: Statement) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	slidesOf(S, def(S))
}

predicate ValidLabel(l: Label, S: Statement)
	reads *
	requires Valid(S)
	requires Core(S)
{
	if l == [] then true
	else
	match S {
	case Skip =>				false
	case Assignment(LHS,RHS) =>	false
	case SeqComp(S1,S2) =>		if l[0] == 1 then ValidLabel(l[1..], S1) else ValidLabel(l[1..], S2)
	case IF(B0,Sthen,Selse) =>	if l[0] == 1 then ValidLabel(l[1..], Sthen) else ValidLabel(l[1..], Selse)
	case DO(B,Sloop) =>			if l[0] == 1 then ValidLabel(l[1..], Sloop) else false
	}
}

function {:verify false}slidesOf(S: Statement, V: set<Variable>) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
	ensures forall s :: s in slidesOf(S, V) ==> ValidLabel(SlideLabel(s), S) && !IsEmptyAssignment(slipOf(S, SlideLabel(s)))
{
	slidesOf'(S, V, [])
}

function {:verify false}slidesOf'(S: Statement, V: set<Variable>, l: Label): (slides: set<Slide>)
	reads *
	requires Valid(S)
	requires Core(S)
	ensures forall s :: s in slides ==> ValidLabel(SlideLabel(s), S) && !IsEmptyAssignment(slipOf(S, SlideLabel(s)))
{
	match S {
	case Skip => {}
	case Assignment(LHS,RHS) => set v | v in V * setOf(LHS) :: (l, v)
	case SeqComp(S1,S2) =>		slidesOf'(S1, V, l+[1]) + slidesOf'(S2, V, l+[2])
	case IF(B0,Sthen,Selse) =>	slidesOf'(Sthen, V, l+[1]) + slidesOf'(Selse, V, l+[2])
	case DO(B,Sloop) =>			slidesOf'(Sloop, V, l+[1])
	}
}

function SlideLabels(s: Slide, S: Statement): set<Label>
	requires Valid(S) && Core(S)
	requires s in slidesOf(S, def(S))
{
	set l | l == SlideLabel(s) ||
	(l < SlideLabel(s) && (IsDO(slipOf(S, l)) || IsIF(slipOf(S, l))))
}


datatype SlideDGPath = Empty | Extend(SlideDGPath, Slide)

predicate IsEmptySlideDGPath(path: SlideDGPath)
{
	match path
	case Empty => true
	case Extend(prefix, n) => false
}

predicate IsExtendSlideDGPath(path: SlideDGPath)
{
	match path
	case Empty => false
	case Extend(prefix, n) => true
}

function GetPrefixSlideDGPath(path: SlideDGPath): SlideDGPath
	requires IsExtendSlideDGPath(path)
{
	match path {
	case Extend(prefix, n) => prefix
	}
}

function GetNSlideDGPath(path: SlideDGPath): Slide
	requires IsExtendSlideDGPath(path)
{
	match path {
	case Extend(prefix, n) => n
	}
}

predicate SlideDGReachable(slideDG: SlideDG, from: Slide, to: Slide, S: set<Slide>)
	//requires null !in S
	//reads S
{
	exists via: SlideDGPath :: SlideDGReachableVia(slideDG, from, via, to, S)
}

predicate SlideDGReachableVia(slideDG: SlideDG, from: Slide, via: SlideDGPath, to: Slide, S: set<Slide>)
	//requires null !in S
	//reads S
	decreases via
{
	match via
	case Empty => from == to
	case Extend(prefix, n) => n in S && to in SlideDGNeighbours(slideDG, n) && SlideDGReachableVia(slideDG, from, prefix, n, S)
}

function SlideDGNeighbours(slideDG: SlideDG, n: Slide) : set<Slide>
	requires n in SlideDGMap(slideDG)
{
	SlideDGMap(slideDG)[n]
}


////////// Slide Dependence: ////////////

predicate SlideDependence(Sm: Slide, Sn: Slide, S: Statement)
	requires Valid(S) && Core(S)
	requires Sm in slidesOf(S, def(S)) && Sn in slidesOf(S, def(S))
{
	var v := SlideVariable(Sm);
	exists l :: l in SlideLabels(Sn, S) && 
	v in UsedVars(S, l) && ReachingDefinition(S, SlideLabel(Sm), l, v)
}

predicate ReachingDefinition(S: Statement, l1: Label, l2: Label, v: Variable)
	requires Valid(S) && Core(S)
	requires ValidLabel(l1, S) && ValidLabel(l2, S)
{
	(v, l1) in ReachingDefinitionsIn(S, l2)
}

function ReachingDefinitionsIn(S: Statement, l: Label): set<(Variable, Label)>
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
{
	var V := def(S);
	var rdIn: set<(Variable, Label)> := set v | v in V :: (v, []);
	ReachingDefinitionsInRec(S, rdIn, l)

	// ReachingDefinitionsInRec(S, {}, l) // instead of {} use (v,[]) for each variable in S
}

function ReachingDefinitionsInRec(S: Statement, rdIn: set<(Variable, Label)>, l: Label): set<(Variable, Label)>
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
{
	if l == [] then rdIn else
	assert !IsAssignment(S) && !IsSkip(S);
	match S {
		case SeqComp(S1,S2) =>
			if l[0] == 1 then ReachingDefinitionsInRec(S1, rdIn, l[1..])
			else ReachingDefinitionsInRec(S2, ReachingDefinitionsOut(S1, rdIn), l[1..])
		case IF(B0,Sthen,Selse) =>
			if l[0] == 1 then ReachingDefinitionsInRec(Sthen, rdIn, l[1..])
			else ReachingDefinitionsInRec(Selse, rdIn, l[1..])
		case DO(B,Sloop) =>
			ReachingDefinitionsInRec(Sloop, rdIn + ReachingDefinitionsOut(Sloop, rdIn), l[1..])
	}
}

function ReachingDefinitionsOut(S: Statement, rdIn: set<(Variable, Label)>): set<(Variable, Label)>
	requires Valid(S) && Core(S)
{
	ReachingDefinitionsOutRec(S, rdIn, [])
}

function ReachingDefinitionsOutRec(S: Statement, rdIn: set<(Variable, Label)>, l: Label): set<(Variable, Label)>
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
{
	match S {
		case Assignment(LHS,RHS) => RDKill(LHS, rdIn) + RDGen(LHS, l)
		case Skip => rdIn
		case SeqComp(S1,S2) => ReachingDefinitionsOutRec(S2, ReachingDefinitionsOutRec(S1, rdIn, l+[1]), l+[2])
		case IF(B0,Sthen,Selse) => ReachingDefinitionsOutRec(Sthen, rdIn, l+[1]) + ReachingDefinitionsOutRec(Selse, rdIn, l+[2])
		case DO(B,Sloop) => rdIn + ReachingDefinitionsOutRec(Sloop, {}, l+[1])
	}
}

function RDKill(V: seq<Variable>, rdIn: set<(Variable, Label)>): set<(Variable, Label)>
{
	if V == [] then rdIn
	else
		var s := set p | p in rdIn && V[0] == p.0;
		RDKill(V[1..], rdIn - s)
}

function RDGen(V: seq<Variable>, l: Label): set<(Variable, Label)>
{
	set v | v in V :: (v, l)
}

function ReachingDefinitionsInFor(S: Statement, l: Label, v: Variable): set<(Variable, Label)>
{
	var rdIn := ReachingDefinitionsIn(S, l);

	set p | p in rdIn && p.0 == v
}

//////////////   From CFG.dfy:   ////////////////

function UsedVars(S: Statement, l: Label): set<Variable>
	requires Valid(S) && Core(S)
	requires ValidLabel(l, S)
{
	var slipOfS := slipOf(S, l);

	match S {
	case Assignment(LHS,RHS) => set v | v in GetRHSVariables(RHS)
	case SeqComp(S1,S2) => {}
	case IF(B,Sthen,Selse) => set v | v in B.1
	case DO(B,S0) => set v | v in B.1
	case Skip => {}
	}
}

function DefinedVars(S: Statement, l: Label): set<Variable>