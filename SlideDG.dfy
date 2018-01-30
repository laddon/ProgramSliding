include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// SlideDG Definitions:
type Slide = (PDGNode, Variable, set<PDGNode>)
type Edge = (Slide, Slide, set<Variable>)
type SlideDG = (Statement, set<Slide>, map<Slide, set<Slide>>) // map from node to it's predecssors

method ComputeSlideDG(S: Statement, pdgN: set<PDGNode>, pdgE: set<PDGEdge>) returns (slideDG: SlideDG)
{
	var N := ComputeSlideDGNodes(S, pdgN);
	var E := ComputeSlideDGEdges(S, N);
	var m : map<Slide, set<Slide>>; // TODO

	//slideDG := (S, N, E, m);
}

method ComputeSlideDGNodes(S: Statement, pdgN: set<PDGNode>) returns (slides: set<Slide>)
{
	slides := {};
	var copyPDGN := pdgN;

	while (|copyPDGN| > 0)
	{
		var pdgNode :| pdgNode in copyPDGN;
		copyPDGN := copyPDGN - {pdgNode};
		match pdgNode {
			case Entry =>
			case Node(l) => 
				var subS := FindSubstatement(S, l);
				match subS {
					case Assignment(LHS,RHS) =>
						var v: Variable;
						var slide := ComputeSlide(S, v /* LHS? */, l);
						slides := slides + {slide};
				}
		}
	}
}

method ComputeSlideDGEdges(S: Statement, Slides: set<Slide>) returns (edges: set<Edge>)
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



/*
/*function FlowInsensitiveSlice(S: Statement, V: set<Variable>): Statement
	// FIXME: generalize
	requires S == Assignment(["i","sum", "prod"],["i+1","sum+i","prod*i"])
{
	if V == {"sum"} then Assignment(["sum"],["sum+i"])
	else Assignment(["i","prod"],["i+1","prod*i"])
}*/

function method GetAssignmentsOfV(LHS : seq<Variable>, RHS : seq<Expression>, V: set<Variable>) : Statement

{
	if LHS == [] then Skip
	else if LHS[0] in V then 
	var tempRes := GetAssignmentsOfV(LHS[1..], RHS[1..], V);
	match tempRes {
		case Assignment(LHS1,RHS1) => Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1)
	}
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)

	/*if LHS == [] then Skip
	else if LHS[0] in V then SeqComp(Assignment([LHS[0]],[RHS[0]]), GetAssignmentsOfV(LHS[1..], RHS[1..], V))
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)*/
}

function method ComputeSlides(S: Statement, V: set<Variable>) : Statement

{
	if V * def(S) == {} then Skip
	else
	match S {
		case Skip => Skip
		case Assignment(LHS,RHS) => GetAssignmentsOfV(LHS,RHS,V)
		case SeqComp(S1,S2) => SeqComp(ComputeSlides(S1,V), ComputeSlides(S2,V))
		case IF(B0,Sthen,Selse) => IF(B0, ComputeSlides(Sthen,V) , ComputeSlides(Selse,V))
		case DO(B,S) => DO(B, ComputeSlides(S,V))
	}
}

function method ComputeSlidesDepRtc(S: Statement, V: set<Variable>) : set<Variable>

{
	var slidesSV := ComputeSlides(S, V);
	var U := glob(slidesSV) * def(S);

	if U <= V then V else ComputeSlidesDepRtc(S, V + U)
}


method ComputeFISlice(S: Statement, V: set<Variable>) returns (SV: Statement)
	//ensures SV == FlowInsensitiveSlice(S,V)
{
	var Vstar := ComputeSlidesDepRtc(S, V);

	SV := ComputeSlides(S, Vstar);
}*/