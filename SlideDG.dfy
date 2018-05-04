include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// SlideDG Definitions:
type Slide = (CFGNode, Variable, set<CFGNode>) // changed from PDGNode To CFGNode
type Edge = (Slide, Slide, set<Variable>)
type SlideDG = (Statement, set<Slide>, map<Slide, set<Slide>>) // map from node to it's predecssors

method ComputeSlideDG(S: Statement, pdgN: set<PDGNode>, pdgE: set<PDGEdge>) returns (slideDG: SlideDG)
	requires Core(S)
{
	var N := ComputeSlideDGNodes(S, pdgN);
	var E := ComputeSlideDGEdges(S, N);
	var m : map<Slide, set<Slide>>; // TODO

	//slideDG := (S, N, E, m);
}

method ComputeSlideDGNodes(S: Statement, pdgN: set<PDGNode>) returns (slides: set<Slide>)
	requires Core(S)
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


function SlideDGNeighbours(n: Slide) : set<Slide>