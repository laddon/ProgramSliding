include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// SlideDG Definitions:
type Slide = (CFGNode, Variable, set<CFGNode>) // changed from PDGNode To CFGNode
type Edge = (Slide, Slide, set<Variable>)
type SlideDG = (Statement, set<Slide>, map<Slide, set<Slide>>) // map from node to it's predecssors

function SlideDG(S: Statement, cfg: CFG): SlideDG

method ComputeSlideDG(S: Statement, cfgN: set<CFGNode>, cfgE: set<CFGEdge>) returns (slideDG: SlideDG)
	requires Core(S)
	ensures SlideDGOf(slideDG, S)
{
	var N := ComputeSlideDGNodes(S, cfgN);
	var E := ComputeSlideDGEdges(S, N);
	var m : map<Slide, set<Slide>>; // TODO

	slideDG := (S, N, m);
}

predicate SlideDGOf(slideDG: SlideDG, S: Statement)


// With CFG instead of PDG:
method ComputeSlideDGNodes(S: Statement, cfgN: set<CFGNode>) returns (slides: set<Slide>)
	requires Core(S)
{
	slides := {};
	var copyCFGN := cfgN;

	while (|copyCFGN| > 0)
	{
		var cfgNode :| cfgNode in copyCFGN;
		copyCFGN := copyCFGN - {cfgNode};
		match cfgNode {
			case Entry =>
			case Exit =>
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

function SlideDGNodes(S: Statement, cfgN: set<CFGNode>) : set<Slide>

/*method ComputeSlideDGNodes(S: Statement, pdgN: set<PDGNode>) returns (slides: set<Slide>)
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


function SlideDGNeighbours(slideDG: SlideDG, n: Slide) : set<Slide>

function slidesOf(S: Statement, V: set<Variable>) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	slidesOf'(S, V, [], {})
}

function slidesOf'(S: Statement, V: set<Variable>, l: Label, nodes: set<CFGNode>) : set<Slide>
	reads *
	requires Valid(S)
	requires Core(S)
{
	match S {
	case Skip => {}
	case Assignment(LHS,RHS) => set v | v in V * setOf(LHS) :: (CFGNode.Node(l), v, nodes)
	case SeqComp(S1,S2) =>		slidesOf'(S1, V, l+[1], nodes) + slidesOf'(S2, V, l+[2], nodes)
	case IF(B0,Sthen,Selse) =>	slidesOf'(Sthen, V, l+[1], nodes + {CFGNode.Node(l)}) + slidesOf'(Selse, V, l+[2], nodes + {CFGNode.Node(l)})
	case DO(B,Sloop) =>			slidesOf'(Sloop, V, l+[1], nodes + {CFGNode.Node(l)})
	}
}