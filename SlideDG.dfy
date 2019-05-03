include "PDG.dfy"
//include "ProofUtil.dfy"

// SlideDG Definitions:
type Slide = (CFGNode, Variable, set<CFGNode>) // changed from PDGNode To CFGNode
type Edge = (Slide, Slide, set<Variable>)
type SlideDG = (Statement, set<Slide>, map<Slide, set<Slide>>) // map from node to it's predecssors

function method SlideCFGNode(s: Slide): CFGNode
{
	s.0
}

function method SlideVariable(s: Slide): Variable
{
	s.1
}

function method SlideCFGNodes(s: Slide): set<CFGNode>
{
	s.2
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

method ComputeSlideDG(S: Statement, cfg: CFG) returns (slideDG: SlideDG)
	requires Core(S)
	//ensures SlideDGOf(S, cfg) == ComputeSlideDG(S, cfg)
	//ensures IsSlideDGOf(slideDG, S)
{
	var N := ComputeSlideDGNodes(S, cfg.0);
	var E := ComputeSlideDGEdges(S, N);
	var m : map<Slide, set<Slide>>; // TODO

	slideDG := (S, N, m);
}

predicate IsSlideDGOf(slideDG: SlideDG, S: Statement)
{
	//forall Sm, Sn :: Sm in SlideDGSlides(slideDG) && Sn in SlideDGSlides(slideDG) ==>
		//(exists e: Edge :: e in EdgesOf(slideDG) && e.0 == Sm && e.1 == Sn <==> SlideDependence(CFGOf(S), Sm, Sn, S))


	//SlideDGStatement(slideDG) == S &&     && 
	SlideDGOf(S, CFGOf(S)) == slideDG

	//(S, set<Slide>, map<Slide, set<Slide>>)
}

lemma ExistsSlideDependence(slideDG: SlideDG, S: Statement, Sm: Slide, Sn: Slide)
	requires IsSlideDGOf(slideDG, S)
	requires Sm in SlideDGSlides(slideDG)
	requires Sn in SlideDGSlides(slideDG)
	ensures exists e: Edge :: e in EdgesOf(slideDG) && e.0 == Sm && e.1 == Sn <==> SlideDependence(CFGOf(S), Sm, Sn, S)

function SlideDGOf(S: Statement, cfg: CFG): SlideDG

// With CFG instead of PDG:
method {:verify false}ComputeSlideDGNodes(S: Statement, cfgN: set<CFGNode>) returns (slides: set<Slide>)
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
	ensures forall s :: s in slidesOf(S, V) ==> assume s.0 != CFGNode.Entry && s.0 != CFGNode.Exit; match s.0 { case Node(l1) => ValidLabel(l1, S) && !IsEmptyAssignment(slipOf(S, l1))}
{
	slidesOf'(S, V, [], {})
}

function {:verify false}slidesOf'(S: Statement, V: set<Variable>, l: Label, nodes: set<CFGNode>): (slides: set<Slide>)
	reads *
	requires Valid(S)
	requires Core(S)
	ensures forall s :: s in slides ==> assume s.0 != CFGNode.Entry && s.0 != CFGNode.Exit; match s.0 { case Node(l1) => ValidLabel(l1, S) && !IsEmptyAssignment(slipOf(S, l1))}
{
	match S {
	case Skip => {}
	case Assignment(LHS,RHS) => set v | v in V * setOf(LHS) :: (CFGNode.Node(l), v, nodes)
	case SeqComp(S1,S2) =>		slidesOf'(S1, V, l+[1], nodes) + slidesOf'(S2, V, l+[2], nodes)
	case IF(B0,Sthen,Selse) =>	slidesOf'(Sthen, V, l+[1], nodes + {CFGNode.Node(l)}) + slidesOf'(Selse, V, l+[2], nodes + {CFGNode.Node(l)})
	case DO(B,Sloop) =>			slidesOf'(Sloop, V, l+[1], nodes + {CFGNode.Node(l)})
	}
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

predicate SlideDependence(cfg: CFG, m: Slide, n: Slide, S: Statement)
	// For n, exists n' in n.cfgNodes, this n' includes v (v is defined in m) and uses v and there exists a cfg-path with no more defs to v..
	requires Valid(S) && Core(S)
{
	var v := SlideVariable(m);
	exists n' :: n' in SlideCFGNodes(n) && 
	match n' {
		case Node(l) => v in UsedVars(S, l) && ReachingDefinition(S, cfg, n', SlideCFGNode(m), v)
		case Entry => false
		case Exit => false
	}
}

predicate ReachingDefinition(S: Statement, cfg: CFG, cfgNode: CFGNode, cfgNode': CFGNode, v': Variable)
	requires Valid(S) && Core(S)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
{
	DefInCFGNode(S, cfgNode', v') && exists path: CFGPath :: CFGReachableVia(cfgNode', path, cfgNode, CFGNodes(cfg)) && (forall node :: node in Nodes(path) - {cfgNode'} ==> !DefInCFGNode(S, node, v'))
}

predicate DefInCFGNode(S: Statement, cfgNode: CFGNode, v: Variable)
	requires Valid(S) && Core(S)
	// Check if cfgNode defines v.
{
	match cfgNode
	case Entry => false
	case Exit => false
	case Node(l) => 
		var s := FindSubstatement(S, l);
		match s
		case Assignment(LHS,RHS) => v in LHS
		case Skip => false
		case SeqComp(S1,S2) => false
		case IF(B0,Sthen,Selse) => false
		case DO(B,Sloop) => false
		case LocalDeclaration(L,S0) => false
		case Live(L,S0) => false
		case Assert(B) => false

}

predicate NoDefPath(S: Statement, cfg: CFG, cfgNode: CFGNode, cfgNode': CFGNode, v': Variable)
	requires Valid(S) && Core(S)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
{
	exists path: CFGPath :: CFGReachableVia(cfgNode', path, cfgNode, CFGNodes(cfg)) && (forall node :: node in Nodes(path) ==> !DefInCFGNode(S, node, v'))
}

function Nodes(path: CFGPath): set<CFGNode>
	decreases path
{
	match path
	case Empty => {}
	case Extend(prefix, n) => {n} + Nodes(prefix)
}

function ReachingDefinitions(S: Statement, cfg: CFG, cfgNode: CFGNode): (res: set<(CFGNode, Variable)>)
	requires cfgNode in CFGNodes(cfg)
	requires Valid(S) && Core(S)
	ensures forall pair :: pair in res <==> ReachingDefinition(S, cfg, cfgNode, pair.0, pair.1)