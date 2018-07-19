include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"
include "SlideDG.dfy"

method {:verify false}Slice(S: Statement, V: set<Variable>) returns (slidesSV: set<Slide>)
	requires Core(S)
{
	var cfg := ComputeCFG(S);
	//var pdgN, pdgE := ComputePDG(S, cfg); // TODO: Change to PDG
	var slideDG := ComputeSlideDG(S, cfg.0, cfg.1);

	slidesSV := ComputeSlice(S, V, slideDG, cfg);
}

method {:verify true}ComputeSlice(S: Statement, V: set<Variable>, slideDG: SlideDG, cfg: CFG) returns (slidesSV: set<Slide>)
	requires Core(S)
	requires forall s :: s in slideDG.1 ==> s in slideDG.2
	requires forall s1,s2 :: s1 in slideDG.2 && s2 in slideDG.2[s1]  ==> s2 in slideDG.1
	ensures forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1)))	 
{
	slidesSV := FindFinalDefSlides(S, slideDG, cfg, V);
	assert slidesSV == finalDefSlides(S, slideDG, cfg, V);

	var worklist := slidesSV;

	var visited := {};
	
	while (|worklist| > 0)
		invariant forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1)))	 
		invariant forall Sn :: Sn in worklist ==> Sn in slideDG.2
		invariant worklist <= slidesSV <= slideDG.1
		invariant visited + worklist == slidesSV
		invariant visited * worklist == {}
		//invariant forall Sm :: Sm in worklist ==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1)))
		decreases slideDG.1 - visited
	{
		var slide :| slide in worklist;
		assert (visited + {slide}) * ((worklist - {slide}) + (slideDG.2[slide] - slidesSV - {slide})) == {} by {
			assert visited * ((worklist - {slide}) + (slideDG.2[slide] - slidesSV - {slide})) == {} by { assert visited * worklist == {}; assert visited <= slidesSV; }
			assert slide !in (worklist - {slide}) + (slideDG.2[slide] - slidesSV - {slide});
		}
		assert visited + {slide} + ((worklist - {slide}) + (slideDG.2[slide] - slidesSV - {slide})) == slidesSV + (slideDG.2[slide] - slidesSV - {slide}) by {
			assert visited + worklist == slidesSV;
			assert slide in slidesSV;
			var nr := (slideDG.2[slide] - slidesSV - {slide});
			assert ((worklist - {slide}) + nr) <= slidesSV + nr by {
				calc {
					(worklist - {slide}) + nr;
				<=
					worklist + nr;
				<=
					slidesSV + nr;
				}
			}
			assert visited + {slide} + ((worklist - {slide}) + nr) >= slidesSV + nr by {
				calc {
					visited + {slide} + ((worklist - {slide}) + nr);
				>=
					visited + worklist + nr;
				==
					slidesSV + nr;
				}
			}
		}
		worklist, visited := worklist - {slide}, visited + {slide};
		var newlyReachable := slideDG.2[slide] - slidesSV - {slide};
		slidesSV := slidesSV + newlyReachable; // + slideDG.2[slide];
		worklist := worklist + newlyReachable; // + (slideDG.2[slide] - visited)

		assert forall Sm :: Sm in slidesSV ==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1))) by {
			assert forall Sm :: Sm in slidesSV - newlyReachable ==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in (visited - {slide}) * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1)));
			
		}
		assert forall Sm :: Sm in slidesSV <== (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, slideDG.1)));	 

	}
}

function finalDefSlides(S: Statement, slideDG: SlideDG, cfg: CFG, V: set<Variable>): set<Slide>
	requires Core(S)
{
	set slide | slide in slideDG.1 && slide.1 in V && slide in finalDefSlidesOfVariable(S, slideDG, cfg, slide.1)
}

method {:verify true}FindFinalDefSlides(S: Statement, slideDG: SlideDG, cfg: CFG, V: set<Variable>) returns (slidesSV: set<Slide>)
	requires Core(S)
	ensures slidesSV == finalDefSlides(S, slideDG, cfg, V)
{
	slidesSV := {};
	var copyV := V;

	while (|copyV| > 0)
		decreases copyV
	{
		var v :| v in copyV;
		copyV := copyV - {v};

		var Sv := FindFinalDefSlidesOfVariable(S, slideDG, cfg, v);
		slidesSV := slidesSV + Sv;
	}

	assume slidesSV == finalDefSlides(S, slideDG, cfg, V);
}

function finalDefSlidesOfVariable(S: Statement, slideDG: SlideDG, cfg: CFG, v: Variable): set<Slide>
	requires Core(S)
{
	set slide | slide in slideDG.1 && ReachingDefinition(S, cfg, CFGNode.Exit, slide.0, v)
}

method {:verify false}FindFinalDefSlidesOfVariable(S: Statement, slideDG: SlideDG, cfg: CFG, v: Variable) returns (slidesSv: set<Slide>)
	requires Core(S)
	ensures slidesSv == finalDefSlidesOfVariable(S, slideDG, cfg, v)
{
	slidesSv := {};
	var vDefNodes := findDefNodes(slideDG.0, slideDG.1, v); // find all def nodes of v in slideDG
	
	while (|vDefNodes| > 0)
	{
		var vDefNode :| vDefNode in vDefNodes;
		vDefNodes := vDefNodes - {vDefNode};

		match vDefNode.0 {
			case Entry =>
			case Node(l) =>
				var cfgNode := CFGNode.Node(l);
				var pathsToExit := findAllPathsToExit(slideDG.0, cfg, [cfgNode], {}); // foreach node - find all paths to exit (in cfg) - seq of cfg nodes
				var res := isFinalDefSlide(slideDG.0, pathsToExit, vDefNode);	      // check if there is at least one path that its only def is in the source node

				if (res)
				{
					slidesSv := slidesSv + {vDefNode};
				}	
		}
	}
}

method {:verify false}findAllPathsToExit(S: Statement, cfg: CFG, path: seq<CFGNode>, tempPathsToExit: set<seq<CFGNode>>) returns (pathsToExit: set<seq<CFGNode>>)
{
	pathsToExit := tempPathsToExit;
	
	match path[0] {
		case Entry =>
			//assert |cfg.2[path[0]]| == 1;
			var node :| node in cfg.2[path[0]];
			pathsToExit := findAllPathsToExit(S, cfg, [node] + path, pathsToExit);
		case Node(l) =>
			var nodes := cfg.2[path[0]];

			while (|nodes| > 0) // Could be 1 or 2.
			{
				var cfgNode :| cfgNode in nodes;
				nodes := nodes - {cfgNode};
				if (cfgNode !in path)
				{
					match cfgNode {
						case Entry =>
							// Can't be.
						case Node(l) =>
							pathsToExit := findAllPathsToExit(S, cfg, [cfgNode] + path, pathsToExit);
						case Exit =>
							pathsToExit := pathsToExit + {path};
					}
				}
			}
		case Exit =>
			pathsToExit := pathsToExit + {path};
	}
}

method {:verify false}isFinalDefSlide(S: Statement, pathsToExit: set<seq<CFGNode>>, vDefNode: Slide) returns (res: bool)
{
	var copyPathsToExit := pathsToExit;
	res := false;

	while (|copyPathsToExit| > 0 && !res)
	{
		var pathToExit :| pathToExit in copyPathsToExit;
		copyPathsToExit := copyPathsToExit - {pathToExit};
		res := isDefInPath(S, pathToExit[..|pathToExit|-1], vDefNode);
	}

	res := !res;
}

method {:verify false}isDefInPath(S: Statement, pathToExit: seq<CFGNode>, vDefNode: Slide) returns (res: bool)
{
	//pathToExit = [cfgNode , cfgNode , ... , cfgNode]]
	//check for each pathToExit[i] if it's def is v. If so - return true, else - return false.

	if |pathToExit| == 0 { res := false; }
	else
	{
		match pathToExit[0]
		{
			case Node(l) =>
				var defVars := DefinedVars(S, l);
				if (vDefNode.1 in defVars)
				{
					res := true;
				}
				else
				{
					res := isDefInPath(S, pathToExit[1..], vDefNode);
				}
		}
	}
}

method {:verify false}findDefNodes(S: Statement, nodes: set<Slide>, v: Variable) returns (res: set<Slide>)
{
	if |nodes| == 0  { res := {}; }
	else
	{
		var node :| node in nodes;

		if v == node.1 {
			var res' := findDefNodes(S, nodes - {node}, v);
			res := {node} + res';
		} else {
			res := findDefNodes(S, nodes - {node}, v);
		}
	}
}











datatype CFGPath = Empty | Extend(CFGPath, CFGNode)
datatype SlideDGPath = Empty | Extend(SlideDGPath, Slide)
//datatype Path<T> = Empty | Extend(Path<T>, T)

predicate CFGReachable(from: CFGNode, to: CFGNode, S: set<CFGNode>)
	//requires null !in S
	//reads S
{
	exists via: CFGPath :: CFGReachableVia(from, via, to, S)
}

predicate CFGReachableVia(from: CFGNode, via: CFGPath, to: CFGNode, S: set<CFGNode>)
	//requires null !in S
	//reads S
	decreases via
{
	match via
	case Empty => from == to
	case Extend(prefix, n) => n in S && to in CFGNeighbours(n) && CFGReachableVia(from, prefix, n, S)
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



predicate SlideDependence(cfg: CFG, m: Slide, n: Slide, S: Statement)
	// For n, exists n' in n.cfgNodes, this n' includes v (v is defined in m) and uses v.
	requires Core(S)
{
	var v := m.1;
	exists n' :: n' in n.2 && 
	match n' {
		case Node(l) => v in UsedVars(S, l) && ReachingDefinition(S, cfg, n', m.0, v)
		case Entry => false
		case Exit => false
	}
}

function ReachingDefinitions(S: Statement, cfg: CFG, cfgNode: CFGNode): (res: set<(CFGNode, Variable)>)
	requires cfgNode in cfg.0
	requires Core(S)
	ensures forall pair :: pair in res <==> ReachingDefinition(S, cfg, cfgNode, pair.0, pair.1)

predicate DefInCFGNode(S: Statement, cfgNode: CFGNode, v: Variable)
	requires Core(S)
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
	requires Core(S)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
{
	exists path: CFGPath :: CFGReachableVia(cfgNode', path, cfgNode, cfg.0) && (forall node :: node in Nodes(path) ==> !DefInCFGNode(S, node, v'))
}

predicate ReachingDefinition(S: Statement, cfg: CFG, cfgNode: CFGNode, cfgNode': CFGNode, v': Variable)
	requires Core(S)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
{
	DefInCFGNode(S, cfgNode', v') && exists path: CFGPath :: CFGReachableVia(cfgNode', path, cfgNode, cfg.0) && (forall node :: node in Nodes(path) - {cfgNode'} ==> !DefInCFGNode(S, node, v'))
}

function Nodes(path: CFGPath): set<CFGNode>
	decreases path
{
	match path
	case Empty => {}
	case Extend(prefix, n) => {n} + Nodes(prefix)
}