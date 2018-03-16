include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"
include "SlideDG.dfy"

method {:verify false}ComputeSlice(S: Statement, V: set<Variable>) returns (slidesSV: set<Slide>)
	ensures forall Sm :: Sm in slidesSV <==> Sm in finalDefSlides( , , V) || ( exists Sn in finalDefSlides( , , V) and path (using generic path) in slideDG from Sm to Sn)
{
	var cfg := ComputeCFG(S);
	var pdgN, pdgE := ComputePDG(S, cfg); // TODO: Change to PDG
	var slideDG := ComputeSlideDG(S, pdgN, pdgE);
	slidesSV := FindFinalDefSlides(slideDG, cfg, V);
	var worklist := slidesSV;

	while (|worklist| > 0)
		invariant forall Sn :: Sn in slidesSV ==> Sn in slideDG.2
	{
		var Sn :| Sn in slidesSV;
		worklist := worklist - {Sn};

		slidesSV := slidesSV + slideDG.2[Sn];
	}
}

function finalDefSlides(slideDG: SlideDG, cfg: CFG, V: set<Variable>): set<Slide>
{
	set slide | slide in slideDG.1 && slide.1 in V && slide in finalDefSlidesOfVariable(slideDG, cfg, slide.1)
}

method {:verify false}FindFinalDefSlides(slideDG: SlideDG, cfg: CFG, V: set<Variable>) returns (slidesSV: set<Slide>)
	ensures slidesSV == finalDefSlides(slideDG, cfg, V)
{
	slidesSV := {};
	var copyV := V;

	while (|copyV| > 0)
	{
		var v :| v in copyV;
		copyV := copyV - {v};

		var Sv := FindFinalDefSlidesOfVariable(slideDG, cfg, v);
		slidesSV := slidesSV + Sv;
	}
}

function finalDefSlidesOfVariable(slideDG: SlideDG, cfg: CFG, v: Variable): set<Slide>
{
	set slide | slide in slideDG.1 && ReachingDefinition(cfg, CFGNode.Exit, slide.0, v)
}

method {:verify false}FindFinalDefSlidesOfVariable(slideDG: SlideDG, cfg: CFG, v: Variable) returns (slidesSv: set<Slide>)
	ensures slidesSv == finalDefSlidesOfVariable(slideDG, cfg, v)
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
datatype Path<T> = Empty | Extend(Path<T>, T)

predicate Reachable(from: CFGNode, to: CFGNode, S: set<CFGNode>)
	//requires null !in S
	//reads S
{
	exists via: CFGPath :: ReachableVia(from, via, to, S)
}

predicate ReachableVia(from: CFGNode, via: CFGPath, to: CFGNode, S: set<CFGNode>)
	//requires null !in S
	//reads S
	decreases via
{
	match via
	case Empty => from == to
	case Extend(prefix, n) => n in S && to in Neighbours(n) && ReachableVia(from, prefix, n, S)
}



predicate SlideDependence(cfg: CFG, m: Slide, n: Slide, S: Statement)
	// For n, exists n' in n.cfgNodes, this n' includes v (v is defined in m) and uses v.
{
	var v := m.1;
	exists n' :: n' in n.2 && 
	match n' {
		case Node(l) => v in UsedVars(S, l) && ReachingDefinition(cfg, n', m.0, v)
		case Entry => false
		case Exit => false
	}
}

function ReachingDefinitions(cfg: CFG, cfgNode: CFGNode): (res: set<(CFGNode, Variable)>)
	requires cfgNode in cfg.0
	ensures forall pair :: pair in res <==> ReachingDefinition(cfg, cfgNode, pair.0, pair.1)

predicate DefInCFGNode(cfgNode: CFGNode, v: Variable)
	// Check if cfgNode defines v.

predicate NoDefPath(cfg: CFG, cfgNode: CFGNode, cfgNode': CFGNode, v': Variable)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
{
	exists path: CFGPath :: ReachableVia(cfgNode', path, cfgNode, cfg.0) && (forall node :: node in Nodes(path) ==> !DefInCFGNode(node, v'))
}

predicate ReachingDefinition(cfg: CFG, cfgNode: CFGNode, cfgNode': CFGNode, v': Variable)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
{
	DefInCFGNode(cfgNode', v') && exists path: CFGPath :: ReachableVia(cfgNode', path, cfgNode, cfg.0) && (forall node :: node in Nodes(path) ==> !DefInCFGNode(node, v'))
}

function Nodes(path: CFGPath): set<CFGNode>
	decreases path
{
	match path
	case Empty => {}
	case Extend(prefix, n) => {n} + Nodes(prefix)
}