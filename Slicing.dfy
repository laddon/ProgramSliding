include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"
include "SlideDG.dfy"

method {:verify false}ComputeSlice(S: Statement, V: set<Variable>) returns (S_V: set<Slide>)
{
	var cfg := ComputeCFG(S);
	var pdgN, pdgE := ComputePDG(S, cfg); // TODO: Change to PDG
	var slideDG := ComputeSlideDG(S, pdgN, pdgE);
	S_V := finalDefSlides(slideDG, cfg, V);
	var worklist := S_V;

	while (|worklist| > 0)
		invariant forall Sn :: Sn in S_V ==> Sn in slideDG.2
	{
		var Sn :| Sn in S_V;
		worklist := worklist - {Sn};

		S_V := S_V + slideDG.2[Sn];
	}
}

method {:verify false}finalDefSlides(slideDG: SlideDG, cfg: CFG, V: set<Variable>) returns (S_V: set<Slide>)
{
	S_V := {};
	var copyV := V;

	while (|copyV| > 0)
	{
		var v :| v in copyV;
		copyV := copyV - {v};

		var Sv := finalDefSlidesOfVariable(slideDG, cfg, v);
		S_V := S_V + Sv;
	}
}

method {:verify false}finalDefSlidesOfVariable(slideDG: SlideDG, cfg: CFG, v: Variable) returns (Sv: set<Slide>)
{
	Sv := {};
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
					Sv := Sv + {vDefNode};
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





predicate SlideDependence(m: Slide, n: Slide, S: Statement)
	// For n, exists n' in n.cfgNodes, this n' includes v (v is defined in m) and uses v.

	//exists n' :: n' in n.2 ==> 


function ReachingDefinitions(cfg: CFG, cfgNode: CFGNode) : set<(CFGNode, Variable)>
	requires cfgNode in cfg.0
	ensures forall pair :: pair in ReachingDefinitions(cfg, cfgNode) ==> DefInCFGNode(pair.0, pair.1) && SingleDefPath(cfg, cfgNode, pair.0, pair.1)


function SlidesUseVariable(slideDG: SlideDG, slide: Slide, v: Variable) : set<Slide>
	requires slide in slideDG.1
	requires v == slide.1
	ensures forall s :: s in SlidesUseVariable(slideDG, slide, v) ==> s in slideDG.1 && SlideUseVariable(s, v)


predicate SlideUseVariable(slide: Slide, v: Variable)
	// Check if slide uses v.

predicate DefInCFGNode(cfgNode: CFGNode, v: Variable)
	// Check if cfgNode defines v.

predicate SingleDefPath(cfg: CFG, cfgNode: CFGNode, cfgNode': CFGNode, v': Variable)
	// Check if path from cfgNode' to cfgNode exists (in cfg), that doesn't include more def to v'.
