include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"
include "SlideDG.dfy"

method {:verify false}Slice(S: Statement, V: set<Variable>) returns (slidesSV: set<Slide>)
	requires Core(S)
{
	var cfg := ComputeCFG(S);
	//var pdgN, pdgE := ComputePDG(S, cfg); // TODO: Change to PDG
	var slideDG := ComputeSlideDG(S, cfg);

	slidesSV := ComputeSlice(S, V, slideDG, cfg);
}

/*method {:verify false}ComputeSlice(S: Statement, V: set<Variable>, slideDG: SlideDG, cfg: CFG) returns (slidesSV: set<Slide>)
	requires Core(S)
	requires forall s :: s in SlideDGSlides(slideDG) ==> s in SlideDGMap(slideDG)
	requires forall s1,s2 :: s1 in SlideDGMap(slideDG) && s2 in SlideDGMap(slideDG)[s1]  ==> s2 in SlideDGSlides(slideDG)
	ensures forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG))))	 
{
	slidesSV := FindFinalDefSlides(S, slideDG, cfg, V);
	
	var worklist := slidesSV;
	var visited := {};
	
	while (|worklist| > 0)
	{
		var slide :| slide in worklist;
		
		worklist, visited := worklist - {slide}, visited + {slide};
		var newlyReachable := SlideDGMap(slideDG)[slide] - slidesSV - {slide};
		slidesSV := slidesSV + newlyReachable; // + SlideDGMap(slideDG)[slide];
		worklist := worklist + newlyReachable; // + (SlideDGMap(slideDG)[slide] - visited)
	}
}*/

method {:verify false}ComputeSlice(S: Statement, V: set<Variable>, slideDG: SlideDG, cfg: CFG) returns (slidesSV: set<Slide>)
	requires Core(S)
	requires forall s :: s in SlideDGSlides(slideDG) ==> s in SlideDGMap(slideDG)
	requires forall s1,s2 :: s1 in SlideDGMap(slideDG) && s2 in SlideDGMap(slideDG)[s1]  ==> s2 in SlideDGSlides(slideDG)
	ensures forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG))))	 
{
	slidesSV := FindFinalDefSlides(S, slideDG, cfg, V);
	assert slidesSV == finalDefSlides(S, slideDG, cfg, V);

	var worklist := slidesSV;

	var visited := {};
	
	while (|worklist| > 0)
		invariant forall Sm :: Sm in slidesSV <==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG))))	 
		invariant forall Sn :: Sn in worklist ==> Sn in SlideDGMap(slideDG)
		invariant worklist <= slidesSV <= SlideDGSlides(slideDG)
		invariant visited + worklist == slidesSV
		invariant visited * worklist == {}
		//invariant forall Sm :: Sm in worklist ==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG))))
		decreases SlideDGSlides(slideDG) - visited
	{
		var slide :| slide in worklist;
		assert (visited + {slide}) * ((worklist - {slide}) + (SlideDGMap(slideDG)[slide] - slidesSV - {slide})) == {} by {
			assert visited * ((worklist - {slide}) + (SlideDGMap(slideDG)[slide] - slidesSV - {slide})) == {} by { assert visited * worklist == {}; assert visited <= slidesSV; }
			assert slide !in (worklist - {slide}) + (SlideDGMap(slideDG)[slide] - slidesSV - {slide});
		}
		assert visited + {slide} + ((worklist - {slide}) + (SlideDGMap(slideDG)[slide] - slidesSV - {slide})) == slidesSV + (SlideDGMap(slideDG)[slide] - slidesSV - {slide}) by {
			assert visited + worklist == slidesSV;
			assert slide in slidesSV;
			var nr := (SlideDGMap(slideDG)[slide] - slidesSV - {slide});
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
		var newlyReachable := SlideDGMap(slideDG)[slide] - slidesSV - {slide};
		slidesSV := slidesSV + newlyReachable; // + SlideDGMap(slideDG)[slide];
		worklist := worklist + newlyReachable; // + (SlideDGMap(slideDG)[slide] - visited)

		assert forall Sm :: Sm in slidesSV ==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG)))) by {
			assert forall Sm :: Sm in slidesSV - newlyReachable ==> (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in (visited - {slide}) * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG))));
			
		}
		assert forall Sm :: Sm in slidesSV <== (Sm in finalDefSlides(S, slideDG, cfg, V) || (exists Sn :: Sn in visited * finalDefSlides(S, slideDG, cfg, V) && SlideDGReachable(slideDG, Sm, Sn, SlideDGSlides(slideDG))));	 

	}
}

function finalDefSlides(S: Statement, slideDG: SlideDG, cfg: CFG, V: set<Variable>): set<Slide>
	requires Core(S)
{
	set slide | slide in SlideDGSlides(slideDG) && SlideVariable(slide) in V && slide in finalDefSlidesOfVariable(S, slideDG, cfg, SlideVariable(slide))
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
	set slide | slide in SlideDGSlides(slideDG) && ReachingDefinition(S, cfg, CFGNode.Exit, SlideCFGNode(slide), v)
}

method {:verify false}FindFinalDefSlidesOfVariable(S: Statement, slideDG: SlideDG, cfg: CFG, v: Variable) returns (slidesSv: set<Slide>)
	requires Core(S)
	ensures slidesSv == finalDefSlidesOfVariable(S, slideDG, cfg, v)
{
	slidesSv := {};
	var vDefNodes := findDefNodes(SlideDGStatement(slideDG), SlideDGSlides(slideDG), v); // find all def nodes of v in slideDG
	
	while (|vDefNodes| > 0)
	{
		var vDefNode :| vDefNode in vDefNodes;
		vDefNodes := vDefNodes - {vDefNode};

		match SlideCFGNode(vDefNode) {
			case Entry =>
			case Node(l) =>
				var cfgNode := CFGNode.Node(l);
				var pathsToExit := findAllPathsToExit(SlideDGStatement(slideDG), cfg, [cfgNode], {}); // foreach node - find all paths to exit (in cfg) - seq of cfg nodes
				var res := isFinalDefSlide(SlideDGStatement(slideDG), pathsToExit, vDefNode);	      // check if there is at least one path that its only def is in the source node

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
			//assert |CFGMap(cfg)[path[0]]| == 1;
			var node :| node in CFGMap(cfg)[path[0]];
			pathsToExit := findAllPathsToExit(S, cfg, [node] + path, pathsToExit);
		case Node(l) =>
			var nodes := CFGMap(cfg)[path[0]];

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
				if (SlideVariable(vDefNode) in defVars)
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

		if v == SlideVariable(node) {
			var res' := findDefNodes(S, nodes - {node}, v);
			res := {node} + res';
		} else {
			res := findDefNodes(S, nodes - {node}, v);
		}
	}
}
