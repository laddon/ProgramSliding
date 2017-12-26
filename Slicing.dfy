include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"
include "SlideDG.dfy"

method ComputeSlice(S: Statement, V: set<Variable>) returns (S_V: set<Slide>)
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

method finalDefSlides(slideDG: SlideDG, cfg: CFG, V: set<Variable>) returns (S_V: set<Slide>)
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

method finalDefSlidesOfVariable(slideDG: SlideDG, cfg: CFG, v: Variable) returns (Sv: set<Slide>)
{
	Sv := {};
	var vDefNodes := findDefNodes(slideDG.0, slideDG.1, v);
	// find all def nodes of v in slideDG

	while (|vDefNodes| > 0)
	{
		var vDefNode :| vDefNode in vDefNodes;
		vDefNodes := vDefNodes - {vDefNode};

		match vDefNode.0 {
			case Entry =>
			case Node(l) =>
				var cfgNode := CFGNode.Node(l);
				var pathsToExit := findAllPathsToExit(slideDG.0, cfg, [cfgNode], {}); // foreach node - find all paths to exit (in cfg) - seq of cfg nodes
				var res := isFinalDefSlide(pathsToExit, vDefNode /* or cfgNode */, v);		 // check if there is at least one path that it's only def is in the source node

				if (res)
				{
					Sv := Sv + {vDefNode};
				}	
		}
	}

	// foreach node - find all paths to exit (in cfg) and check if there is at least one path that it's only def is in the source node.
	// for example: if v=i then {5,9}

}

method findAllPathsToExit(S: Statement, cfg: CFG, path: seq<CFGNode>, tempPathsToExit: set<seq<CFGNode>>) returns (pathsToExit: set<seq<CFGNode>>)
{
	match path[0] {
		case Entry =>
			//assert |cfg.2[path[0]]| == 1;
			var node :| node in cfg.2[path[0]];
			pathsToExit := findAllPathsToExit(S, cfg, [node] + path, tempPathsToExit);
		case Node(l) =>
			var nodes := cfg.2[path[0]];
			var cfgNode :| cfgNode in nodes;
			nodes := nodes - {cfgNode};

			match cfgNode {
				case Entry =>
					// Can't be.
				case Node(l) =>
					pathsToExit := findAllPathsToExit(S, cfg, [CFGNode.Node(l)] + path, tempPathsToExit);
				case Exit =>
					tempPathsToExit := tempPathsToExit + {path};
			}

			if (|cfg.2[path[0]]| == 2) // if (nodes != {})
			{
				cfgNode :| cfgNode in nodes;
				nodes := nodes - {cfgNode};
				//assert nodes == {};

				match cfgNode {
					case Entry =>
						// Can't be.
					case Node(l) =>
						pathsToExit := findAllPathsToExit(S, cfg, [CFGNode.Node(l)] + path, tempPathsToExit);
					case Exit =>
						tempPathsToExit := tempPathsToExit + {path};
				}
			}	
		case Exit =>
			tempPathsToExit := tempPathsToExit + {path};
	}
 
	// �� ���� ������ �� ����� ��� 0 �� �� exit
	// ������ ���� �tempPathsToExit
	// �� ���� ������ ��� 1 �� ���� ���� ����� ��������� �� ���� ���
	// �� ���� ������ ��� 2 ���� ���� ����� ��������� �� ���� ������ ��� ���� ��������� �� ���� ����

	// ���� ��������� ������ �� [cfgNode]=path
	// ��� �� ��� ����� ��������� ����� �� ���� ������ ����
	// [neighbor,restOfPath]
	// ��� ��� ���� �� ������� �� ����� ������ ����.
	// ��� �� ��� ����� �exit
	// ����� �� path
	// �-tempPathsToExit
}

method isFinalDefSlide(pathsToExit: set<seq<CFGNode>>, vDefNode: Slide, v: Variable) returns (res: bool)
{
	var copyPathsToExit := pathsToExit;
	res := false;

	while (|copyPathsToExit| > 0 && !res)
	{
		var pathToExit :| pathToExit in copyPathsToExit;
		copyPathsToExit := copyPathsToExit - {pathToExit};
		res := isDefInPath(pathToExit, vDefNode, v);
	}

	res := !res;
}

method isDefInPath(pathToExit: seq<CFGNode>, vDefNode: Slide, v: Variable) returns (res: bool)
{
	//pathToExit = [cfgNode , cfgNode , ... , cfgNode]]
	//check for each pathToExit[i] if it's def is v. If so - return true, else - return false.

	if |pathToExit| == 0 { res := false; }
	else
	{
		if pathToExit[0] == vDefNode.1 { res := true; }
		else { res := isDefInPath(pathToExit[1..], vDefNode, v); }
	}
}

method findDefNodes(S: Statement, nodes: set<Slide>, v: Variable) returns (res: set<Slide>)
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