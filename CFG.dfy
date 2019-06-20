include "Definitions.dfy"
include "Util.dfy"

// Label Definition from AST of the Statement:
newtype Branch = b: int | 1 <= b <= 2
type Label = seq<Branch>

// CFG Definitions:
datatype CFGNode = Node(l:Label) | Entry | Exit
type CFGEdge = (CFGNode, CFGNode)
type CFG = (set<CFGNode>, set<CFGEdge>, map<CFGNode, set<CFGNode>>) // map from cfgNode to it's successors

function method CFGNodes(cfg: CFG): set<CFGNode>
{
	cfg.0
}

function method CFGEdges(cfg: CFG): set<CFGEdge>
{
	cfg.1
}

function method CFGMap(cfg: CFG): map<CFGNode, set<CFGNode>>
{
	cfg.2
}

function method ComputeCFG(S: Statement): CFG
	ensures CFGOf(S) == ComputeCFG(S)
/*{
	var N := ComputeCFGNodes(S, []);
	var E := ComputeCFGEdges(S, N);
	var m := map<CFGNode, set<CFGNode>>; // TODO
	(N, E, m)
}*/

function method ComputeCFGNodes(S: Statement, l: Label) : set<CFGNode>
	requires Core(S)
{
	match S {
		case Assignment(LHS,RHS) => {CFGNode.Node(l)}
		case SeqComp(S1,S2) => ComputeCFGNodes(S1, l+[1]) + ComputeCFGNodes(S2, l+[2])
		case IF(B,Sthen,Selse) => {CFGNode.Node(l)} + ComputeCFGNodes(Sthen, l+[1]) + ComputeCFGNodes(Selse, l+[2])
		case DO(B,S0) => {CFGNode.Node(l)} + ComputeCFGNodes(S0, l+[1])
		case Skip => {}
	}
}

function method ComputeCFGEdges(S: Statement, N: set<CFGNode>) : set<CFGEdge>

function CFGOf(S: Statement): CFG

datatype CFGPath = Empty | Extend(CFGPath, CFGNode)

function CFGNeighbours(n: CFGNode) : set<CFGNode>

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