include "Definitions.dfy"
include "Util.dfy"

// Label Definition from AST of the Statement:
newtype Branch = b: int | 1 <= b <= 2
type Label = seq<Branch>

// CFG Definitions:
datatype CFGNode = Node(l:Label) | Entry | Exit
type CFGEdge = (CFGNode, CFGNode)
type CFG = (set<CFGNode>, set<CFGEdge>, map<CFGNode, set<CFGNode>>) // map from cfgNode to it's successors

method ComputeCFG(S: Statement) returns (cfg: CFG)
{
	var N := ComputeCFGNodes(S, []);
	var E := ComputeCFGEdges(S, N);
	var m : map<CFGNode, set<CFGNode>>; // TODO
	cfg := (N, E, m);
}

function method ComputeCFGNodes(S: Statement, l: Label) : set<CFGNode>
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


function method FindSubstatement(S: Statement, l: Label) : Statement
	requires |l| >= 1
{
	match S {
		case Assignment(LHS,RHS) => if |l| == 1 then S else Skip
		case SeqComp(S1,S2) => if |l| >= 2 then (if l[1] == 1 then FindSubstatement(S1, l[1..]) else FindSubstatement(S2, l[1..])) else Skip
		case IF(B,Sthen,Selse) => if |l| >= 2 then (if l[1] == 1 then FindSubstatement(Sthen, l[1..]) else FindSubstatement(Selse, l[1..])) else Skip
		case DO(B,S0) => if |l| >= 2 then FindSubstatement(S0, l[1..]) else Skip
		case Skip => Skip
	}
}

function UsedVars(S: Statement, l: Label) : set<Variable>
/*{
	// call FindSubstatement

	var subStatement := FindSubstatement(S, l);

}*/

function method DefinedVars(S: Statement, l: Label) : set<Variable>
/*{
	// call FindSubstatement

	var subStatement := FindSubstatement(S, l);

}*/

function Neighbours(n: CFGNode) : set<CFGNode>