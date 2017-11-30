include "Definitions.dfy"
include "Util.dfy"

// Label Definition from AST of the Statement:
newtype Branch = b: int | 1 <= b <= 2
type Label = seq<Branch>

// CFG Definitions:
datatype CFGNode = Node(l:Label) | Entry | Exit
type CFGEdge = (CFGNode, CFGNode)
type CFG = (set<CFGNode>, set<CFGEdge>)

method ComputeCFG(S: Statement) returns (N: set<CFGNode>, E: set<CFGEdge>)
{
	
}

function FindSubstatement(S: Statement, l: Label) : Statement

function UsedVars(S: Statement, l: Label) : set<Variable>
	// call FindSubstatement

function DefinedVars(S: Statement, l: Label) : set<Variable>
	// call FindSubstatement
