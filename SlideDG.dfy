include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// SlideDG Definitions:
type Slide = Statement
type Edge = (Slide, Slide, set<Variable>)

method ComputeSlideDG(S: Statement) returns (N: set<Slide>, E: set<Edge>)
{
	
}

method ComputeSlide(S: Statement, v: Variable, l: Label) returns (n: Slide)
{
	
}

