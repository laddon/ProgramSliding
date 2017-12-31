include "Definitions.dfy"
include "Util.dfy"
include "PDG.dfy"


// SlideDG Definitions:
type Slide = (PDGNode, Variable, set<PDGNode>)
type Edge = (Slide, Slide, set<Variable>)
type SlideDG = (Statement, set<Slide>, map<Slide, set<Slide>>) // map from node to it's predecssors

method ComputeSlideDG(S: Statement, N: set<PDGNode>, E: set<PDGEdge>) returns (slideDG: SlideDG)


method ComputeSlide(S: Statement, v: Variable, l: Label) returns (n: Slide)

