include "Definitions.dfy"

// Laws for manipulating core statements
lemma Law1(X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>,E2: seq<Expression>)
	requires Valid(Assignment(X,E1))
	requires Valid(Assignment(Y,E2))
	requires setOf(X) !! setOf(Y) + varsInExps(E1)
	ensures var S1 := Assignment(X,E1); var S2 := Assignment(Y,E2);
		EquivalentStatments(SeqComp(S1,S2), SeqComp(S2,S1))
