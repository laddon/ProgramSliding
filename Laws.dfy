include "Definitions.dfy"

// Laws for manipulating core statements
lemma Law1(X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>,E2: seq<Expression>)
	requires Valid(Assignment(X,E1))
	requires Valid(Assignment(Y,E2))
	requires setOf(X) !! setOf(Y) + varsInExps(E1)
	ensures var S1 := Assignment(X,E1); var S2 := Assignment(Y,E2);
		EquivalentStatments(SeqComp(S1,S2), SeqComp(S2,S1))

lemma Law2(S: Statement, X: set<Variable>)
	requires Valid(S)
	ensures var LHS := fSetToSeq(X); var RHS := seqVarToSeqExpr(LHS);
		EquivalentStatments(S, SeqComp(S, Assignment(LHS,RHS)))

lemma Law3(S: Statement, S1: Statement, S2: Statement, B: BooleanExpression)
	requires Valid(SeqComp(S, IF(B, S1, S2)))
	requires Valid(IF(B, SeqComp(S,S1), SeqComp(S,S2)))
	requires def(S) !! vars(B)
	ensures EquivalentStatments(SeqComp(S, IF(B, S1, S2)), IF(B, SeqComp(S,S1), SeqComp(S,S2)))
