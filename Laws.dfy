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

lemma Law4(S1: Statement, S2: Statement, S3: Statement, B: BooleanExpression)
	requires Valid(SeqComp(IF(B, S1, S2), S3))
	requires Valid(IF(B, SeqComp(S1,S3), SeqComp(S2,S3)))
	ensures EquivalentStatments(SeqComp(IF(B, S1, S2), S3), IF(B, SeqComp(S1,S3), SeqComp(S2,S3)))

function Law5Left(S1: Statement, X: seq<Variable>, B: BooleanExpression, E: seq<Expression>): Statement
	requires ValidAssignment(X,E)
{
	var S0 := EqualityAssertion(X,E);
	var S2 := Assignment(X,E);
	SeqComp(S0,DO(B,SeqComp(S1,S2)))
}

function Law5Right(S1: Statement, X: seq<Variable>, B: BooleanExpression, E: seq<Expression>): Statement
	requires ValidAssignment(X,E)
{
	var S0 := EqualityAssertion(X,E);
	var S2 := Assignment(X,E);
	SeqComp(S0,SeqComp(DO(B,S1),S2))
}

lemma Law5(S1: Statement, X: seq<Variable>, B: BooleanExpression, E: seq<Expression>)
	requires ValidAssignment(X,E)
	requires Valid(Law5Left(S1,X,B,E))
	requires Valid(Law5Right(S1,X,B,E))
	requires setOf(X) !! B.1 + input(S1) + varsInExps(E)
	ensures EquivalentStatments(Law5Left(S1,X,B,E),Law5Right(S1,X,B,E))

lemma Law6(X: seq<Variable>, E: seq<Expression>)
	requires Valid(Assignment(X,E))
	ensures var assertion := EqualityAssertion(X,E);
		EquivalentStatments(assertion,SeqComp(assertion, Assignment(X,E)))

