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


// Assertion-based program analysis

/// Introduction of assertions

lemma Law7(X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>,E2: seq<Expression>)
	requires ValidAssignment(Y,E2)
	requires var S := Assignment(X+Y,E1+E2);
		Valid(S) && Valid(SeqComp(S,EqualityAssertion(Y,E2)))
	requires setOf(X) !! setOf(Y) // TODO: this should follow from the above, with X+Y being the LHS of an assignment, yet this is not yet formulated in ValidAssignment
	requires setOf(X) + setOf(Y) !! varsInExps(E2)
	ensures var S := Assignment(X+Y,E1+E2);
		EquivalentStatments(S, SeqComp(S,EqualityAssertion(Y,E2)))

lemma Law8(X: seq<Variable>, X': seq<Variable>, E: seq<Expression>)
	requires ValidAssignment(X,E)
	requires ValidAssignment(X',E)
	requires var S := Assignment(X+X',E+E);
		Valid(S) && Valid(SeqComp(S,EqualityAssertion(X,seqVarToSeqExpr(X'))))
	requires setOf(X) !! setOf(X')
	ensures var S := Assignment(X+X',E+E);
		EquivalentStatments(S, SeqComp(S,EqualityAssertion(X,seqVarToSeqExpr(X'))))

lemma Law9(S1: Statement, B1: BooleanExpression, B2: BooleanExpression)
	requires Valid(DO(B1,S1))
	requires Valid(DO(B1,SeqComp(Assert(B2),S1)))
	requires forall state :: B1.0.requires(state) && B1.0(state) ==> B2.0.requires(state) && B2.0(state)
	ensures EquivalentStatments(DO(B1,S1),DO(B1,SeqComp(Assert(B2),S1)))

/// Propagation of assertions

lemma Law11(S: Statement, B: BooleanExpression)
	requires Valid(SeqComp(Assert(B),S))
	requires Valid(SeqComp(S,Assert(B)))
	requires def(S) !! B.1
	ensures EquivalentStatments(SeqComp(Assert(B),S),SeqComp(S,Assert(B)))

lemma Law12(S1: Statement, S2: Statement, B1: BooleanExpression, B2: BooleanExpression)
	requires Valid(SeqComp(Assert(B1),IF(B2,S1,S2)))
	requires Valid(IF(B2,SeqComp(Assert(B1),S1),SeqComp(Assert(B1),S2)))
	ensures EquivalentStatments(SeqComp(Assert(B1),IF(B2,S1,S2)),IF(B2,SeqComp(Assert(B1),S1),SeqComp(Assert(B1),S2)))

function Law13Left(S: Statement, B1: BooleanExpression, B2: BooleanExpression, B3: BooleanExpression): Statement
{
	SeqComp(Assert(B1),DO(B2,SeqComp(S,Assert(B3))))
}

function Law13Right(S: Statement, B1: BooleanExpression, B2: BooleanExpression, B3: BooleanExpression, B4: BooleanExpression): Statement
{
	SeqComp(Assert(B1),DO(B2,SeqComp(Assert(B4),SeqComp(S,Assert(B3)))))
}

lemma Law13(S: Statement, B1: BooleanExpression, B2: BooleanExpression, B3: BooleanExpression, B4: BooleanExpression)
	requires Valid(Law13Left(S,B1,B2,B3))
	requires Valid(Law13Right(S,B1,B2,B3,B4))
	requires forall state :: B1.0.requires(state) && B1.0(state) ==> B4.0.requires(state) && B4.0(state)
	requires forall state :: B3.0.requires(state) && B3.0(state) ==> B4.0.requires(state) && B4.0(state)
	ensures EquivalentStatments(Law13Left(S,B1,B2,B3),Law13Right(S,B1,B2,B3,B4))

function Law14Left(S: Statement, B1: BooleanExpression, B2: BooleanExpression, B3: BooleanExpression): Statement
{
	SeqComp(Assert(B1),DO(B2,SeqComp(S,Assert(B3))))
}

function Law14Right(S: Statement, B1: BooleanExpression, B2: BooleanExpression, B3: BooleanExpression, B4: BooleanExpression): Statement
{
	var B2andB4 := (state reads * requires B2.0.requires(state) && B4.0.requires(state) => B2.0(state) && B4.0(state), B2.1+B4.1);
	SeqComp(Assert(B1),DO(B2andB4,SeqComp(S,Assert(B3))))
}

lemma Law14(S: Statement, B1: BooleanExpression, B2: BooleanExpression, B3: BooleanExpression, B4: BooleanExpression)
	requires Valid(Law14Left(S,B1,B2,B3))
	requires Valid(Law14Right(S,B1,B2,B3,B4))
	requires forall state :: B1.0.requires(state) && B1.0(state) ==> B4.0.requires(state) && B4.0(state)
	requires forall state :: B3.0.requires(state) && B3.0(state) ==> B4.0.requires(state) && B4.0(state)
	ensures EquivalentStatments(Law14Left(S,B1,B2,B3),Law14Right(S,B1,B2,B3,B4))


function Law15Left(B1: BooleanExpression, B2: BooleanExpression): Statement
{
	var B1andB2 := (state reads * requires B1.0.requires(state) && B2.0.requires(state) => B1.0(state) && B2.0(state), B1.1+B2.1);
	Assert(B1andB2)
}

function Law15Right(B1: BooleanExpression, B2: BooleanExpression): Statement
{
	SeqComp(Assert(B1),Assert(B2))
}

lemma Law15(B1: BooleanExpression, B2: BooleanExpression)
	requires Valid(Law15Left(B1,B2))
	requires Valid(Law15Right(B1,B2))
	ensures EquivalentStatments(Law15Left(B1,B2),Law15Right(B1,B2))
