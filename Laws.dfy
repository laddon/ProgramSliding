include "Definitions.dfy"
include "Substitutions.dfy"

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

function Law16Left(S: Statement, B1: BooleanExpression, B2: BooleanExpression): Statement
{
	SeqComp(Assert(B1),DO(B2,S))
}

function Law16Right(S: Statement, B1: BooleanExpression, B2: BooleanExpression): Statement
{
	SeqComp(Assert(B1),DO(B2,SeqComp(Assert(B1),S)))
}

lemma Law16(S: Statement, B1: BooleanExpression, B2: BooleanExpression)
	requires Valid(Law16Left(S,B1,B2))
	requires Valid(Law16Right(S,B1,B2))
	requires B1.1 !! def(S)
	ensures EquivalentStatments(Law16Left(S,B1,B2),Law16Right(S,B1,B2))

function Law17aLeft(X: seq<Variable>, E: seq<Expression>, Y: seq<Variable>, Y': seq<Variable>): Statement
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
{
	SeqComp(EqualityAssertion(Y,seqVarToSeqExpr(Y')),Assignment(X,E))
}

function Law17aRight(X: seq<Variable>, E: seq<Expression>, Y: seq<Variable>, Y': seq<Variable>): Statement
	reads *
	requires |Y| == |Y'|
	requires setOf(Y) !! setOf(Y')
{
	var E' := ESeqSubstitute(E,Y,Y');
	SeqComp(EqualityAssertion(Y,seqVarToSeqExpr(Y')),Assignment(X,E'))
}

lemma Law17a(X: seq<Variable>, E: seq<Expression>, Y: seq<Variable>, Y': seq<Variable>)
	requires |Y| == |Y'|
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
	requires setOf(Y) !! setOf(Y')
	requires Valid(Law17aLeft(X,E,Y,Y'))
	requires Valid(Law17aRight(X,E,Y,Y'))
	ensures EquivalentStatments(Law17aLeft(X,E,Y,Y'),Law17aRight(X,E,Y,Y'))

function Law17bLeft(S1: Statement, S2: Statement, B: BooleanExpression, Y: seq<Variable>, Y': seq<Variable>): Statement
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
{
	SeqComp(EqualityAssertion(Y,seqVarToSeqExpr(Y')),IF(B,S1,S2))
}

function Law17bRight(S1: Statement, S2: Statement, B: BooleanExpression, Y: seq<Variable>, Y': seq<Variable>): Statement
	reads *
	requires |Y| == |Y'|
	requires setOf(Y) !! setOf(Y')
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
{
	SeqComp(EqualityAssertion(Y,seqVarToSeqExpr(Y')),IF(BSubstitute(B,Y,Y'),S1,S2))
}

lemma Law17b(S1: Statement, S2: Statement, B: BooleanExpression, Y: seq<Variable>, Y': seq<Variable>)
	requires |Y| == |Y'|
	requires setOf(Y) !! setOf(Y')
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
	requires Valid(Law17bLeft(S1,S2,B,Y,Y'))
	requires Valid(Law17bRight(S1,S2,B,Y,Y'))
	ensures EquivalentStatments(Law17bLeft(S1,S2,B,Y,Y'),Law17bRight(S1,S2,B,Y,Y'))

function Law17cLeft(S1: Statement, B: BooleanExpression, Y: seq<Variable>, Y': seq<Variable>): Statement
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
{
	var Inv := EqualityAssertion(Y,seqVarToSeqExpr(Y'));
	SeqComp(Inv,DO(B,SeqComp(S1,Inv)))
}

function Law17cRight(S1: Statement, B: BooleanExpression, Y: seq<Variable>, Y': seq<Variable>): Statement
	reads *
	requires |Y| == |Y'|
	requires setOf(Y) !! setOf(Y')
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
{
	var Inv := EqualityAssertion(Y,seqVarToSeqExpr(Y'));
	SeqComp(Inv,DO(BSubstitute(B,Y,Y'),SeqComp(S1,Inv)))
}

lemma Law17c(S1: Statement, B: BooleanExpression, X: seq<Variable>, E: seq<Expression>, Y: seq<Variable>, Y': seq<Variable>)
	requires |Y| == |Y'|
	requires setOf(Y) !! setOf(Y') // TODO: remove this - after removing it from the precondition of the substitution
	requires ValidAssignment(Y,seqVarToSeqExpr(Y'))
	requires Valid(Law17cLeft(S1,B,Y,Y'))
	requires Valid(Law17cRight(S1,B,Y,Y'))
	ensures EquivalentStatments(Law17cLeft(S1,B,Y,Y'),Law17cRight(S1,B,Y,Y'))

function Law18aLeft(X: seq<Variable>, Y: seq<Variable>, Z: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>, E3: seq<Expression>): Statement
	requires |X| == |E1| && |Y| == |E2| && |Z| == |E3|
{
	SeqComp(Assignment(X+Y,E1+E2),Assignment(Z,E3))
}

function Law18aRight(X: seq<Variable>, Y: seq<Variable>, Z: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>, E3: seq<Expression>): Statement
	reads *
	requires |X| == |E1| && |Y| == |E2| && |Z| == |E3|
{
	SeqComp(Assignment(X+Y,E1+E2),Assignment(Z,ESeqSubstituteVbyE(E3,Y,E2)))
}

lemma Law18a(X: seq<Variable>, Y: seq<Variable>, Z: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>, E3: seq<Expression>)
	requires |X| == |E1| && |Y| == |E2| && |Z| == |E3|
	requires Valid(Law18aLeft(X,Y,Z,E1,E2,E3))
	requires Valid(Law18aRight(X,Y,Z,E1,E2,E3))
	requires setOf(X) !! setOf(Y)
	requires setOf(X) + setOf(Y) !! varsInExps(E2)
	ensures EquivalentStatments(Law18aLeft(X,Y,Z,E1,E2,E3),Law18aRight(X,Y,Z,E1,E2,E3))

function Law18bLeft(S1: Statement, S2: Statement, B: BooleanExpression, X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>): Statement
	requires |X| == |E1| && |Y| == |E2|
{
	SeqComp(Assignment(X+Y,E1+E2),IF(B,S1,S2))
}

function Law18bRight(S1: Statement, S2: Statement, B: BooleanExpression, X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>): Statement
	reads *
	requires |X| == |E1| && |Y| == |E2|
{
	SeqComp(Assignment(X+Y,E1+E2),IF(BSubstituteVbyE(B,Y,E2),S1,S2))
}

lemma Law18b(S1: Statement, S2: Statement, B: BooleanExpression, X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>)
	requires |X| == |E1| && |Y| == |E2|
	requires Valid(Law18bLeft(S1,S2,B,X,Y,E1,E2))
	requires Valid(Law18bRight(S1,S2,B,X,Y,E1,E2))
	requires setOf(X) !! setOf(Y)
	requires setOf(X) + setOf(Y) !! varsInExps(E2)
	ensures EquivalentStatments(Law18bLeft(S1,S2,B,X,Y,E1,E2),Law18bRight(S1,S2,B,X,Y,E1,E2))

function Law18cLeft(S1: Statement, B: BooleanExpression, X: seq<Variable>, X': seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E1': seq<Expression>, E2: seq<Expression>): Statement
	requires |X| == |E1| && |Y| == |E2| && |X'| == |E1'|
{
	SeqComp(Assignment(X+Y,E1+E2),DO(B,SeqComp(S1,Assignment(X',E1'))))
}

function Law18cRight(S1: Statement, B: BooleanExpression, X: seq<Variable>, X': seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E1': seq<Expression>, E2: seq<Expression>): Statement
	reads *
	requires |X| == |E1| && |Y| == |E2| && |X'| == |E1'|
{
	SeqComp(Assignment(X+Y,E1+E2),DO(BSubstituteVbyE(B,Y,E2),SeqComp(S1,Assignment(X',E1'))))
}

lemma Law18c(S1: Statement, B: BooleanExpression, X: seq<Variable>, X': seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E1': seq<Expression>, E2: seq<Expression>)
	requires |X| == |E1| && |Y| == |E2| && |X'| == |E1'|
	requires Valid(Law18cLeft(S1,B,X,X',Y,E1,E1',E2))
	requires Valid(Law18cRight(S1,B,X,X',Y,E1,E1',E2))
	requires setOf(X) + setOf(X') !! setOf(Y)
	requires setOf(X) + setOf(X') + setOf(Y) !! varsInExps(E2)
	ensures EquivalentStatments(Law18cLeft(S1,B,X,X',Y,E1,E1',E2),Law18cRight(S1,B,X,X',Y,E1,E1',E2))

// Live variables analysis

/// Introduction and removal of liveness information

lemma Law19(S: Statement, V: seq<Variable>)
	requires Valid(S)
	requires Valid(Live(V,S))
	requires def(S) <= setOf(V)
	ensures EquivalentStatments(S,Live(V,S))

/// Propagation of liveness information

lemma Law20(S1: Statement, S2: Statement, V1: seq<Variable>, V2: seq<Variable>)
	requires Valid(Live(V1,SeqComp(S1,S2)))
	requires Valid(Live(V1,SeqComp(Live(V2,S1),Live(V1,S2))))
	requires setOf(V2) == setOf(V1) - ddef(S2) + input(S2)
	ensures EquivalentStatments(Live(V1,SeqComp(S1,S2)),Live(V1,SeqComp(Live(V2,S1),Live(V1,S2))))

lemma Law21(B: BooleanExpression, S1: Statement, S2: Statement, V: seq<Variable>)
	requires Valid(Live(V,IF(B,S1,S2)))
	requires Valid(Live(V,IF(B,Live(V,S1),Live(V,S2))))
	ensures EquivalentStatments(Live(V,IF(B,S1,S2)),Live(V,IF(B,Live(V,S1),Live(V,S2))))

lemma Law22(B: BooleanExpression, S: Statement, V1: seq<Variable>, V2: seq<Variable>)
	requires Valid(Live(V1,DO(B,S)))
	requires Valid(Live(V1,DO(B,Live(V2,S))))
	requires setOf(V2) == setOf(V1) + B.1 + input(S)
	ensures EquivalentStatments(Live(V1,DO(B,S)),Live(V1,DO(B,Live(V2,S))))

/// Dead assignments: introduction and elimination

lemma Law23(S: Statement, V: seq<Variable>, X: seq<Variable>, Y: seq<Variable>, E1: seq<Expression>, E2: seq<Expression>)
	requires |X| == |E1| && |Y| == |E2|
	requires Valid(Live(V,SeqComp(S,Assignment(X,E1))))
	requires Valid(Live(V,SeqComp(S,Assignment(X+Y,E1+E2))))
	requires setOf(Y) == setOf(X) + setOf(V)
	ensures EquivalentStatments(Live(V,SeqComp(S,Assignment(X,E1))),Live(V,SeqComp(S,Assignment(X+Y,E1+E2))))

