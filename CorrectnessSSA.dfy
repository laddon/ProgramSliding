include "Definitions.dfy"
include "Substitutions.dfy"
include "RE.dfy"
include "Util.dfy"
include "Laws.dfy"

function ToSSALeft(S: Statement, XL3i: seq<Variable>, XL4f: seq<Variable>, XL5f: seq<Variable>, 
	X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL3i+XL4f+XL5f+Y,SeqComp(S,Assignment(XL3i+XL4f+XL5f,seqVarToSeqExpr(X3+X4+X5))))
}

function ToSSARight(XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>,	
	X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, 
	S': Statement, XL4f: seq<Variable>, XL5f: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL3i+XL4f+XL5f+Y,SeqComp(Assignment(XL1i+XL2i+XL3i+XL4i,seqVarToSeqExpr(X1+X2+X3+X4)),S'))
}

// TODO: move to a more central/reusable location: Util? Definitions?
predicate mutuallyDisjoint3<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)
{
	|setOf(s1+s2+s3)| == |s1|+|s2|+|s3|
}

predicate mutuallyDisjoint4<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T>)
{
	|setOf(s1+s2+s3+s4)| == |s1|+|s2|+|s3|+|s4|
}

predicate mutuallyDisjoint5<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T>, s5: seq<T>)
{
	|setOf(s1+s2+s3+s4+s5)| == |s1|+|s2|+|s3|+|s4|+|s5|
}

predicate mutuallyDisjoint6<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>, s4: seq<T>, s5: seq<T>, s6: seq<T>)
{
	|setOf(s1+s2+s3+s4+s5+s6)| == |s1|+|s2|+|s3|+|s4|+|s5|+|s6|
}

predicate PreconditionsOfToSSA(S: Statement, S': Statement, X: set<Variable>, 
	XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>, 
	XL4f: seq<Variable>, XL5f: seq<Variable>, 
	X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>, 
	Y: seq<Variable>, XLs: set<Variable>)
{
	glob(S) <= X+setOf(Y)                                                                                    // P1
	&& mutuallyDisjoint5(X1,X2,X3,X4,X5) && setOf(X1+X2+X3+X4+X5) <= X                                       // P2
	&& mutuallyDisjoint6(XL1i,XL2i,XL3i,XL4i,XL4f,XL5f) && setOf(XL1i+XL2i+XL3i+XL4i+XL4f+XL5f) <= XLs       // P3
	&& X !! setOf(Y) && XLs !! X+setOf(Y)                                                                    // P4
	&& setOf(X1) !! setOf(X3) && setOf(X1+X3) !! def(S)                                                      // P5
	&& mutuallyDisjoint3(X2,X4,X5) && setOf(X2+X4+X5) <= def(S)                                              // P6
	&& mutuallyDisjoint4(X1,X2,X3,X4) && X * (setOf(X3+X4+X5)-ddef(S)+input(S)) <= setOf(X1+X2+X3+X4) // P7
}

predicate CorrectnessOfToSSA(S: Statement, S': Statement, X: set<Variable>,
	X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>,
	XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>,
	XL4f: seq<Variable>, XL5f: seq<Variable>, Y: seq<Variable>, XLs: set<Variable>)
	reads *
{
	PreconditionsOfToSSA(S,S',X,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,X1,X2,X3,X4,X5,Y,XLs) ==>
	Valid(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y)) && Valid(ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y)) &&
	EquivalentStatments(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y),ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y)) // Q1
	&& X !! glob(S') // Q2
}

lemma LemmaIfToSSAIsCorrect(B: BooleanExpression, S1: Statement, S2: Statement,
		X: set<Variable>, XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>,
		XL4f: seq<Variable>, XL5f: seq<Variable>, Y: seq<Variable>, XLs: set<Variable>,
		X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>,
		S1': Statement,	XL4t: seq<Variable>, XL5t: seq<Variable>, XL4e: seq<Variable>, XL5e: seq<Variable>,
		X4d1: seq<Variable>, X4d2: seq<Variable>, X4d1d2: seq<Variable>,
		XL4d1t: seq<Variable>, XL4d1e: seq<Variable>, XL4d1d2t: seq<Variable>, XL4d1d2e: seq<Variable>, XL4d2i: seq<Variable>,
		XL4d1i: seq<Variable>, XL4d2e: seq<Variable>, XLs': set<Variable>, XLs'': set<Variable>,
		S2': Statement)
	requires Core(S1) && Core(S2) && Core(S1') && Core(S2');
	requires input(IF(B,S1,S2)) * X <= setOf(X1+X2+X3+X4) <= X //TODO: justify
	requires |X1+X2+X3+X4| == |XL1i+XL2i+XL3i+XL4i| && setOf(X1+X2+X3+X4) !! setOf(XL1i+XL2i+XL3i+XL4i)
	requires var B' := BSubstitute(B,X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i);
		PreconditionsOfToSSA(IF(B,S1,S2),IF(B',S1',S2'),X,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,X1,X2,X3,X4,X5,Y,XLs) &&
		Valid(ToSSALeft(IF(B,S1,S2),XL3i,XL4f,XL5f,X3,X4,X5,Y)) &&
		Valid(ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,IF(B',S1',S2'),XL4f,XL5f,Y))
	requires mutuallyDisjoint6(XL4d1t,XL4d2e,XL4d1d2t,XL4d1d2e,XL5t,XL5e) && XLs !! setOf(XL4d1t+XL4d2e+XL4d1d2t+XL4d1d2e+XL5t+XL5e) &&
		XLs' == XLs+setOf(XL4d1t+XL4d2e+XL4d1d2t+XL4d1d2e+XL5t+XL5e) &&
		PreconditionsOfToSSA(S1,S1',X,XL1i,XL2i,XL3i,XL4i,XL4t,XL5t,X1,X2,X3,X4,X5,Y,XLs') &&
		CorrectnessOfToSSA(S1,S1',X,X1,X2,X3,X4,X5,XL1i,XL2i,XL3i,XL4i,XL4t,XL5t,Y,XLs')
	requires XLs'' == XLs' + (glob(S1') - setOf(Y)) &&
		PreconditionsOfToSSA(S2,S2',X,XL1i,XL2i,XL3i,XL4i,XL4e,XL5e,X1,X2,X3,X4,X5,Y,XLs'') &&
		CorrectnessOfToSSA(S2,S2',X,X1,X2,X3,X4,X5,XL1i,XL2i,XL3i,XL4i,XL4e,XL5e,Y,XLs'')
	ensures var B',S1'',S2'' := BSubstitute(B,X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i),
		SeqComp(S1',Assignment(XL4f+XL5f,seqVarToSeqExpr(XL4t+XL5t))),
		SeqComp(S2',Assignment(XL4f+XL5f,seqVarToSeqExpr(XL4e+XL5e)));
		CorrectnessOfToSSA(IF(B,S1,S2),IF(B',S1'',S2''),X,X1,X2,X3,X4,X5,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y,XLs)
{
	var B',S1'',S2'' := BSubstitute(B,X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i),
		SeqComp(S1',Assignment(XL4f+XL5f,seqVarToSeqExpr(XL4t+XL5t))),
		SeqComp(S2',Assignment(XL4f+XL5f,seqVarToSeqExpr(XL4e+XL5e)));
	var S,S' := IF(B,S1,S2),IF(B',S1'',S2'');
	var liveOnEntry,liveOnExit := setOf(XL1i+XL2i+XL3i+XL4i),setOf(XL3i+XL4f+XL5f);

	assume Valid(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y)) && Valid(ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y)) &&
		EquivalentStatments(ToSSALeft(S,XL3i,XL4f,XL5f,X3,X4,X5,Y),ToSSARight(XL1i,XL2i,XL3i,XL4i,X1,X2,X3,X4,S',XL4f,XL5f,Y));// by {

	assert X !! glob(S') by
	{
		assert glob(S') <= glob(S1') + glob(S2') + B'.1 + setOf(XL4f+XL5f) + setOf(XL4t+XL5t) + setOf(XL4e+XL5e) by { calc {
			glob(S');
		== { RE5(S'); }
			def(S') + input(S');
		==
			def(IF(B',S1'',S2'')) + input(IF(B',S1'',S2''));
		==
			def(S1'') + def(S2'') + input(IF(B',S1'',S2''));
		== { assert input(IF(B',S1'',S2'')) == B'.1 + input(S1'') + input(S2''); }
			def(S1'') + def(S2'') + B'.1 + input(S1'') + input(S2'');
		<=
			def(S1') + setOf(XL4f+XL5f) + def(S2') + B'.1 + input(S1') + setOf(XL4t+XL5t) + input(S2') + setOf(XL4e+XL5e);
		==
			def(S1') + input(S1') + def(S2') + input(S2') + B'.1 + setOf(XL4f+XL5f) + setOf(XL4t+XL5t) + setOf(XL4e+XL5e);
		== { assert def(S1') + input(S1') == glob(S1') by { RE5(S1'); } }
			glob(S1') + def(S2') + input(S2') + setOf(XL4f+XL5f) + B'.1 + setOf(XL4t+XL5t) + setOf(XL4e+XL5e);
		== { assert def(S2') + input(S2') == glob(S2') by { RE5(S2'); } }
			glob(S1') + glob(S2') + B'.1 + setOf(XL4f+XL5f) + setOf(XL4t+XL5t) + setOf(XL4e+XL5e);
		}}
		assert X !! glob(S1');
		assert X !! glob(S2');
		assert X !! B'.1;
		assert X !! setOf(XL4f+XL5f);
		assert X !! setOf(XL4t+XL5t);
		assert X !! setOf(XL4e+XL5e);
	}
}
/*
/*	
not sure about the parameters to D3, should figure it out and fix; and then
should show that the preconditions above indeed guarantee that the preconditions of D3 (below, after the appropriate parameter substitutions) all hold;
and finally show that the postcondition of D3 (again, with the appropriate substitution) guarantee that our postconditions hold.

D.3:
	Live(XL2f+Y,SeqComp(IF(B,S1,S2),Assignment(XL2f,seqVarToSeqExpr(X2))))
==
	Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B',S1',S2')))


*/
		var XL1i',XL2f',X1',X2' := setOf(XL1i+XL2i+XL3i+XL4i),X1+X2+X3+X4,
		assert TransformationD3Left(B,S1,S2,X2,XL2f,Y),TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y) && 
			EquivalentStatments(TransformationD3Left(B,S1,S2,X2,XL2f,Y),TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y)) by {
		TransformationD3(B,B',S1,S2,S1',S2',X1,X2,XL1i,XL2i,XL2f,Y);

/*
requires Valid(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'))) // P5
	requires Valid(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'))) // P4
	requires setOf(XL1i) !! B.1 // P3
	requires setOf(XL1i) !! setOf(X1) // P2
	requires |X1| == |XL1i|
	requires EquivalentBooleanExpressions(B',BSubstitute(B,X1,XL1i)) // P1

	requires Valid(TransformationD3Left(B,S1,S2,X2,XL2f,Y))
	requires Valid(TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
	ensures EquivalentStatments(TransformationD3Left(B,S1,S2,X2,XL2f,Y),
			TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
			*/
	}	
	assert setOf(X) !! glob(S'); // Q2
}*/

function TransformationD3Left(B: BooleanExpression, 
		S1: Statement, S2: Statement,
		X2: seq<Variable>,
		XL2f: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL2f+Y,SeqComp(IF(B,S1,S2),Assignment(XL2f,seqVarToSeqExpr(X2))))
}

function TransformationD3Right(B': BooleanExpression, 
		S1': Statement, S2': Statement,
		X1: seq<Variable>,
		XL1i: seq<Variable>, XL2f: seq<Variable>, Y: seq<Variable>): Statement
{
	Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B',S1',S2')))
}

lemma TransformationD3(B: BooleanExpression, B': BooleanExpression, 
		S1: Statement, S2: Statement, S1': Statement, S2': Statement,
		X1: seq<Variable>, X2: seq<Variable>,
		XL1i: seq<Variable>, XL2i: seq<Variable>, XL2f: seq<Variable>, Y: seq<Variable>)
	requires Valid(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'))) // P5
	requires Valid(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))))
	requires Valid(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1')))
	requires EquivalentStatments(Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))),
		Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'))) // P4
	requires setOf(XL1i) !! B.1 // P3
	requires setOf(XL1i) !! setOf(X1) // P2
	requires |X1| == |XL1i|
	requires EquivalentBooleanExpressions(B',BSubstitute(B,X1,XL1i)) // P1

	requires Valid(TransformationD3Left(B,S1,S2,X2,XL2f,Y))
	requires Valid(TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
	ensures EquivalentStatments(TransformationD3Left(B,S1,S2,X2,XL2f,Y),
			TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y))
{
	var T1 := TransformationD3Left(B,S1,S2,X2,XL2f,Y);
	var T2 := TransformationD3Right(B',S1',S2',X1,XL1i,XL2f,Y);
	forall P: Predicate ensures EquivalentPredicates(wp(T1,P),wp(T2,P)) {
		var P1 := wp(T1,P);
		var P2 := wp(T2,P);
		forall s: State | P1.0.requires(s) && P2.0.requires(s) ensures P1.0(s) == P2.0(s) {
			calc {
				wp(T2,P).0(s);
			== // def. of T2 and of TransformationD3Right
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B',S1',S2'))),P).0(s);
			== { assert B'.0(s) == BSubstitute(B,X1,XL1i).0(s); // from P1
						var IF1,IF1',V := IF(BSubstitute(B,X1,XL1i),S1',S2'),IF(B',S1',S2'),XL2f+Y;
						assert EquivalentStatments(IF1',IF1);
						var A1 := Assignment(XL1i,seqVarToSeqExpr(X1));
						var SC1,SC1' := SeqComp(A1,IF1),SeqComp(A1,IF1');
						assert EquivalentStatments(SC1',SC1) by { assert EquivalentStatments(IF1',IF1); Leibniz4(A1,IF1,IF1'); }
						assert EquivalentStatments(Live(V,SC1'),Live(V,SC1));
						}
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(BSubstitute(B,X1,XL1i),S1',S2'))),P).0(s);
			== { assert setOf(XL1i) !! setOf(X1); // P2
						Law18b(S1',S2',BSubstitute(B,X1,XL1i),[],XL1i,[],seqVarToSeqExpr(X1)); }
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(BSubstituteVbyE(BSubstitute(B,X1,XL1i),XL1i,seqVarToSeqExpr(X1)),S1',S2'))),P).0(s);
			== {// remove redundant (reversed) double sub.
					var B'' := BSubstituteVbyE(BSubstitute(B,X1,XL1i),XL1i,seqVarToSeqExpr(X1));
					assert EquivalentBooleanExpressions(B,B'') by { assert setOf(XL1i) !! B.1; /* P3 */ ReversedDoubleSubstitutions(B,X1,XL1i); }
					assert EquivalentStatments(IF(B,S1',S2'),IF(B'',S1',S2'));
					var A1,IF1,IF1',V := Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B,S1',S2'),IF(B'',S1',S2'),XL2f+Y;
					var SC1,SC2 := SeqComp(A1,IF1'),SeqComp(A1,IF1);
					assert EquivalentStatments(SC1,SC2) by { assert EquivalentStatments(IF1',IF1); Leibniz4(A1,IF1',IF1); }
					assert EquivalentStatments(Live(V,SC1),Live(V,SC2));
					}
				wp(Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),IF(B,S1',S2'))),P).0(s);
			== { assert setOf(XL1i) !! B.1; // P3
						Law3(Assignment(XL1i,seqVarToSeqExpr(X1)),S1',S2',B); } // distribute statement over IF
				wp(Live(XL2f+Y,IF(B,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'),SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'))),P).0(s);
			== { Law21(B,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'),SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'),XL2f+Y); } // propagate liveness info.
				wp(Live(XL2f+Y,IF(B,Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1')),
					Live(XL2f+Y,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2')))),P).0(s);
			== { var V := XL2f+Y;
						var T1 := Live(V,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2))));
						var T1' := Live(V,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S1'));
						assert EquivalentStatments(T1,T1'); // P4
						var T2 := Live(V,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2))));
						var T2' := Live(V,SeqComp(Assignment(XL1i,seqVarToSeqExpr(X1)),S2'));
						assert EquivalentStatments(T2,T2'); // P5
						var IF1,IF1' := IF(B,T1,T2),IF(B,T1',T2');
						assert EquivalentStatments(IF1',IF1);
						assert EquivalentStatments(Live(V,IF1'),Live(V,IF1));
					}
				wp(Live(XL2f+Y,IF(B,Live(XL2f+Y,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2)))),
					Live(XL2f+Y,SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2)))))),P).0(s);
			== { Law21(B,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2))),SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2))),XL2f+Y); } // remove liveness info.
				wp(Live(XL2f+Y,IF(B,SeqComp(S1,Assignment(XL2f,seqVarToSeqExpr(X2))),SeqComp(S2,Assignment(XL2f,seqVarToSeqExpr(X2))))),P).0(s);
			== { Law4(S1,S2,Assignment(XL2f,seqVarToSeqExpr(X2)),B); } // dist. IF over ";"
				wp(Live(XL2f+Y,SeqComp(IF(B,S1,S2),Assignment(XL2f,seqVarToSeqExpr(X2)))),P).0(s);
			== // def. of T1 and of TransformationD3Left
				wp(T1,P).0(s);
			}
		}
	}
}

//method TransformationD5(S: Statement, X: seq<Variable>, X: seq<Variable>) returns (S': Statement)

function IfToSSACorrectnessLeft(B: BooleanExpression, S1: Statement, S2: Statement,
		X3: seq<Variable>, X4: seq<Variable>, X5: seq<Variable>, // live-on-exit variables (the X2 of D.3)
		XL3i: seq<Variable>, XL4f: seq<Variable>, XL5f: seq<Variable>, // live-on-exit instances (the XL2f of D.3)
		Y: seq<Variable>): Statement
{
//	Live(XL3i+XL4f+XL5f+Y,SeqComp(IF(B,S1,S2),Assignment(XL3i+XL4f+XL5f,seqVarToSeqExpr(X3+X4+X5))))
	TransformationD3Left(B,S1,S2,X3+X4+X5,XL3i+XL4f+XL5f,Y)
//	Live(XL2f          +Y,SeqComp(IF(B,S1,S2),Assignment(XL2f          ,seqVarToSeqExpr(X2      ))))
}

function IfToSSACorrectnessRight(B': BooleanExpression, S1': Statement, S2': Statement,
		X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, // live-on-entry variables (the X1 of D.3)
		XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>, // live-on-entry instances (the XL1i of D.3)
		XL4f: seq<Variable>, XL5f: seq<Variable>, // along with XL1i: live-on-exit instances (the XL2f of D.3)
		Y: seq<Variable>): Statement
{
//	Live(XL3i+XL4f+XL5f+Y,SeqComp(Assignment(XL1i+XL2i+XL3i+XL4i,seqVarToSeqExpr(X1+X2+X3+X4)),IF(B',S1',S2')))
	TransformationD3Right(B',S1',S2',X1+X2+X3+X4,XL1i+XL2i+XL3i+XL4i,XL3i+XL4f+XL5f,Y)
//	Live(XL2f          +Y,SeqComp(Assignment(XL1i               ,seqVarToSeqExpr(X1         )),IF(B',S1',S2')))
}

lemma IfToSSACorrectness(B: BooleanExpression, S1: Statement, S2: Statement, B': BooleanExpression, S1': Statement, S2': Statement,
		X1: seq<Variable>, X2: seq<Variable>, X3: seq<Variable>, X4: seq<Variable>, // live-on-entry variables (the X1 of D.3)
		X5: seq<Variable>, // along with X3,X4: live-on-exit variables (the X2 of D.3)
		XL1i: seq<Variable>, XL2i: seq<Variable>, XL3i: seq<Variable>, XL4i: seq<Variable>, // live-on-entry instances (the XL1i of D.3)
		XL4f: seq<Variable>, XL5f: seq<Variable>, // along with XL1i: live-on-exit instances (the XL2f of D.3)
		Y: seq<Variable>)
	requires Valid(IfToSSACorrectnessLeft(B,S1,S2,X3,X4,X5,XL3i,XL4f,XL5f,Y))
	requires Valid(IfToSSACorrectnessRight(B',S1',S2',X1,X2,X3,X4,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y))
	ensures EquivalentStatments(IfToSSACorrectnessLeft(B,S1,S2,X3,X4,X5,XL3i,XL4f,XL5f,Y),
			IfToSSACorrectnessRight(B',S1',S2',X1,X2,X3,X4,XL1i,XL2i,XL3i,XL4i,XL4f,XL5f,Y))
