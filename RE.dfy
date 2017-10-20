include "Definitions.dfy"



//============================================================
//					*** RE1-RE5 ***
//============================================================


lemma RE1(S: Statement, W: set<Predicate>)
requires Valid(S)
ensures EquivalentPredicates( wp(S,((s1: State) requires forall Q :: Q in W ==> Q.0.requires(s1) => exists P: Predicate :: P.0.requires(s1) && P.0(s1), VarsOfPredicateSet(W))), (((s1: State) requires forall Q :: Q in W ==> Q.0.requires(s1) => exists P: Predicate :: P in W && wp.requires(S,P) && (wp(S,P)).0(s1), VarsOfPredicateSet(W))))

//EquivalentPredicates(wp(S,(((s1: State) requires P.0.requires(s1) => exists p: State :: P.0.requires(p) && P.0(p) && P2(p).0(s1)), P.1)),(((s1: State) requires P.0.requires(s1)=> exists p: State :: P.0.requires(p) && P.0(p) && wp.requires(S,P2(p)) && (wp(S,P2(p)).0(s1))),P.1);

//requires isUniversallyDisjunctive(wp(S,P))
//ensures isUniversallyDisjunctive(wp(SeqComp(L,S),P))
/*{
	// NEED TO UNDERSTAND THEN FIX
	/*calc{
		wp(SeqComp(L,S),P)
		== { L !! glob(P)}
		wp(S,P)
		== {proviso}
		(9P : P 2 Ps : wp.S.P)
		== {again, wp of locals}
		(9P : P 2 Ps : wp.“ |[var L ; S]| ”.P)
	}*/
}*/

lemma RE2( S: Statement,P: Predicate)
requires Valid(S)
ensures vars(wp(S,P)) <= vars(P) - ddef(S) + input(S)
{
	match S {
		case Assignment(LHS, RHS) =>  calc {
			vars(wp(S,P)); 
			== {/* wp of assignment */}
			vars(sub(P, LHS, RHS));
			<= {/* glob of normal sub */}
			vars(P)- setOf(LHS) + varsInExps(RHS);
			== {/* ddef of input of assignment */}
			vars(P)-ddef(S) + input(S);
		}
		case SeqComp(S1, S2) =>  calc {
			vars(wp(S,P)); 
			== {/* wp of SeqComp */ Leibniz(vars,wp(S,P),wp(S1,wp(S2,P)));}
			vars(wp(S1,wp(S2,P)));
			<= {RE2(S1,wp(S2,P));}
			vars(wp(S2,P)) - ddef(S1) + input(S1);
			<= {RE2(S2,P);}
			((vars(P) - ddef(S2)) + input(S2)) - ddef(S1) + input(S1);
			== {/* set theory: (a [ b) \ c = (a \ c) [ (b \ c) and (d \ e) \ f = d \ (e [ f ) */}
			(vars(P) - (ddef(S1) + ddef(S2))) + (input(S2) - ddef(S1)) + input(S1);
			== {/* ddef and input of SeqComp */}
			(vars(P) - ddef(SeqComp(S1,S2))) + input(SeqComp(S1,S2));
			== {/* definition of SeqComp */}
			(vars(P) - ddef(S)) + input(S);
		}
		case IF(B0, Sthen, Selse) => forall s:State { calc {
			vars(wp(S,P));
			== {/* IF definition */}
			vars(wp(IF(B0, Sthen, Selse),P));
			== {/* wp definitionof IF */Leibniz(vars,wp(IF(B0, Sthen, Selse),P),AND(IMPLIES(B0,wp(Sthen,P)), IMPLIES(NOT(B0),wp(Selse,P))));}
			vars(AND(IMPLIES(B0,wp(Sthen,P)), IMPLIES(NOT(B0),wp(Selse,P))));
			== {/* def. of glob; glob.B = glob.(¬B) */}
			B0.1 + vars(wp(Sthen,P)) + vars(wp(Selse,P));
			<= {/* proviso, twice */}
			B0.1 + (vars(P) - ddef(Sthen)) + input(Sthen) + (vars(P) - ddef(Selse)) + input(Selse);
			== {/* */}
			(vars(P) - ddef(Sthen)) + (vars(P) - ddef(Selse)) + input(Sthen) + input(Selse) + B0.1;
			== {/* set theory */}
			(vars(P) - (ddef(Sthen) /* common */* ddef(Selse))) + input(Sthen) + input(Selse) + B0.1;
			== {/* ddef and input of IF */}
			(vars(P) - ddef(IF(B0,Sthen,Selse))) + input(IF(B0,Sthen,Selse));
			== {/* IF definition */}
			vars(P) - ddef(S) + input(S);
		}
		}
		case DO(B,Sloop) => /* forall Q:Predicate { calc { 
			vars(wp(S,P));
			== {assert EquivalentPredicates(wp(S,P),AND(OR(B,P), OR(NOT(B), wp(Sloop, Q))));Leibniz(vars,wp(S,P),AND(OR(B,P), OR(NOT(B), wp(Sloop, Q))));} // maybe cuased by forall Q
			vars(AND(OR(B,P), OR(NOT(B), wp(Sloop, Q))));
			== {}
			vars(B) + vars(P) + vars(wp(Sloop, Q));
			<= {/*Proviso glob.(wp.S.Q) <= (glob.Q\ddef.S) + input.S */}
			vars(B) + vars(P) + (vars(Q) - ddef(Sloop)) + input(Sloop);
			<= {/*Set theory*/}
			vars(B) + vars(P) + vars(Q) + input(Sloop);
			<= {/*Proviso glob.Q <=  glob.P + glob.B + input.S*/}
			vars(B) + vars(P) + vars(B) + vars(P) + input(Sloop) + input(Sloop);
			== {/*Set theory*/}
			vars(B) + vars(P) + input(Sloop);
		}}*/		assume vars(wp(S,P)) <= vars(P) - ddef(S) + input(S);
		case Skip => calc {

		}
		case LocalDeclaration(L,S0) => calc {
			(vars(wp(S,P)));
			== {/* wp definition of LocalDeclaration */}
			vars(wp(S0,P)); 
			<= {RE2(S0,P);}
			(vars(P) - ddef(S0) + input(S0));
			== {LocalDecStrangers2(S,P);}
			(vars(P) - ddef(S) + input(S));
		} 
		case Live(L,S0) => assume vars(wp(S,P)) <= vars(P) - ddef(S) + input(S);
		case Assert(B) => calc {
			vars(wp(S,P));
			== // wp of Assertions
			vars(P)+B.1;
			== { assert ddef(S) == {}; assert input(S) == B.1; }
			vars(P) - ddef(S) + input(S);
		}
	}
}

lemma RE3( S: Statement,P: Predicate)
requires  def(S) !! vars(P)
requires Valid(S)
ensures EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPredicate(true))))
{
   
	match S {
		case Skip => forall s: State { calc {
		wp(S,P).0(s);
		== {IdentityOfAND(S,P);}
		wp(S,AND(P,ConstantPredicate(true))).0(s);
		== {ConjWp(S, P, ConstantPredicate(true));}
		AND(wp(S,P),wp(S,ConstantPredicate(true))).0(s);
		== {/*def of wp*/}
		AND(P,wp(S,ConstantPredicate(true))).0(s);
		}
		}

		case SeqComp(S1, S2) => forall s: State { calc {
		wp(S,P).0(s);
		== {}
		wp(SeqComp(S1, S2),P).0(s);
		== {/* wp of SeqComp */}
		wp(S1, wp(S2, P)).0(s);
		== {assert def(S2) !! vars(P);RE3(S2,P); Leibniz2(wp,wp(S2, P),AND(P,wp(S2,ConstantPredicate(true))),S1);}
		wp(S1, AND(P,wp(S2,ConstantPredicate(true)))).0(s);
		== {/* wp(S1) is finitely conjunctive */ConjWp(S1, P, wp(S2,ConstantPredicate(true)));}
		AND(wp(S1,P),wp(S1,wp(S2,ConstantPredicate(true)))).0(s);
		== {assert def(S1) !! vars(P);}
		AND(AND(P,wp(S1,ConstantPredicate(true))),wp(S1,wp(S2,ConstantPredicate(true)))).0(s);
		== {}
		AND(P,AND(wp(S1,ConstantPredicate(true)),wp(S1,wp(S2,ConstantPredicate(true))))).0(s);
		== {/* finitely conjunctive */ConjWp(S1, ConstantPredicate(true),wp(S2,ConstantPredicate(true)));}
		AND(P,wp(S1,AND(ConstantPredicate(true),wp(S2,ConstantPredicate(true))))).0(s);
		== {/* identity element of ^ */assert def(S2) !! vars(ConstantPredicate(true));RE3(S2,ConstantPredicate(true));Leibniz2(wp,wp(S2, ConstantPredicate(true)),AND(ConstantPredicate(true),wp(S2,ConstantPredicate(true))),S1);}
		AND(P,wp(S1,wp(S2,ConstantPredicate(true)))).0(s);
		== {/* wp of SeqComp */}
		AND(P,wp(SeqComp(S1, S2),ConstantPredicate(true))).0(s);
		== {/* definition of SeqComp */}
		AND(P,wp(S,ConstantPredicate(true))).0(s);
		}
		}

		case IF(B0, Sthen, Selse) => forall s: State { calc {
			wp(S,P).0(s);
			== {/* IF definition */}
			wp(IF(B0, Sthen, Selse),P).0(s);
			== {/* wp definition of IF */}
			AND(IMPLIES(B0,wp(Sthen,P)),IMPLIES(NOT(B0),wp(Selse,P))).0(s);
			== {/*proviso: def(IF) !! vars(P) => def(Sthen) !! vars(P) */}
			AND(IMPLIES(B0,AND(P,wp(Sthen,ConstantPredicate(true)))),IMPLIES(NOT(B0),wp(Selse,P))).0(s);
			== {/*proviso: def(IF) !! vars(P) => def(Selse) !! vars(P) */}
			AND(IMPLIES(B0,AND(P,wp(Sthen,ConstantPredicate(true)))),IMPLIES(NOT(B0),AND(P,wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [X => (Y && Z) == (X => Y) && (X => Z)] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(B0,wp(Sthen,ConstantPredicate(true)))),IMPLIES(NOT(B0),AND(P,wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [X => (Y && Z) == (X => Y) && (X => Z)] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(B0,wp(Sthen,ConstantPredicate(true)))),AND(IMPLIES(NOT(B0),P),IMPLIES(NOT(B0),wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [(A && B) && C == (A && C) && B] */}
			AND(AND(IMPLIES(B0,P),IMPLIES(NOT(B0),P)),AND(IMPLIES(B0,wp(Sthen,ConstantPredicate(true))),IMPLIES(NOT(B0),wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* pred. calc.: [Y => Z) && (!Y => Z) == Z] */}
			AND(P,AND(IMPLIES(B0,wp(Sthen,ConstantPredicate(true))),IMPLIES(NOT(B0),wp(Selse,ConstantPredicate(true))))).0(s);
			== {/* wp definition of IF */}
			AND(P,wp(IF(B0,Sthen,Selse),ConstantPredicate(true))).0(s);
			== {/* IF definition */}
			AND(P,wp(S,ConstantPredicate(true))).0(s);
		}
		}

		case DO(B,Sloop) => /*forall s: State { calc {
		wp(S,P)(s);
		== {}
		AND(P, wp(S,ConstantPrdicate(true)))(s);
		}
		}*/
		assume EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPredicate(true))));
		
		case LocalDeclaration(L,S0) => forall s: State { calc {
			wp(S,P).0(s);
			== {assert setOf(L) !! vars(P) by {LocalDecStrangers(S,P);}}
			wp(S0,P).0(s);
			== {assert vars(P) !! def(S0) by {assert def(S) !! vars(P);assert setOf(L) !! vars(P) by {LocalDecStrangers(S,P); }}RE3(S0,P);/**/}
			AND(P, wp(S0,ConstantPredicate(true))).0(s);
			== {} 
			AND(P, wp(S,ConstantPredicate(true))).0(s); 
		}
		}
		
		case Assignment(LHS, RHS) => forall s: State { calc {
		(AND(P,wp(S,ConstantPredicate(true)))).0(s);
		== {/* wp of assignment */}
		(AND(P,sub(ConstantPredicate(true), LHS, RHS))).0(s);
		== {assert setOf(LHS) !! vars(ConstantPredicate(true));}
		(AND(P,ConstantPredicate(true))).0(s);
		== {/* identity element of ^ */}
		P.0(s);
		== {assert setOf(LHS) !! vars(P);SubDefinitionLemma(P,LHS,RHS,s);}
		sub(P, LHS, RHS).0(s);
		== {/* wp of assignment */}
		wp(S,P).0(s);
		}
		}
		
		// FIXME: complete proof for the following extended constructs...
		case Live(L, S0) => assume EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPredicate(true))));		
		case Assert(B) => assume EquivalentPredicates(wp(S,P), AND(P, wp(S,ConstantPredicate(true))));		
	}
}




lemma RE4(S: Statement)
//	requires ddef(S) <= def(S)
//	ensures S.LocalDeclaration? ==> ddef(S) <= def(S)

lemma RE5(S: Statement)
	ensures glob(S) == def(S) + input(S)
	//ensures S.LocalDeclaration? ==> vars(SeqComp(L,S)) == def(SeqComp(L,S)) + input(SeqComp(L,S))
/*{
	match S{
		case LocalDeclaration(L,S1) => calc{
			glob(S); 
			==
			glob(S1);
			== {/*glob of locals;*/}
			def(S1) + input(S1);
			== {/*def and input of locals*/}
			def(S) + input(S);
		}
	}
}
*/
 

