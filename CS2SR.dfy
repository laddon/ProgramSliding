include "Definitions.dfy"

//============================================================
//					*** Convert Statement to C# Program ***
//============================================================

function ConvertStatment2CS(S: Statement): string
{   
   match stmt
   {
		case Skip => return ""
		case Assignment(LHS,RHS) => return ConvertAssignment(LHS,RHS)
		case SeqComp(S1,S2) => return ConvertStatment2CS(S1) + ConvertStatment2CS(S2)
		case IF(B0,Sthen,Selse) => return ConvertIFStatment2CS(B0,Sthen,Selse)
		case DO(B,Sloop) => return ConvertDOStatment2CS(B,Sloop)
		case LocalDeclaration(L,S0) => return ConvertStatment2CS(S0)
		case Live(L, S0) => return ConvertStatment2CS(S0)
		case Assert(B) => return ""
   }
}

function ConvertAssignment(LHS: seq<Variable>, RHS: seq<Expression>): string
{
    if ((|LHS| > 1) && (|RHS| > 1)) then
		LHS[0] + " = " + RHS[0] + " ;\n" + ConvertAssignment(LHS[1..],RHS[1..])
	else if ((|LHS| > 0) && (|RHS| > 0)) then
		LHS[0] + " = " + RHS[0] + " ;\n"
	else
		""
}

function ConvertIFStatment2CS(B0: BooleanExpression, Sthen: Statement, Selse: Statement): string
{
    return "IF (" + B0 + ")\n{\n" +  ConvertStatment2CS(Sthen) + "else\n{\n" + ConvertStatment2CS(Selse) + "}\n}";
}

function ConvertDOStatment2CS(B: BooleanExpression, Sloop: Statement): string
{
    return "WHILE (" + B + ")\n{\n" +  ConvertStatment2CS(Sloop) + "}";
}