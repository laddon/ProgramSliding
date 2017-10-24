	
function method digitToString(num: int) : (res : string)
requires num >= 0 && num <= 9
ensures res == "0" 
	|| res == "1" 
	|| res == "2" 
	|| res == "3" 
	|| res == "4" 
	|| res == "5" 
	|| res == "6" 
	|| res == "7" 
	|| res == "8" 
	|| res == "9"
{
	if num == 0 then "0"
	else if num == 1 then "1"
	else if num == 2 then "2"
	else if num == 3 then "3"
	else if num == 4 then "4"
	else if num == 5 then "5"
	else if num == 6 then "6"
	else if num == 7 then "7"
	else if num == 8 then "8"
	else "9"
}

function method intToString(num: int) : (res: string)
requires num >= 0
ensures forall c :: c in res ==> '\u0030' <= c <= '\u0039'
{
	if num >= 0 && num <= 9 then digitToString(num)
	else
		intToString(num / 10) + digitToString(num % 10)
		
}

/* res := X*Y */
function method {:verify true} seqConjunction<T(==)>(X: seq<T>, Y: seq<T>) : (res: seq<T>)
requires uniqueness(X)
requires uniqueness(Y)
ensures forall i :: i in res ==> i in X && i in Y
ensures forall i :: i !in res ==> i !in X || i !in Y
{
	if X == [] || Y == [] then []
	else if X[0] in Y then [X[0]]+seqConjunction(X[1..], Y)
	else seqConjunction(X[1..], Y)
}


/* res := X-Y */
function method {:verify true} seqSubtraction<T(==)>(X: seq<T>, Y: seq<T>) : (res: seq<T>)
requires uniqueness(X)
requires uniqueness(Y)
decreases X
ensures forall i :: i in res ==> i in X && i !in Y
ensures forall i :: i !in res ==> i !in X || i in Y
{
	if X == [] then []
	else if Y == [] then X
	else if X[0] in Y then seqSubtraction(X[1..], Y)
	else [X[0]]+seqSubtraction(X[1..], Y)
}

predicate uniqueness<T(==)>(X: seq<T>)
{
	(forall i,j :: i in X && j in X && i != j) ==> true
}
