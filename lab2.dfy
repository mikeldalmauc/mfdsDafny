// EXERCISE 0
// m <- maximo de dos numers
// S <- suma de eos dos numeros
// Resultado la suma de esos dos numeros
method MaxSumaBackwards(m:nat, s:nat) returns (x:nat, y:nat)
    requires 2*m >= s >= m;
    ensures x + y == s;
    ensures m >= x && m >= y
    ensures m == x || m == y
{
    x:= m;
    y:= s-m;
}

// method Main()
//     decreases *;
// {
//     var max, other := MaxSumaBackwards(7,12);
    
//     print max;
//     print "\n";
//     print other;

//     while true 
//         decreases * ;
//     {}
// }

function fact (n:int):int
	requires n >= 0
	decreases n				    
{
if n == 0 then 1 else n * fact(n-1)
}

// EXERCISE 1
// This is the method that appears in the lecture slides.
method factorial1 (n:int) returns (f:int)
	requires n >= 0
	ensures f == fact(n)
{
var x := n; 
f := 1;
//assert 1*fact(n) == fact(n);
while x > 0
    invariant 0 <= x <= n;
    invariant f * fact(x) == fact(n);
    // decreases x; 
	{
		// assert ;
	f := x * f;
		// assert ;
	x := x - 1;
	}
}

// Write invariants, assert and termination metrics (although Dafny guess it) for the following two programs:

// EXERCISE 2

method factorial2 (n:int) returns (f:int)
	requires n >= 0
	ensures f == fact(n)
{
var x := 1; 
f := 1;
while x <= n
     invariant 1 <= x <= n +1
	 invariant  f == fact(x-1);
	{
		assert f*x == fact(x);
	f := f * x;
		 assert f == fact(x); 
	x := x + 1;
	}

}


// EXERCISE 3
method factoial3 (n:int) returns (f:int)
	requires n >= 0
	ensures f == fact(n)
{
	var x:int := 0; 
	f := 1;
	while x < n
		invariant 0 <= x <= n
		invariant f == fact(x)
		{
		// 	assert 0<=x+1 && f*(x+1) == fact(x+1);
		// x := x + 1;
		// 	assert 0<=x<=n && f*x == fact(x);
		// f := f * x;
		// 	assert 0<=x<=n && f == fact(x);

			x,f := x+1,f*(x+1);
		}
}


// EXERCISE 4
// Write a method Main that calculates the first 11 factorials and shows the results.

method Main ()
{
	var i:= 0;
	var f:= 0;
	while i < 11
	invariant 0 <= i <= 11
	{
	   f := factoial3(i);
		print "factoria de ", i, " = ", f , "\n";
	   i := i + 1;
	}
}
// EXERCISE 5
// Verify the following recursive method that calculates the number of combinations of m elements out of n,
// that is the combinatorial number "m over n".

method combinations (m:int, n:int) returns (r:int)
 	decreases  m, n
	requires m >= n >= 0
	ensures  r == combinations'(m,n)
{
if n == 0 || n == m  { r := 1; }
else { 
     var raux1 := combinations(m-1,n-1);
	 	//assert  raux1*fact(n-1)*fact(m-n) == fact(m-1); // H.I
	 var raux2 := combinations(m-1,n);
	 	// assert raux2*fact(n)*fact(m-n-1) == fact(m-1); // H.I 2
	 
	 	// assert (raux1 + raux2)* fact(n) * fact(m-n) == fact(m);
	 r := raux1 + raux2;
		// assert  r * fact(n) * fact(m-n) == fact(m);
	 }
}

function combinations' (m:int, n:int):int
 	decreases  m, n
	requires m >= n >= 0
	//ensures  r * fact(n) * fact(m-n) == fact(m)  
{
	if n == 0 || n == m 
	then 1 
	else combinations'(m-1,n-1) + combinations'(m-1,n)
}

lemma comb_Lemma(m:int, n:int)
	requires m>=n>=0
	ensures combinations'(m,n) * fact(n) * fact(m-n) == fact(m)  
{}
// EXERCISE 6
// Define a function sumSerie(n:int):int such that 
// (informally) sumSerie(n) == 1 + 3 + ... + (2*n - 1)

function sumSerie(n:int):int
	decreases n
	requires n>=1
	{
		if n == 1 then 1 else 2*n-1 + sumSerie(n-1)
	}
/*
Define and prove (even if Dafny proves it automatically)
the lemma "Lemma_Square" that helps Dafny proving the contract of the following method.
*/

lemma Lemma_Square(n:int)
	requires n >= 1
	ensures sumSerie(n) == n*n
{}

method Square (a:int) returns (x:int)
	requires a >= 1
	ensures x == a*a
{
	x := 0;
	var y := 0;
	while  y < a
		invariant 0 <= y <= a
		invariant y>0 ==> x == sumSerie(y)
		invariant y == 0 ==> x == 0
		{
			//assert y+1 > 0;
			//assert y>0 ==> x == sumSerie(y);
			//assert y+1>0 ==> x + 2*(y+1) -1 == x + 2*y + 1 == sumSerie(y+1);
			y := y+1;
			//assert y>0 ==> x + 2*y - 1 == sumSerie(y);
			x := x + 2*y - 1;
			//assert x == sumSerie(y);
		}
	//assert x == sumSerie(a);
	Lemma_Square(a);
}






