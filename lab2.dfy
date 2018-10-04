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

method Main()
    decreases *;
{
    var max, other := MaxSumaBackwards(7,12);
    
    print max;
    print "\n";
    print other;

    while true 
        decreases * ;
    {}
}

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
/*
method factorial3 (n:int) returns (f:int)
	requires n >= 0
	ensures f == fact(n)
{
var x:int := 0; 
f := 1;
while x < n
	  // invariant 
	  // invariant 
	{
		// assert ;
	x := x + 1;
		// assert ;
	f := f * x;
	}
}
*/

// EXERCISE 4
// Write a method Main that calculates the first 11 factorials and shows the results.


// EXERCISE 5
// Verify the following recursive method that calculates the number of combinations of m elements out of n,
// that is the combinatorial number "m over n".

method combinations (m:int, n:int) returns (r:int)
	requires m >= n >= 0
	//ensures  r * fact(n) * fact(m-n) == fact(m)  
{
if n == 0 || n == m  { r := 1; }
else { 
     var raux1 := combinations(m-1,n-1);
	 var raux2 := combinations(m-1,n);
	 r := raux1 + raux2;
	 }
}

// EXERCISE 6
// Define a function sumSerie(n:int):int such that 
// (informally) sumSerie(n) == 1 + 3 + ... + (2*n - 1)



/*
Define and prove (even if Dafny proves it automatically)
the lemma "Lemma_Square" that helps Dafny proving the contract of the following method.
*/
/*
lemma Lemma_Square(n:int)

method Square' (a:int) returns (x:int)
	requires a >= 0
	ensures x == sumSerie(a)
{
x := 0;
var y := 0;
while  y != a
		// invariant 
	{
    x := x + 2*y + 1;
	y := y+1;
	}
Lemma_Square(?);
}
*/





