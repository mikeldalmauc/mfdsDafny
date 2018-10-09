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

lemma Lemma_Square2(n:int)
	requires n >= 0
	ensures sumSerie2(n) == n*n
	{}

function sumSerie2(n:int):int
	decreases n
	requires n>=0
	{
		if n <= 1 then n else 2*n - 1 + sumSerie2(n-1)
	}


method Square2 (a:int) returns (x:int)
	requires a >= 1
	ensures x == sumSerie2(a)
{
	x := 0;
	var y := 0;
	while  y < a
		invariant 0 <= y <= a
		invariant x == sumSerie2(y)
		{
			y := y + 1;
			x := x + 2*y - 1;
		}
	assert x == sumSerie2(a);
	Lemma_Square2(a);
	assert x == a*a;
}

method Square3(a:int) returns (x:int)
	requires a >= 1
	ensures x == a*a
	{
		x := 1;
		var y  := 2;
		while y <= a
			invariant 0 <= y <= a+1
			invariant x == sumSerie(y-1)
		{
			x := x + 2*y -1;
			y := y + 1;
		}
		Lemma_Square(a);
	}

method computeFactTuring(n:int) returns (u:int)
	requires n >= 1
	ensures u == fact(n)
	{
		var r := 1;
		u := 1;
		while r < n
		 invariant 1 <= r <= n
		 invariant u == fact(r)
		{
			var v := u;
			var i := 1;
			while i < r + 1
				invariant 0 <= i <= r +1
				invariant u == i*fact(r)
			{
				u,i := v + u, i + 1;
			}
			r := r + 1;
		}
	}

method sig_fact(r:int, u:int) returns (v:int)
	requires r >= 0 && u == fact(r)
	ensures v == fact(r+1)
{
	v := u;
	var i := 1;
	while i < r + 1
		invariant 0 <= i <= r +1
		invariant v == i*fact(r)
	{
		assert 1 <= i+1 <= r+1 && v+u == (i+1)*fact(r);
		v,i := v + u, i + 1;
		assert 1 <= i <= r+1 && v == i * fact (r);
	}
}

function power(b:int,e:int):int
requires e>=0;
{
	if e == 0 then 1 else b * power(b,e-1)
}

lemma even_Lemma(base:int, exp:int)
requires exp%2 == 0 && exp >= 0
ensures power(base,exp) == power(base*base,exp/2)
{
	if exp == 0 {

	}else{
		even_Lemma(base,exp-2);
	}
} // TODO hacer a mano la demostracción por inducción de este lemma con menos 2

method computePower(b:int, e:int) returns (p:int)
	requires e >= 0 
	ensures p == power(b,e)
{
	var t, x := e, b;
	p := 1;
	while t > 0
	invariant 0 <= t <= e
	invariant p* power(x,t) == power(b,e)
	{
		if t % 2 == 0 {
			even_Lemma(x,t);
		//assert p * power(x*x, t/2) == power(b,e);
			x , t := x*x, t/2;
		} else {
			//assert p * x * power(x,t-1) == power(b,e);
			p, t := p*x, t-1;
		}
	}
}

method computePowerRec(b:int, e:int) returns (p:int)
	requires e >= 0
	ensures p == power(b,e)
	decreases e
	{
		if e == 0 {
			p:= 1;
		} else if e % 2 == 0 {
			even_Lemma(b,e);
			p := computePowerRec(b*b,e/2);
		} else {
			var k :=computePowerRec(b,e-1);
			p := b*k;
		}
	}

method factorialRaro(n:int) returns (f:int)
	requires n>= 1 
	ensures f == fact(n)
	{
		// var i f * fact(n-i-1) = fact(n)
	}