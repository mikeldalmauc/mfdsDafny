// Exercise 1

method RootApprox (x:int)  returns (r:int)
	requires x >= 0
	ensures r*r <= x < (r+1)*(r+1) 
{
	r := 0;  
	while (r+1)*(r+1) <= x
		invariant r*r <= x
		{
		r := r+1;
		}
}

method VC_for_RootApprox ()
{
// assert forall x :: x >= 0 ==> 0*0 <= x;
assert forall x,r :: ( r*r <= x  &&  (r+1)*(r+1) <= x ) ==> (r+1)*(r+1) <= x ;
assert forall x,r :: ( r*r <= x  &&  !((r+1)*(r+1) <= x) )==> r*r <= x < (r+1)*(r+1) ;
}

// Exercise 2

predicate noDivU(x:int, t:int)
{
forall z :: ( 1 < z < t ==> x % z != 0) 
}

predicate prime(x:int)
{ 
x >= 2  && noDivU(x,x) 
}

predicate noPrimesIn(a:int, b:int)
{
forall z :: a < z < b ==> !prime(z)
}

method next_prime (x:int) returns (p:int)
	requires prime(x)
	ensures p > x && prime(p) && noPrimesIn(x,p)
	decreases *
{
var next := x+1;
var isPrime:= false;
while !isPrime					
    invariant next > x >= 2
    invariant noPrimesIn(x,next)          
	invariant isPrime ==> (p == next && prime(next))       
	decreases *
	{
	var d := 2;
	while next % d != 0 
		invariant 2 <= d <= next
		invariant noDivU(next,d) 
		decreases next-d
		{ 
		d := d+1; 
		}
	isPrime := d == next;
	if isPrime { p := next; } else { next := next+1; }
	}
}


method VC ()
{
//vc1

//vc2

//vc3

//vc4

//vc5
    
}