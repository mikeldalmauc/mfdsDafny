// Exercise 1

method RootApprox (x:int)  returns (r:int)
	requires x >= 0
	ensures r*r <= x < (r+1)*(r+1) 
{
	r := 0;  
	while (r+1)*(r+1) <= x
		invariant 0 <= r*r <= x
		{
		r := r+1;
		}
}

method VC_for_RootApprox ()
{
assert forall x :: x >= 0 ==> 0 <= 0*0 <= x;
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
		// invariant next > x >= 2          //Estos dos tambi�n son invariantes aqu� y en la VC5 hacen falta
		// invariant noPrimesIn(x,next)  
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
assert forall x, p :: prime(x) ==> ( x+1 > x >= 2 && noPrimesIn(x,x+1) 
                                     && false ==> (p == x+1 && prime(x+1) ) );

//vc2
assert forall x, next, isPrime, p :: ( next > x >= 2 && noPrimesIn(x,next) 
            && (isPrime ==> (p==next && prime(next)))
         && !isPrime ) ==> (2 <= 2 <= next && noDivU(next,2) );

//vc3

assert forall x, next, isPrime, p ::
       ( next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> (p==next && prime(next)))
         && !!isPrime ) ==> ( p > x && prime(p) && noPrimesIn(x,p) );

//vc4

assert forall d, next :: (2 <= d <= next && noDivU(next,d) && next%d != 0) 
       ==>  2 <= d+1 <= next && noDivU(next,d+1);

/*
//vc5  como qued� al final de la clase
assert forall x, d, next, p :: (2 <= d <= next && noDivU(next,d) && !(next%d != 0))
       ==> ( 
	         ( d == next && next > x >= 2 && noPrimesIn(x,next) 
			 && ( d == next ==> prime(next) ) )
			 ||
			 ( d != next && next+1 > x >= 2 && noPrimesIn(x,next+1) 
			 && ( d == next ==> (p == next+1 && prime(next) )) )
			 );
*/

//vc5  una vez revisada y corregida en mi despacho
assert forall x, d, next, p :: 
       (2 <= d <= next && noDivU(next,d) 
	     && next > x >= 2 && noPrimesIn(x,next) // parte extra por invariantes ocultos
		 && !(next%d != 0))
       ==> ( 
	         ( d == next && next > x >= 2 && noPrimesIn(x,next) 
	         && ( d == next ==> prime(next) ) )
			 ||
			 ( d != next && next+1 > x >= 2 && noPrimesIn(x,next+1) 
			 && ( d == next ==> (p == next+1 && prime(next) )) )
			 );
}