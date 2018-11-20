// Exercise 1: Write in paper how you obtain the (five) VCs for the method ComputeFactorial

function fact(n:nat):nat
{
 if n == 0 then 1 else n * fact(n-1)
}

method ComputeFactorial(n:int) returns (f:int)
	requires 1 <= n;
	ensures f == fact(n);
{
 var x := 1;
 f := 1;
 while x < n
   invariant 1 <= x <= n;
   invariant f == fact(x);
	{ 
	var v, z := f, 1;
	while z < x + 1
		invariant 1 <= z <= x + 1 <= n;
		invariant v == fact(x) && f == z * fact(x);
		{
		f, z := f + v, z + 1;
		}
	x := x + 1;
	}
}

// Exercise 2: Check in Dafny that all the VCs are valid (sentences) asserts.

method VC_for_ComputeFactorial ()
{
    //vc1
    assert forall n :: 1 <= n ==> (1 <= n && 1 == fact(1));

    //VC2
    assert forall n,x,f :: (1 <= x <= n && f == fact(x) && x < n) ==> (1 <= x+1 <= n && f==fact(x));

    //VC3   
    assert forall n,x,f :: (1 <= x <= n && f == fact(x) && !(x < n)) ==> f == fact(n);

    //VC4
    assert forall n,x,f,z,v:: (1 <= z <= x+1 <= n && v == fact(x) && f == z*fact(x) && z < x + 1) ==> 
                (1 <= z+1 <= x+1 <= n && v == fact(x) && f+v == (z+1)*fact(x));

    //VC5
    assert forall n,x,f,z,v:: (1 <= z <= x+1 <= n && v == fact(x) && f == z*fact(x) && !(z < x + 1)) ==>
                (1 <= x+1 <= n && f == fact(x+1)); 
}
