function exp(x:int, e:int):int
	requires e >= 0
    decreases e
{
if e == 0 then 1 else x*exp(x,e-1)
}

lemma {:induction false} exp3_Lemma(n:int)
    requires n >= 1
    decreases n
	ensures (exp(3,n)-1)%2 == 0
{
/*
if n == 1 {
           //assert exp(3,1)-1 == 2;
           }
else {
      exp3_Lemma(n-1);
	  assert (exp(3,n-1)-1)%2 == 0; // Hip�tesis de inducci�n
	  assert exp(3,n)-1 == 2*exp(3,n-1) + (exp(3,n-1)-1); // Relaci�n entre P(n) y P(n-1)
      }
*/
if n != 1 
     {
      exp3_Lemma(n-1);
	  assert (exp(3,n-1)-1)%2 == 0; // Hip�tesis de inducci�n
	  assert exp(3,n)-1 == 2*exp(3,n-1) + (exp(3,n-1)-1); // Relaci�n entre P(n) y P(n-1)
      }
}

/**
    Asegura algo para todo n, es una propiedad cerrada
 */
lemma forall_exp3_Lemma()
	ensures forall n :: n>=1 ==> (exp(3,n)-1)%2 == 0
{
    forall n | n>=1 { exp3_Lemma(n); }
}

lemma {:induction false} cuatron_Lemma(n:int)
    decreases  n
	requires n >= 6
	ensures 4*n < n*n - 7
{
// assert  n*n - 7 >= 6*n - 7 == 6*(n-1) - 1 >= n*5 -1 > 4*n;
if n == 6 {
           assert 4*6 < 6*6 -7;
          }
else {
     cuatron_Lemma(n-1);
     // assert exp(n-1,2) == (n-1)*exp(n-1,1)
     // assert 4*(n-1) < (n-1)*exp(n-1,1) - 7 == exp(n-1,2) - 7
     // assert forall n :: n >= 1 ==> exp(n-1,2) - 7
	 assert 4*(n-1) < (n-1)*(n-1) - 7; //H.I.
	 assert 4*n < n*n-(2*n+2);
	 assert 4*n < n*n - 7 <==> 5 <= 2*n;
     }
}

/*
    Demostras por inducción :

        For all n >= 1 -> (3**2n - 1) % 8
*/

lemma {:induction false} mult8_Lemma(n:int)
    requires n >= 1 
    decreases n
    ensures (exp(3,2*n)-1)%8 == 0
{
    if n != 1 {
        mult8_Lemma(n-1);
        assert (exp(3,2*(n-1))-1)%8 == 0;// H.I. no es obligatorio porque con la llamada al lema es equivalente a escribir esta línea
        assert exp(3,2*n)-1 == 8*exp(3,2*n-2) + exp(3,2*n-2) - 1;
    }
}

/*
    Forall n : n>= 1 => 1 + 3 + 5 + ... + (2n-1) = n**2
*/

function oddSum(n:int):int
 decreases  n
    requires n >=1
{
        if n == 1 then 1 else oddSum(n-1) + 2*n -1
}

lemma {:induction false} oddSum_Lemma(n:int)
    decreases  n
    requires n >= 1
    ensures oddSum(n) == n*n
{
    if n != 1 {
        oddSum_Lemma(n-1);
        assert oddSum(n-1) == (n - 1)*(n - 1);
        assert oddSum(n) == oddSum(n-1) + 2*n - 1;
    }
}

/*
    Forall n : n >= 0 => !n = n exp n
*/

function factorial (n:int):int
 decreases  n
    requires n >= 0
{
    if n == 0 then 1 else n*factorial(n-1)
}

lemma {:induction false} factorial_Lemma(n:int)
    requires n >= 1
    decreases  n
    ensures factorial(n) <= exp(n,n)
    {
        if n != 1 
        {
            factorial_Lemma(n-1);
           // assert factorial(n-1) <= exp(n-1,n-1);
           base_Lemma(n-1,n,n-1);
           assert exp(n-1,n-1) <= exp(n,n-1);
           assert factorial(n) <= n * exp(n-1, n-1) <= n * exp(n,n-1);
        }
    }

lemma {:induction false}base_Lemma(x:int, y:int, e:int)
    decreases  x, y, e
    requires e >= 0
    requires 1 <= x <= y
    ensures exp(x,e) <= exp(y,e)
{
    if e != 0 {
        base_Lemma(x,y,e-1);
        assert exp(x,e-1) <= exp (y,e-1); // HI
        assert exp(x,e) == x*exp(x,e-1);
        assert exp(y,e) == y*exp(y,e-1);
        assert exp(x, e-1) <= (y/x)*exp(y,e-1);
    }
}