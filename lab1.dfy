function exp(x:int, e:int):int
	requires e >= 0
    decreases e
   // ensures x >= 1 ==> exp(x,e) >= 1
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

/**
    CLASE 4 

 */
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
        assert forall x, e :: e>= 0 && x >= 1 ==> exp(x,e) >= 1;
        //assert x*exp(x,e-1) <= y*exp(y,e-1);
    }
}

predicate even(n:nat)
{
    n%2 == 0
}

function sumDigits(x:nat):nat
{
    if x < 10 then x else x % 10 + sumDigits(x/10)
}

lemma Div11_Lemma(n:nat)
    requires n >= 11 && n % 11 == 0
    ensures even(sumDigits(n))
{
    if n > 11 {
        var k := n / 11;
        calc{
            sumDigits(n);
            == 
            sumDigits(11*(k-1)+11);
            == {commutes_Lemma(11*(k-1),11);}
            sumDigits(11*(k-1)) + sumDigits(11);
            ==
            sumDigits(11*(k-1)) + 2;
        }
        Div11_Lemma(11 * (k-1));//Hipotesis de induccion
        //assert Div11_Lemma(11*k) = sumDigits( Div11_Lemma(11 * (k-1))) + sumDigits(11);
    }
}

lemma commutes_Lemma(a:nat, b:nat)
    ensures sumDigits(a+b) == sumDigits(a) + sumDigits(b)
// Este lemma es falso

lemma factoria_exp3_Lemma(n:int)
requires n >=7
ensures exp(3,n) < factorial (n)
{
    if n == 7 {
       // assert exp(3,7) < factorial(7);
    } else {
        factoria_exp3_Lemma(n-1);
        assert exp(3,n-1) <= factorial(n-1);
        assert forall n :: n >= 0 ==> factorial(n) >= 1;
        //product_Lemma(3, n, factorial(n-1));
        assert forall a,b,c:: 1 <= a < b && c >= 1 ==> a*c < b*c;
        assert 3*exp(3,n-1) <  3*factorial(n-1) <  n*factorial(n-1);
    }
}

lemma product_Lemma (a:int, b:int, c:int)
requires 1 <= a < b && c >= 1
ensures a*c < b*c
{}

lemma exp2n_Lemma(n:int)
    requires n >= 1
    ensures factorial(2*n) < exp(2,2*n)*exp(factorial(n),2)
{
    if n != 1 {
        calc {
            factorial(2*n);
            ==
            2*n*(2*n-1)*factorial(2*n-2);
            < {exp2n_Lemma(n-1);}
            2*n*(2*n-1)*exp(2,2*(n-1))*exp(factorial(n-1),2);
            ==
            2*n*(2*n-1)*exp(2,2*(n-1))*factorial(n-1)*factorial(n-1);
            ==
            (2*n-1)*exp(2,2*n-1)*factorial(n)*factorial(n-1);
            ==
            n*exp(2,2*n)*factorial(n)*factorial(n-1)
            -exp(2,2*n-1)*factorial(n)*factorial(n-1);
            ==
             exp(2,2*n)*factorial(n)*factorial(n)
            - (exp(2,2*n-1)*factorial(n)*factorial(n-1));
            ==
             exp(2,2*n)*exp(factorial(n),2)
            - (exp(2,2*n-1)*factorial(n)*factorial(n-1));
            < {assert forall x:: x>=0 ==> factorial(x) >= 1;
                assume exp(factorial(n),2) == factorial(n)*factorial(n);
            }
            exp(2,2*n)*exp(factorial(n),2);
        }
    }
}