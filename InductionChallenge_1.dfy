function squaresProgression(n:int):int
    decreases n
    requires n > 0
{
    if n == 1 then
        4 
    else
        squaresProgression(n-1) + (2*n-1)*(2*n-1) + 3*n*n
}


lemma productDistributive_Lemma(a:int, b:int, c:int)
    ensures a*b + a*c == a*(b + c)
    {}


lemma {:induction false} squaresProgression_Lemma(n:int)
    decreases n
    requires n > 0
    ensures squaresProgression(n) == n*(2*n+1)*(7*n+1)/6
{
    if n > 1  {
        calc {
            squaresProgression(n);
            == 
            squaresProgression(n-1) + (2*n-1)*(2*n-1) + 3*n*n;
            ==  {squaresProgression_Lemma(n-1);}  // H.I.
            (n-1)*(2*(n-1)+1)*(7*(n-1)+1)/6 + (2*n-1)*(2*n-1) + 3*n*n;
            ==
            ((n-1)*(7*n-6)*(2*n-1) + 6*(2*n-1)*(2*n-1))/6 + 3*n*n;
            == {productDistributive_Lemma(2*n-1, (n-1)*(7*n-6), 6*(2*n-1));}
            ((n-1)*(7*n-6) + 6*(2*n-1))*(2*n-1)/6 + 3*n*n;
            ==
            n*(2*n-1)*(7*n-1)/6 + 3*n*n;
            ==
            (n*(2*n-1)*(7*n-1) + 18*n*n)/6;
            == 
            n*((2*n-1)*(7*n-1) + 18*n)/6;
            == {productDistributive_Lemma(n, (2*n-1)*(7*n-1), 3*n);}
            n*(14*n*n+9*n+1)/6;
            == {assert (7*n+1)*(2*n+1) == 14*n*n+9*n+1;}
            n*(7*n+1)*(2*n+1)/6;
        }
    }
}