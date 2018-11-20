predicate isCroissant(a:seq<int>)
{
    if |a| <= 1 then 
        true 
    else 
        forall i :: 1 <= i < |a| ==> a[i-1] <= a[i]
}

predicate maxLength(a:seq<int>, k:int)
    requires k >= 1
    decreases |a|
{
    if |a| < k then 
        false
    else 
        if |a| == k then
            isCroissant(a)
        else
            assert |a| >= 2;
            exists i :: (1 <= i < (|a|-2) ==> maxLength(a[..i] + a[(i+1)..], k))
}


// The final value of k, represents the answer we are looking for, i.e.  we seek to stablish the relation
// k = the maximum length upsecuence contained in a[0],...,a[N-1] (Postcondition) . EWD697 - 5
method lengthLongestUpsecuence(a:seq<int>) returns (k:int)
    requires |a| > 0
    ensures k >= 1 &&  maxLength(a,k) == true
{
    k := 1;             // Max upsecuence length
    var n := 1;         // Elements evaluated 
    var m:= [a[0]];     // Array of minimun rightmost elements of upsecuences of length j

    while n < |a|
        // Invariant relation introducing the variable n 
        // k = the maximum upsecuence contained in a[0],...,a[n-1] and 1 <= n <= N
        invariant 1 <= k <= n <= |a|
        invariant |m| == k
        invariant maxLength(a[..n],k) == true
        decreases |a| - n
    {

        if m[k-1] <= a[n] {
            k := k + 1;            // k increases as we found an upsecuence of this length
            m := m + [a[n]];       // a[n] becomes the minimum righ-most element of the upsecuence of length k containe in a[0]...a[n]
        }else{

            // We find m[j] the minimum rightmost element of an upsecuente of length j where 1 < j < k
            if a[n] < m[0] { // New smallest beginning of subsecuence
                m := m[0 := a[n]]; 
            }else{
                var i := k - 1;

                while i > 0
                    invariant 0 <= i <= k - 1  // we already know here m[k-1] is greater than a[n], no need to reach
                {
                    if  a[n] < m[i] {
                        i := i - 1;
                    } else {
                        m := m[i := a[n]];
                        i := 0;
                    }
                }
            }
        }
        assume |m|== k; // TODO
        n := n + 1;
    }
}

// We find m[j] the minimum rightmost element of an upsecuente of length 
// P2: forall j : 1 < j < k: m[j] = the minimum rightmost element of an upsecuence contained in A[0] .. A[n-1]
method binarySearch(m:seq<int>, aN: int, k:int) returns (j:int)
    requires k > 1 && |m| == k
    requires m[0] <= aN < m[k-1] // 
    ensures 1 < j < k-1 && m[j-1] <= aN < m[j]
    {
        var i,h := 0,0; // Cut point
        j := k-1;
        while j - i > 0
            // P3 invaraint in Dijktras article
            invariant 0 <= i <= j < k &&  m[i] <= aN < m[j]
            decreases  j - i 
            {
                assert i != j;
                h := (i + j)/2;
                if m[h] <= aN {
                    i := h;
                }else{
                    j := h;
                }
            }
    }