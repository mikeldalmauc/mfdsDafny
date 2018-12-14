predicate method isCroissant(a:seq<int>)
{
    forall i,j :: 1 <= i <= j < |a| ==> a[i] <= a[j]
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
            exists i :: (0 <= i < |a| ==> maxLength(a[..i] + a[(i+1)..], k))
}

method lengthLongestUpsecuence(a:seq<int>) returns (k:int)
    requires |a| > 0
    ensures 1 <= k <= |a| &&  maxLength(a,k) == true
{
    k := 1;             // Max upsecuence length
    var n := 1;         // Elements evaluated 
    var m:= [a[0]];     // Array of minimun rightmost elements of upsecuences of length j

    while n < |a|
        // Invariant relation introducing the variable n 
        // k = the maximum upsecuence contained in a[0],...,a[n-1] and 1 <= n <= N
        invariant 1 <= k <= n <= |a|
        invariant |m| == k
        invariant maxLength(a[..n],k) == true // k is the longest upsecuence
        invariant isCroissant(m)
        decreases |a| - n
    {

        if m[k-1] <= a[n] {
            k := k + 1;            // k increases as we found an upsecuence of this length
            m := m + [a[n]];       // a[n] becomes the minimum righ-most element of the upsecuence of length k containe in a[0]...a[n]

        }else if a[n] < m[0] { // New smallest beginning of subsecuence
            m := m[0 := a[n]]; 
        
        } else {   // We find m[j] the minimum rightmost element of an upsecuente of length j+1 where 0 <= j < k, in a[..n-1]
            m := BinaryInsertion(m, a[n]);
        }

        n := n + 1;
    }
}
 

// We find m[j] the minimum rightmost element of an upsecuente of length 
// P2: forall j : 1  < j < k: m[j] = the minimum rightmost element of an upsecuence contained in A[0] .. A[n-1]
method BinaryInsertion(s:seq<int>, v:int) returns (s':seq<int>)
    requires isCroissant(s)
    requires |s| > 0
    requires s[0] <= v < s[|s|-1]
    ensures isCroissant(s') && v in s'
    ensures |s| == |s'|
    //     var start, end := 0, |a|;
    //     while start < end
    //     invariant 0 <= start <= end <=
    //     invariant a[start] <= m' < a[end..]
    //     {
    //         var mid := (start + end) / 2;

    //         if m' < a[mid] {
    //             end := mid;
    //         } else {
    //             start := mid + 1;
    //         }
    //     }

    //     b := a[mid := m'];
    // }
