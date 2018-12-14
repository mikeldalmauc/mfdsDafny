function reverse<T> (s:seq<T>):seq<T> 
decreases s
ensures |reverse(s)|== |s|
{
if s == [] then [] else reverse(s[1..]) + [s[0]]
}

function seq2set<T> (s:seq<T>): set<T>
    decreases s
{
if s == [] then {} else {s[0]} + seq2set(s[1..])
}

lemma {:induction s1} seq2set_Lemma<T> (s1:seq<T>, s2:seq<T>)
    decreases s1, s2
    ensures seq2set(s1 + s2) == seq2set(s1) + seq2set(s2);
{
    if s1 == [] {
        assert s1 + s2 == s2;
        assert seq2set(s1 + s2) == seq2set(s1) + seq2set(s2);
    } else {
        calc == {
            seq2set(s1 + s2);
            {assert s1 + s2 == [s1[0]] + (s1[1..] + s2);}
            seq2set([s1[0]] + (s1[1..] + s2));
            //{assert  seq2set([s1[0]] + s1[1..] + s2)  == {s1[0]} + seq2set(s1[1..] + s2);}
            seq2set(s1[1..] + s2) + {s1[0]};
            { seq2set_Lemma(s1[1..],s2);}
            ({s1[0]} + seq2set(s1[1..])) + seq2set(s2);
            seq2set(s1) + seq2set(s2);
        }
    }
}
// Exercise 1

lemma {:induction s} seq2setRev_Lemma<T> (s:seq<T>)
    decreases s
	ensures seq2set(reverse(s)) == seq2set(s)
{
    if s == [] {
        assert seq2set(reverse(s)) == seq2set(s) == {};
    } else {
        calc == {
         seq2set(reverse(s));
        seq2set(reverse(s[1..]) + [s[0]]);
        {seq2set_Lemma(reverse(s[1..]), [s[0]]);}
        seq2set(reverse(s[1..])) + {s[0]};
        {seq2setRev_Lemma(s[1..]);}
        seq2set(s[1..]) + {s[0]};
        seq2set(s);
        } 
    }
}
//Exercise 2

method getElems<T> (s:seq<T>) returns (elems:multiset<T>)
	ensures elems == multiset(s)
{
    var i := 0;
    elems := multiset{};
    assert elems == multiset(s[..0]) == multiset{};
    while i < |s|
        decreases |s| - i
        invariant 0 <= i <= |s| && elems == multiset(s[..i])
    {
        // calc {
        //     elems + multiset{s[i]};
        //     multiset(s[..i]) + multiset{s[i]};
        //     {assert s[..i] + [s[i]] == s[..i+1];}
        //     multiset(s[..i+1]);
        // }
        assert s[..i] + [s[i]] == s[..i+1];
        i,elems :=i + 1 , elems + multiset{s[i]};
        assert elems == multiset(s[..i]);
    }
    assert s == s[..|s|];
    assert elems == multiset(s[..|s|]);
}
//Exercise 3

method times<T(==)> (s:seq<T>,x:T) returns (m:nat)
	ensures m == multiset(s)[x]
{
    m := 0;
    var k := 0;

    assert m == multiset(s[..k])[x];
    while k < |s|
        decreases |s| - k
        invariant 0 <= k <= |s| && m == multiset(s[..k])[x]
    {
        //assert s[k] == x && m == multiset(s[..k])[x] ==> multiset(s[..k+1])[x] == m + 1;
        //assert multiset(s[..k])[x] == m;
        assert s[..k+1] == s[..k] + [s[k]];
        //assert (s[k] == x && multiset(s[..k+1])[x] == m + 1 ) || (s[k] != x  &&  multiset(s[..k+1])[x] == m) ;
        if s[k] == x {
            m := m + 1;
        }
        //assert m == multiset(s[..k+1])[x];
        k := k + 1;
    }
    assert s == s[..k];
}

// Exercise 4

lemma {:induction s} seqMultiset_Lemma<T> (s:seq<T>)
    decreases s
    ensures multiset(reverse(s)) == multiset(s)
    {
        if s != [] {
            calc == {
                multiset(reverse(s));
                multiset(reverse(s[1..])) + multiset{s[0]};
                {seqMultiset_Lemma(s[1..]);} //  multiset(reverse(s[1..])) == multiset(s[1..])
                multiset(s[1..]) + multiset{s[0]};
                {assert s == [s[0]] + s[1..];}
                multiset(s);
            }
        }
    }

// Exercise 5: Construct a proof by contradiction of the following lemma

lemma {:induction s} ItsOwnInverse_Lemma<T> (s:seq<T>)
	ensures s == reverse(reverse(s))
{
    if s != reverse(reverse(s))
    {
        calc ==> {
            //assert |reverse(reverse(s))| == |s|;
            exists i :: 0 <= i < |s| && s[i] != reverse(reverse(s))[i]; 
            ==> {Rev_Lemma(s);}
            exists i :: 0 <= i < |s| && reverse(s)[|s| - 1 -i] != reverse(reverse(s))[i]; 
            ==> {Rev_Lemma(reverse(s));}
            exists i :: 0 <= i < |s| && reverse(reverse(s))[i] != reverse(reverse(s))[i]; 
            ==> false;
        }
    }
}

lemma Rev_Lemma<T(==)>(s:seq<T>)
    ensures forall i :: 0 <= i < |s| && s[i] == reverse(s)[|s| - 1 - i]
 

//
method Cubes (n:int) returns (s:seq<int>)
    requires n >= 0
    ensures |s| == n
    ensures forall i:int :: 0 <= i < n ==> s[i] ==  i*i*i 
    
    {
    // invariant with k variable
        var j := 0;
        s := [];
        var c,k,m := 0,1,6;
        while j < n
            decreases n - j 
            invariant 0 <= j == |s| <= n
            invariant forall i:int :: 0 <= i < j ==> s[i] ==  i*i*i 
            invariant c == j*j*j
            invariant k ==  3*j*j + 3*j + 1 
            invariant m == 6*j + 6 
        {
            s := s + [c]; // Derivar formalmente un cáculo incremental de j*j*j
            c := c + k;
            k := k + m;
            m := m + 6;

            assert c == (j+1)*(j+1)*(j+1)
                    == j*j*j + 3*j*j + 3*j + 1;
            assert k == 3 *(j+1)*(j+1) + 3*(j+1) + 1
                     == 3*j*j + 9*j + 7 == 3*j*j + 3*j + 1  + 6*j + 6;
            assert m == 6*j + 12 ;
            
            j := j + 1;

            assert k == 3*j*j + 3*j + 1 ;
            assert c == j*j*j;
            assert m == 6*j + 6;
        }
    }


function zip<T,S> (t:seq<T>, s:seq<S>):seq<(T,S)>
    decreases t, s
{
    if t == [] || s == [] then [] else [(t[0],s[0])] + zip(t[1..],s[1..])
}

lemma {:induction t, s,t',s'} distributibeZip_Lemma<T,S>(t:seq<T>, s:seq<S>,t':seq<T>, s':seq<S>)
    decreases t, s, t', s'
    requires |t| == |s|
    ensures zip(t,s) + zip(t',s') ==  zip(t + t', s + s')
{
    if t == [] 
    {
        assert t' == [] + t' && s' == [] +s';
    } else{
        var tt, ss := t[1..] + t', s[1..] + s';
        calc == {
            zip(t + t', s + s');
            {assert t + t' == [t[0]] + tt && s + s' == [s[0]] + ss;}
            zip([t[0]] + tt, [s[0]] + ss);
            [(t[0],s[0])] + zip(tt,ss);
            {distributibeZip_Lemma(t[1..],s[1..],t',s');}            
            zip([t[0]],[s[0]]) + zip(t[1..],s[1..]) + zip(t',s');
            zip(t,s) + zip(t',s') ;
        } 
    }
}

method unzip<T,S> (a:seq<(T,S)>) returns (t:seq<T>, s:seq<S>)
    ensures a == zip(t,s)
{
    t,s := [],[];
    var i:= 0;
    while i < |a|
        decreases |a| - i
        invariant 0 <= i <= |a|
        invariant |s| == |t| == i
        invariant a[..i] == zip(t,s)
    {
        distributibeZip_Lemma(t,s,[a[i].0],[a[i].1]);
        t := t + [a[i].0];
        s := s + [a[i].1];
        i := i + 1;
    }

}