predicate sorted (s:seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate palindrome<T(==)> (s:seq<T>)
{
    forall i :: 0 <= i < |s|  ==> s[i] == s[|s| -i-1]
}

method pruebas()
{
    var s: seq<int>;

    var s2 := [1,2,3];

    s:= s2;

    assert s2 == [1,2,3];

    var s1:seq<char> := [];

    assert [1,2] <= [1,2,3]; // prefijo

    assert [1,2] < [1,2,3]; // Prefijo propio

    // assert [1,2] < [1,2];  //No es prefijo propio

    //assert s2 + s1 == s2;

    assert s2[0] == 1;

    assert s2[0..2] == [1,2]; // [0,2) cerrado izquierda y abierto a la derecha
    assert s2[1..] == [2,3];

    var s3 := [5,4,3,7,8,10,43,1,2,2];

    assert s3[..1] == [5];
    assert s3[1..] == [4,3,7,8,10,43,1,2,2];

    assert s3[..8] == [5,4,3,7,8,10,43,1];
    assert s3[9..] == [2];

    assert s3[5..] == [10,43,1,2,2];

    assert s3[4..] == [8,10,43,1,2,2]; 
    
    assert s3[..5] == [5,4,3,7,8];   

    assert multiset(s3) == multiset{5,4,3,7,8,10,43,1,2,2}; // Set con elementos repetidos (BAG)

    var s4:set<int> :={1,1,2,3};
    
    assert s4 == {1,2,3};

    var s8 :=  (set x | 0 <= x <= 9 && x%2 == 0 :: x*5);

    //assert s8 == {0,10,20,30,40};
    //assert s7 := (set x | 0 <= x);

}   

function reverse<T> (s:seq<T>):seq<T>
 decreases  s
{
    if s == [] then s else reverse(s[1..]) + [s[0]]
}

lemma {:induction false }
reverse_length_Lemma<T> (s:seq<T>) 
    ensures |reverse(s)| == |s|
   // Ejercicio


// Definir recursivamente una función que convierta una secuencia en el conjunto de sus elementos
function seq2set<T> (s:seq<T>):set<T>
    decreases s
{
    if s == [] then {} else {s[0]} + seq2set(s[1..])
}