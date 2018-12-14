
function method f(i:int):int
    //requires i >= 2
{
    if i%2 == 0 then 5 else 7
}

method pruebas()
{
    var a: array?<int>;
    // a := new int[6](i => 0);
    // assert a[5] == 0;
    // assert a == null;


    a := new int[6](f);
    assert a[3] == 7;
}

//method arrayFromSeq<T(0)>(s:seq<T>) returns (a:array<T>)
// En este caso se puede no inicializar porque es de tipo 0, valores que no necesitan ser incializados
method arrayFromSeq<T>(s:seq<T>) returns (a:array<T>)
    ensures a[..] == s
    ensures fresh(a)
    {
        a := new T[|s|](i requires 0 <= i < |s| => s[i]);

    }

method min(a:array<int>) returns (m:int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
    ensures m in a[..]
{
    var k := 1;
    m := a[0];
    while k < a.Length 
        invariant 0 < k <= a.Length
        invariant forall i :: 0 <= i < k ==> m <= a[i]
        invariant m in a[..]
        {   
            if m > a[k] {
                m := a[k];
            }
            // assume forall i :: 0 <= i < k+1 ==> m <= a[i]
            k := k +1;
        }
    // invariant 
}

method mapAdd(v1:array<int>, c:int) returns (v2:array<int>)
    ensures v2 == v1
    ensures forall i :: 0 <= i < v1.Length ==> v1[i] == old(v1[i])+c
    modifies v1
    {
        var k:= 0 ;
        while k < v1.Length
            invariant 0 <= k <= v1.Length
            invariant forall i :: 0 <= i < k ==> v1[i] == old(v1[i]) + c
            invariant forall i :: k <= i < v1.Length ==> v1[i] == old(v1[i])
            {
                v1[k] := v1[k] + c;
                k:= k + 1;
            }

        return v1;
    }

datatype Color = Red | White | Blue

predicate bellow(c:Color, d:Color)
{
    c == Red || c == d || d == Blue
}

predicate perm<T(==)> (s:seq<T>, r:seq<T>)
{
    multiset(s) == multiset(r)
}

method DutchFlag(a:array<Color>)
    modifies a
    ensures forall i,j:: 0 <= i < j < a.Length ==> bellow(a[i], a[j])
    ensures perm(a[..],old(a[..]))
    {
        var r,w,b := 0, 0, a.Length;
        while w < b
            invariant 0 <= r <= w <= b <= a.Length
            invariant forall i :: 0 <= i < r ==> a[i] == Red
            invariant forall i :: r <= i < w ==> a[i] == White
            invariant forall i :: b <= i < a.Length ==> a[i] == Blue
            invariant perm(a[..],old(a[..])); 
        {
            match a[w] {
                case Red => {
                    a[w],a[r] := a[r],a[w];
                    r := r + 1;
                    w := w + 1;
                }
                case White => {
                    w := w + 1;
                }
                case Blue => {
                    a[w],a[b-1] := a[b-1],a[w];
                    b := b - 1;
                }
            }
        }
    }

// Hacer el dutch flag para 4 colores
datatype  colores = Rojo | Amarillo | Verde | Azul

predicate debajo(c:colores, d:colores)
{
    c == Rojo || c == d || (c == Amarillo && d == Verde) || d == Azul
}

method banderaGay(a:array<colores>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> debajo(a[i],a[j])
    ensures perm(a[..],old(a[..]))
{
    var r,m,v,z := 0,0,a.Length,a.Length;
    while m < v
        invariant r <= m <= v <= z <= a.Length
        invariant forall i :: 0 <= i < r ==> a[i] == Rojo
        invariant forall i :: r <= i < m ==> a[i] == Amarillo
        invariant forall i :: v <= i < z ==> a[i] == Verde
        invariant forall i :: z <= i < a.Length ==> a[i] == Azul
        invariant perm(a[..],old(a[..]))
        {
            match a[m] {
                case Rojo => {
                    a[r], a[m] := a[m], a[r];
                    r, m := r + 1, m + 1;
                }
                case Amarillo => {
                    m := m + 1;
                }
                case Verde => {
                    a[m], a[v-1] := a[v-1], a[m];
                    v := v -1;
                }
                case Azul => {
                    if v == z || m == v - 1{
                        a[m], a[z-1] := a[z-1],a[m];
                    }else {
                        a[m], a[v-1], a[z-1] := a[v-1], a[z-1], a[m];
                    }
                    v , z := v - 1, z-1;
                }
            }
        }
}

predicate sortedBetween(v:array<int>,a:int, b:int)
    reads v
    requires a >= 0 && b <= v.Length
{
    forall i,j:: a <= i <= j < b ==> v[i] <= v[j]
}  

predicate sortedArray(a:array<int>)
    reads a
{
    sortedBetween(a,0,a.Length)
}

method bubleSort(a:array<int>)
    requires a.Length > 0
    ensures sortedArray(a)
    ensures perm(a[..],old(a[..]))
    modifies a
{
    var i:= 1;
    while i < a.Length 
        invariant 1 <= i <= a.Length
        invariant sortedBetween(a,0,i)
        invariant perm(a[..],old(a[..]))
        modifies a
        {
            pushLeft(a,i);
            // assume sortedBetween(a,0,i+1);
            i := i + 1;
        }   
}

method pushLeft(a:array<int>,index:int)
    modifies a
    requires 1 <= index < a.Length
    requires sortedBetween(a,0,index)
    ensures sortedBetween(a,0,index+1)
    ensures perm(a[..],old(a[..]))
{
    var j := index;
    while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= index
        invariant sortedBetween(a,0,j); 
        invariant sortedBetween(a,j,index+1)
        invariant 0 < j < index ==> a[j-1] <= a[j+1];
        invariant perm(a[..],old(a[..]));
    {
        //assert sortedBetween(a,j-1,index+1) && a[j] < a[j-1];
        a[j-1],a[j]:= a[j],a[j-1];
        //assert sortedBetween(a,j,index+1);
        j := j - 1;
        //assert sortedBetween(a,j,index+1);
    }
}

method BinarySearch(a:array<int>, key:int) returns (index:int)
    requires sortedArray(a)
    ensures 0 <= index <= a.Length
    ensures index < a.Length ==> a[index] == key
    ensures index == a.Length ==> key !in a[..] 
    {
        var start, end := 0, a.Length;

        while start < end
        invariant 0 <= start <= end <= a.Length
        invariant key !in a[0..start] + a[end..]
        {
            var mid := (start + end) / 2;

            if key < a[mid] {
                end := mid;
            } else if key == a[mid] {
                return mid;
            } else {
                start := mid + 1;
            }
        }

        return a.Length;
    }

// binary search recursivo con start y end

method BinarySearchR(a:array<int>, key:int, start:int, end:int) returns (index:int)
    requires sortedArray(a)
    requires 0 <= start <= end <= a.Length
    ensures 0 <= index <= a.Length
    ensures index < a.Length ==> a[index] == key
    ensures index == a.Length ==> key !in a[start..end] 
    decreases end-start
    {
            if start == end {
                return a.Length;
            } else {
                var mid := (start + end) / 2;
                if key < a[mid] {
                    index := BinarySearchR(a, key, start, mid);
                } else if key == a[mid] {
                    index :=  mid;
                } else {
                    index := BinarySearchR(a, key, mid + 1, end);
                }
            }   
    }