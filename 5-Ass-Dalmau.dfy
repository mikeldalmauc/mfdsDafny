datatype List<T> = Nil | Cons(head:T, tail:List<T>)

datatype Tree<T> = Empty | Node(left:Tree,data:T,right:Tree)

function length (xs:List):nat
{
match xs
	case Nil => 0
	case Cons(_,t) => 1 + length(t)
}

function multiset_of_list<T> (xs:List<T>): multiset<T>
{
match xs
	case Nil => multiset{}
	case Cons(h,t) => multiset{h} + multiset_of_list(t)
}

function append<T> (xs:List, ys:List): List 
{
match xs
    case Nil => ys
    case Cons(h,t) => Cons(h,append(t,ys))
}

function mirror (t:Tree):Tree
{
match t
	case Empty => Empty
	case Node(l,d,r) => Node(mirror(r),d,mirror(l))
}

function flatten<T> (t:Tree):List<T>
{
match t
	case Empty => Nil
	case Node(l,d,r) => append(flatten(l), Cons(d,flatten(r)))
}

// Exercise 1
// Prove this lemma
lemma {:induction false} Lemma_mirror_multiset (t:Tree)
	ensures multiset_of_list(flatten(t)) == multiset_of_list(flatten(mirror(t)))
    {
         match t 
            case Empty => {}
            case Node(l,d,r) => {
                                calc {
                                        multiset_of_list(flatten(t));
                                        {multisetOfTree_Lemma(t);}
                                        multiset_of_list(flatten(l)) + multiset{d} + multiset_of_list(flatten(r));
                                        {
                                            Lemma_mirror_multiset(l);
                                            Lemma_mirror_multiset(r);
                                        }
                                        multiset_of_list(flatten(mirror(l))) + multiset{d} +  multiset_of_list(flatten(mirror(r)));
                                        {multisetOfTree_Lemma(Node(mirror(r),d,mirror(l)));}
                                        multiset_of_list(flatten(Node(mirror(r),d,mirror(l))));
                                    }
                                } 
    }

lemma multisetOfListAppend_Lemma(l:List, r:List)
    ensures multiset_of_list(append(l,r)) == multiset_of_list(l) + multiset_of_list(r);
    {}

lemma multisetOfTree_Lemma(t:Tree)
    requires t.Node?
    ensures multiset_of_list(flatten(t)) == multiset_of_list(flatten(t.left)) + multiset{t.data} +  multiset_of_list(flatten(t.right));
    {
        calc{
            multiset_of_list(flatten(t));
            multiset_of_list(append(flatten(t.left), Cons(t.data,flatten(t.right))));
            {multisetOfListAppend_Lemma(flatten(t.left), Cons(t.data,flatten(t.right)));}
            multiset_of_list(flatten(t.left)) + multiset{t.data} +  multiset_of_list(flatten(t.right));   
        }
    }

// Exercise 2

function numLeaves(t:Tree):nat
{
match t
	case Empty => 0
	case Node(l,d,r) => if l.Empty? && r.Empty? then 1
	                    else numLeaves(l) + numLeaves(r)
}

// Define a function that calculates the number of nodes of degree 2 of a given tree.
// A node has grade 2 if it has exactly two children
// Complete the definition
function numDegree2 (t:Tree):nat
{
    match t
        case Empty => 0
        case Node(l,d,r) =>
            if l.Empty? || r.Empty? then 
                numDegree2(r) + numDegree2(l)
            else 
                1 + numDegree2(r) + numDegree2(l)
}

// Prove this lemma
lemma {:induction false} Degree2_Lemma (t:Tree)
	requires t.Node?
	ensures numLeaves(t) == numDegree2(t)+1
    {  
        match t
            case Node(l,d,r) => {
                calc {
                    numLeaves(t);
                    if l.Empty? && r.Empty? then 1 else numLeaves(l) + numLeaves(r);
                    {
                        if l.Node? {Degree2_Lemma(l);}
                        if r.Node? {Degree2_Lemma(r);}    
                    }
                    // El siguiente bloque no es obligatorio, el SMT solver lo comprueba
                    if l.Empty? || r.Empty? then 
                        numDegree2(r) + numDegree2(l) + 1
                    else 
                        numDegree2(r) + 1 + numDegree2(l) + 1;
                    numDegree2(t)+1;
                }
            }
    }

// Exercise 3

predicate method isLeaf<T> (t:Tree)            // Note that it can be used in code   
{
t.Node? && t.left.Empty? && t.right.Empty? 
}

function Leaves<T> (t:Tree):set<T>
{
match t
	case Empty => {}
	case Node(l,d,r) => if l.Empty? && r.Empty? then {d}
	                    else Leaves(l) + Leaves(r)
}

method MaxLeave (t:Tree<nat>) returns (max:nat)
    requires t.Node?
	ensures max in Leaves(t) 
	ensures forall d :: d in Leaves(t) ==> d <= max
{   
    var maxL, maxR := 0,0;
    if isLeaf(t) {
        max := t.data;
    }else {
        if !t.left.Empty? { 
            maxL := MaxLeave(t.left);
        }
        if !t.right.Empty? {
            maxR := MaxLeave(t.right);
        }
        if maxL < maxR {
            max := maxR;
        } else {
            max := maxL;
        }
    }
}
// Design a verified body for that method.
// As a hint you can use the following assert that can be preoviously checked to be true.

/*
assert t.Node? ==> Leaves(t) == if isLeaf(t) then {t.data} 
                                else ((if !t.left.Empty? then Leaves(t.left) else {})
								      + (if !t.right.Empty? then Leaves(t.right) else {}));
*/
               