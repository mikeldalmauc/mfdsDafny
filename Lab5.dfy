datatype List<T> = Empty | Cons(head:T, tail:List)

function length<T>(xs:List<T>):nat
{
//if xs.Empty? then 0 else 1+length(xs.tail)
match xs
	case Empty => 0
	case Cons(_,t) => 1 + length(t)
}

function EqPairs<T(==)>(xs:List):nat
{
match xs
	case Empty => 0
	case Cons(h1,Empty) => 0
	case Cons(h1,Cons(h2,t)) 
	    => if h1 == h2 then 1 + EqPairs(Cons(h2,t))
		               else EqPairs(Cons(h2,t))
}


datatype Tree<T> = Empty | Node(left:Tree,root:T,right:Tree)

function max(x:int,y:int):int
{
if x >= y then x else y
}

function depth<T>(t:Tree<T>):nat
{
//if t.Empty? then 0 else 1 + max(depth(t.left),depth(t.right))
match t
	case Empty => 0
	case Node(l,_,r) => 1 + max(depth(l),depth(r))
}

predicate full<T>(t:Tree)
{
/*
match t
	case Empty => true
	case Node(l,_,r) 
	     => (l.Empty? && r.Empty?) ||
		    (l.Node? && r.Node? && full(l) && full(r))
			//!l.Empty? && !r.Empty
*/
t.Empty? || (t.left.Empty? && t.right.Empty?) ||
(t.left.Node? && t.right.Node? && full(t.left) && full(t.right))
}

lemma {:induction false} EqPairs_Lemma<T(==)>(xs:List)
	ensures EqPairs(xs) <= length(xs)
{
match xs {
	case Empty => {}
	case Cons(_,t) 
	     => { calc {
		            EqPairs(xs);
					<=
					1 + EqPairs(t);
		            <= { EqPairs_Lemma(t);}
					1+ length(t);
				    ==
					length(xs);
				   } 
		    }
	}
}

function append<T>(xs:List, ys:List):List
{
if xs.Empty? then ys else Cons(xs.head,append(xs.tail,ys))
}

//Ejercicio: length(append(xs,ys)) == length(append(xs)) + length(append(ys))

function rev<T>(xs:List):List
{
if xs.Empty? then List.Empty 
             else append(rev(xs.tail),Cons(xs.head,List.Empty))
}

lemma rev_twice_Lemma<T>(xs:List)
	ensures rev(rev(xs)) == xs
{
match xs 
	case Empty => {}
	case Cons(h,t) 
	   => {
           calc {
		        rev(rev(Cons(h,t)));
				rev(append(rev(t),Cons(h,List.Empty)));
				== {
				   appendDist_Lemma(rev(t),Cons(h,List.Empty));
				   //assume forall xs:List<T>, ys :: 
				   //rev(append(xs,ys)) == append(rev(ys),rev(xs));                  
				   }
				append(rev(Cons(h,List.Empty)),rev(rev(t)));
				== { rev_twice_Lemma(t); //H.I.
					 // assert rev(rev(t)) == t 
					}
			   append(Cons(h,List.Empty),t);
			   Cons(h,t);
	       }}

}

lemma appendDist_Lemma<T>(xs:List,ys:List)
  ensures rev(append(xs,ys)) == append(rev(ys),rev(xs));
{
match xs 
	case Empty => {
	               appendEmpty_Lemma(rev(ys));
				   //assert rev(ys) == append(rev(ys),List.Empty);
	               }
	case Cons(h,t) 
	  => {
	      calc { 
		        rev(append(Cons(h,t),ys)); 
		        rev(Cons(h,append(t,ys)));
				append(rev(append(t,ys)),Cons(h,List.Empty));           
			         == { appendDist_Lemma(t,ys);	//H.I.	   
		                  // rev(append(t,ys)) == append(rev(ys),rev(t));
						}
		        append(append(rev(ys),rev(t)),Cons(h,List.Empty));
				    == {
					   appendAss(rev(ys),rev(t),Cons(h,List.Empty));
					   //assert forall xs:List<T>, ys, zs :: append(append(xs,ys),zs) == append(xs,append(ys,zs));
					   }
				append(rev(ys), append(rev(t),Cons(h,List.Empty)));

				append(rev(ys),rev(Cons(h,t)));
		       }
	     }
}

lemma appendAss<T>(xs:List, ys:List, zs:List)
 ensures append(append(xs,ys),zs) == append(xs,append(ys,zs));
{}

lemma appendEmpty_Lemma<T>(xs:List)
   ensures append(xs,List.Empty) == xs
{}

lemma appendEmptyForall_Lemma<T>()
   ensures forall xs:List<T> :: append(xs,List.Empty) == xs
{
forall xs:List<T> { appendEmpty_Lemma(xs); }
}

predicate perfect<T>(t:Tree)
{
match t
   case Empty => false
   case Node(l,d,r) => (l.Empty? && r.Empty?) ||
                       ( !l.Empty? && !r.Empty?
					     && perfect(l) && perfect(r)
						 && depth(l) == depth(r) )
}

function numLeaves<T>(t:Tree):nat
{
match t
   case Empty => 0
   case Node(l,d,r) => if l.Empty? && r.Empty?
                       then 1
					   else numLeaves(l) + numLeaves(r)
}

function exp2(n:nat):nat
{
if n == 0 then 1 else 2 * exp2(n-1)
}

lemma {:induction false} leavesPerfect_Lemma<T>(t:Tree)
	requires perfect(t)
	ensures numLeaves(t) == exp2(depth(t)-1)
{
match t
  //case Empty => {}
  case Node(l,d,r) => 
      {
	  calc { 
	       numLeaves(Node(l,d,r));
		   if l.Empty? && r.Empty? then 1 
		   else numLeaves(l) + numLeaves(r);
		   == { 
		       if perfect(l) { leavesPerfect_Lemma(l);}
			   if perfect(r) { leavesPerfect_Lemma(r);}
	           // numLeaves(l) == exp2(depth(l)-1)
	           // numLeaves(r) == exp2(depth(r)-1)
			   }
		   if l.Empty? && r.Empty? then 1 
		   else exp2(depth(l)-1) + exp2(depth(r)-1);

		   if l.Empty? && r.Empty? then 1  else 2 * exp2(depth(l)-1);

		   if l.Empty? && r.Empty? then 1  else exp2(depth(l));

	       exp2(depth(t)-1);
		   }
	  }
}

function numNodes<T>(t:Tree):nat
{
match t
   case Empty => 0
   case Node(l,d,r) => 1 + numNodes(l) + numNodes(r)
}

lemma nodesPerfect_Lemma<T>(t:Tree)
	requires perfect(t)
	ensures numNodes(t) == exp2(depth(t)) - 1
// Ejercicio

function mirror<T>(t:Tree):Tree
{
match t
	case Empty => Tree.Empty
	case Node(l,d,r) => Node(mirror(r),d,mirror(l))
}

lemma {:induction false} mirrorTwice_Lemma<T>(t:Tree)
	ensures mirror(mirror(t)) == t
{
match t 
	case Empty => {}
	case Node(l,d,r) => {
	                     calc {
						       mirror(mirror(t)); 
							   mirror(Node(mirror(r),d,mirror(l)));
							   Node(mirror(mirror(l)),d,mirror(mirror(r)));
							    == {
								    mirrorTwice_Lemma(l); 
									mirrorTwice_Lemma(r);
								   }
							   Node(l,d,r);
						 }
	                    } 
	                   
}

function multiset_of_tree<T>(t:Tree): multiset<T>
{
match t
	case Empty => multiset{}
	case Node(l,x,r) => multiset{x} + multiset_of_tree(l)
	                                + multiset_of_tree(r)
}

lemma {:induction false} multisetTree_Lemma<T>(t:Tree)
	ensures multiset_of_tree(mirror(t)) == multiset_of_tree(t)
    {
        match t 
            case Empty => {}
            case Node(l,d,r) => {
                                calc {
                                        multiset_of_tree(mirror(t));
                                        {multisetTree_Lemma(l);multisetTree_Lemma(r);}
                                        multiset_of_tree(t);
                                    }
                                } 
	                   
    }
// Ejercicio 