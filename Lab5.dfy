
datatype List<T> = Empty | Cons(head:T, tail:List)

function length<T>(xs:List<T>):int
    decreases xs
{
    if xs.Empty? then 0 else 1 + length(xs.tail)
}


datatype Tree<T> = Empty | Node(left:Tree,root:T,right:Tree)

function depth<T>(t:Tree):int
    decreases  t
{
    if t.Empty? then 0 else 1 + max(depth(t.left),depth(t.right))
}

function depth2<T>(t:Tree):int
    decreases  t
{
    match t {
        case Empty => 0
        case Node (l,_,r) =>  1 + max(depth(t.left),depth(t.right))
    }
}

function max(a:int, b:int):int
{
    if a < b then b else a
}