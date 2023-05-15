type T = int // for demo purposes, but could be another type
 
class {:autocontracts} Deque {
    // (Private) concrete state variables 
    const list: array<T>; // circular array, from list[start] (front) to list[(start+size-1) % list.Length] (back) 
    var start : nat; 
    var size : nat;
    ghost var elems: seq<T>;  // front at head, back at tail
    ghost const capacity: nat;

    ghost predicate Valid()
    {
        // (i)
        size <= list.Length &&
        start < list.Length &&
        // (ii)
        capacity == list.Length &&
        elems == (list[..] + list[..])[start..start + size] //big brain ngl
    }
 
    constructor (capacity: nat) 
        requires capacity > 0
        ensures this.capacity == capacity && this.elems == []
    {
        list := new T[capacity];
        start := 0;
        size := 0;
        this.capacity := capacity;
        this.elems := [];
    }
 
    predicate isEmpty()
        ensures isEmpty() <==> |elems| == 0 //only here for documentation reasons
    {
        size == 0
    }
    
    predicate isFull()
        ensures isFull() <==> |elems| == capacity //only here for documentation reasons
    {
        size == list.Length
    }
 
    function front() : T
        requires !isEmpty()
        ensures front() == elems[0]
    {
        list[start]
    }
 
    function back() : T
        requires !isEmpty()
        ensures back() == elems[|elems| - 1]
    {
        list[(start + size - 1) % list.Length] 
    }
    
    // method push_back(x : T)
    //     requires |elems| < capacity
    //     ensures elems == old(elems) + [x]
    // {
    //     list[(start + size) % list.Length] := x;
    //     size := size + 1;
        
    //     elems := elems + [x];
    // }

    method push_front(x : T) 
        requires |elems| < capacity
        ensures elems == [x] + old(elems)
    {
        if start > 0 {
            start := start - 1;
        }
        else {
            start := list.Length - 1;
        }
        list[start] := x;
        size := size + 1;

        elems := [x] + elems;
    }    
 
    method pop_back()
    requires |elems| > 0
    ensures elems == old(elems[.. (|elems| - 1)])
    {
        size := size - 1;

        elems := elems[.. |elems| - 1];
    }
 
    
 
    method pop_front()
        requires |elems| > 0
        ensures elems == old(elems[1 ..])
    {
        if start + 1 < list.Length {
            start := start + 1;
        }
        else {
            start := 0;
        }
        size := size - 1;

        elems := elems[1 ..];
    } 
}
 
// A simple test scenario.
method Main()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    print q.list;
}
