/*
  Class CircularArray.
*/
class {:autocontracts} CircularArray {
  /*
    Implementation
  */
  var arr: array<int>; // The array.
  var start: nat; // The index of the first element.
  var size: nat; // The number of elements in the queue.

  /*
    Abstraction.
  */
  ghost const Capacity: nat; // The capacity of the queue. (WE WERE UNABLE TO MAKE THE SIZE OF THE ARRAY DYNAMIC).
  ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    0 <= start < arr.Length &&
    0 <= size <= arr.Length &&
    Capacity == arr.Length &&
    Elements == if start + size <= arr.Length
                then arr[start..start + size]
                else arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Constructor.
  */
  constructor EmptyQueue(capacity: nat)
    requires capacity > 0
    ensures Elements == []
    ensures Capacity == capacity
  {
    arr := new int[capacity];
    start := 0;
    size := 0;
    Capacity := capacity;
    Elements := [];
  }

  /*
    Enqueue Method
  */
  method Enqueue(e: int)
    requires !IsFull()
    ensures Elements == old(Elements) + [e]
  {
    arr[(start + size) % arr.Length] := e;
    size := size + 1;
    Elements := Elements + [e];
  }

  /*
    Dequeue method.
  */
  method Dequeue() returns (e: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
  {
    e := arr[start];
    if start + 1 < arr.Length {
      start := start + 1;
    }
    else {
      start := 0;
    }
    size := size - 1;
    Elements := Elements[1..];
  }

  /*
    Contains predicate.
  */
  predicate Contains(e: int)
    ensures Contains(e) == (e in Elements)
  {
    if start + size < arr.Length then
      e in arr[start..start + size]
    else
      e in arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == |Elements|
  {
    size
  }

  /*
    IsEmpty predicate.
  */
  predicate IsEmpty()
    ensures IsEmpty() <==> (|Elements| == 0)
  {
    size == 0
  }

  /*
    IsFull predicate.
  */
  predicate IsFull()
    ensures IsFull() <==> |Elements| == Capacity
  {
    size == arr.Length
  }

  /*
    Concatenate method.
  */
  method Concatenate(q1: CircularArray) returns(q2: CircularArray)
    requires q1.Valid()
    requires q1 != this
    ensures q2.Valid()
    ensures fresh(q2)
    ensures q2.Capacity == Capacity + q1.Capacity + 10
    {
      var s1 := if start + size <= arr.Length
                then arr[start..start + size]
                else arr[start..] + arr[..size - (arr.Length - start)];
      var s2 := if q1.start + q1.size <= q1.arr.Length
                then q1.arr[q1.start..q1.start + q1.size]
                else q1.arr[q1.start..] + q1.arr[..q1.size - (q1.arr.Length - q1.start)];
      var elements := s1 + s2;
      var newCapacity := arr.Length + q1.arr.Length + 10;
      q2 := new CircularArray.EmptyQueue(newCapacity);
      var i := 0;
      while i < |elements|
        invariant 0 <= i <= |elements|
        invariant q2.Valid()
        invariant q2.Elements == elements[..i]
        invariant q2.Capacity == newCapacity
      {
        q2.Enqueue(elements[i]);
        i := i + 1;
      }
    }
    
}

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/
method Main()
{
  var q := new CircularArray.EmptyQueue(3);
  q.Enqueue(1);
  assert !q.IsEmpty();
  assert q.Size() == 1;
  assert q.Contains(1);
}
