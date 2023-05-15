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
  ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    arr.Length > 0 &&
    0 <= start < arr.Length &&
    0 <= size <= arr.Length &&
    size == |Elements| &&
    Elements == (arr[..] + arr[..])[start..start + size]
  }

  /*
    Constructor.
  */
  constructor EmptyQueue()
    ensures Valid()
    ensures arr.Length == 10
    ensures start == 0
    ensures size == 0
    ensures Elements == []
  {
    arr := new int[10];
    start := 0;
    size := 0;
    Elements := [];
  }

  /*
    Enqueue Method
  */
  method Enqueue(e: int)
    requires Valid()
    ensures Valid()
    ensures Elements == old(Elements) + [e]

  /*
    Dequeue method.
  */
  method Dequeue() returns (e: int)
    requires Valid()
    requires size > 0
    requires |Elements| > 0
    ensures Valid()
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
    Contains method.
  */
  function Contains(e: int): bool
    ensures Contains(e) == (e in Elements)
  {
    e in (arr[..] + arr[..])[start..start + size]
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == size
  {
    size
  }

  /*
    IsEmpty function.
  */
  function IsEmpty(): bool
    ensures IsEmpty() == (size == 0)
  {
    size == 0
  }

  /*
    Concatenate method.
  */
  method Concatenate(q1: CircularArray) returns(q2: CircularArray)
    requires Valid()
    requires q1.Valid()
    ensures Valid()
    ensures q2.Valid()
    ensures q2.Elements == Elements + q1.Elements
    ensures fresh(q2)
  {
    q2 := new CircularArray.EmptyQueue();
    var i := 0;
    while i < size
      decreases size - i
      invariant 0 <= i <= size == |Elements|
      invariant q2.Elements == Elements[..i]
    {
      q2.Enqueue(arr[(start + i) % arr.Length]);
      i := i + 1;
    }
    i := 0;
    while i < q1.size
      decreases q1.size - i
      invariant 0 <= i <= q1.size == |q1.Elements|
      invariant q2.Elements == Elements + q1.Elements[..i]
    {
      q2.Enqueue(q1.arr[(q1.start + i) % q1.arr.Length]);
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
  var q := new CircularArray.EmptyQueue();
  assert q.Size() == 0;
  var c := q.Contains(0);
  print c;
}