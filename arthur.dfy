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
  {
    if (size == arr.Length) {
      var newArr := new int[arr.Length + 10];
      var i := 0;
      while (i < size)
        decreases size - i
        invariant 0 <= i <= size < newArr.Length
        invariant newArr.Length == arr.Length + 10
        invariant forall j :: 0 <= j < i ==> newArr[j] == arr[(start + j) % arr.Length]
      {
        newArr[i] := arr[(start + i) % arr.Length];
        i := i + 1;
      }
      arr := newArr;
      start := 0;
    }
    arr[(start + size) % arr.Length] := e;
    size := size + 1;
    Elements := Elements + [e];
  }

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