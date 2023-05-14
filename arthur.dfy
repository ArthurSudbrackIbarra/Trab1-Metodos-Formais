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
    0 <= start < arr.Length &&
    0 <= size <= arr.Length &&
    Elements == (arr[..] + arr[..])[start..start + size] // Double the array and take the slice.
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
    Contains method.
  */
  function Contains(e: int): bool
    requires Valid()
    ensures Valid()
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