/*
  Class CircularArray.
*/
class {:autocontracts} CircularArray {
  /*
    Implementation
  */
  var a: array<int>; // The array.
  var startIndex: nat; // The index of the first element.
  var currentIndex: nat; // The index to put the next element.
  var count: nat; // The number of elements in the queue.

  /*
    Abstraction.
  */
  ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    a.Length > 0 &&
    0 <= startIndex < a.Length &&
    0 <= currentIndex < a.Length &&
    0 <= count <= a.Length &&
    count == |Elements| &&
    forall i :: 0 <= i < count ==> Elements[i] == a[(startIndex + i) % a.Length] &&
  }

  /*
    Constructor.
  */
  constructor EmptyQueue()
    ensures Valid()
    ensures a.Length == 10
    ensures startIndex == 0
    ensures currentIndex == 0
    ensures count == 0
    ensures Elements == []
  {
    a := new int[10];
    startIndex := 0;
    currentIndex := 0;
    count := 0;
    Elements := [];
  }

  /*
    Enqueue method.
  */
  // method Enqueue(element: int)
  //   requires Valid()
  //   ensures Valid()
  //   ensures Elements == old(Elements) + [element]
  // {
  //   if (count == a.Length) {
  //     /*
  //       Size limit reached, create a bigger array and transfer the elements.
  //     */
  //     var newA := new int[a.Length + 10];
  //     var i := 0;
  //     while (i < a.Length)
  //       decreases a.Length - i
  //       invariant 0 <= i <= a.Length < newA.Length
  //       invariant forall j :: (0 <= j < i) ==> (a[(j + startIndex) % a.Length] == newA[j])
  //     {
  //       newA[i] := a[(i + startIndex) % a.Length];
  //       i := i + 1;
  //     }
  //     /*
  //       Update the fields.
  //     */
  //     a := newA;
  //     startIndex := 0;
  //     currentIndex := count;
  //   }
  //   /*
  //     Go back to the beginning of the array if the end is reached.
  //   */
  //   if (currentIndex >= a.Length) {
  //     currentIndex := 0;
  //   }
  //   /*
  //     Add the element to the array.
  //   */
  //   a[currentIndex] := element;
  //   currentIndex := currentIndex + 1;
  //   count := count + 1;

  //   /*
  //     Go back to the beginning of the array if the end is reached.
  //   */
  //   if (currentIndex >= a.Length) {
  //     currentIndex := 0;
  //   }
    
  //   /*
  //     Update the abstraction.
  //   */
  //   Elements := Elements + [element];
  // }

  /*
    Contains method.
  */
  method Contains(element: int) returns (r: bool)
    requires Valid()
    ensures Valid()
    ensures r == (element in Elements)
  {
    r := false;
    var i := 0;
    while (i < count)
      decreases count - i
      invariant 0 <= i <= count
      invariant r == (element in Elements[0..i])
    {
      if (a[(i + startIndex) % a.Length] == element) {
        r := true;
      }
      i := i + 1;
    }
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == count
  {
    count
  }

  /*
    IsEmpty function.
  */
  function IsEmpty(): bool
    ensures IsEmpty() == (count == 0)
  {
    count == 0
  }
}
