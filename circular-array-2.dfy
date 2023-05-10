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
    var count: nat; // The number of elements.

    /*
      Abstraction.
    */
    ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

    /*
      Class invariant.
    */
    ghost predicate Valid()
    {
        0 <= startIndex <= a.Length &&
        0 <= currentIndex <= a.Length &&
        0 <= count <= a.Length &&
        count == |Elements| &&
        forall i: nat :: 0 <= i < count ==> Elements[i] == a[(startIndex + i) % a.Length]
    }

    /*
      Constructor.
    */
    constructor WithInitialCapacity(capacity: nat)
        requires capacity > 0
        ensures Valid()
    {
        a := new int[capacity];
        startIndex := 0;
        currentIndex := 0;
        count := 0;
        Elements := [];
    }

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
        while i < count
            invariant 0 <= i <= count
            invariant r == (element in Elements[0..i])
            decreases count - i
        {
            if (a[(startIndex + i) % a.Length] == element) {
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
}