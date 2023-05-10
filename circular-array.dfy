/*
  Class CircularArray.
*/
class {:autocontracts} CircularArray {

  /*
    Implementation.
  */
  var arr: array<int>;
  var startIndex: nat;
  var nextIndex: nat;
  var elementsCount: nat;

  /*
    Abstraction.
  */
  ghost var Content: seq<int>;

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    0 <= startIndex <= arr.Length &&
    0 <= nextIndex <= arr.Length &&
    elementsCount <= arr.Length &&
    (startIndex <= nextIndex ==> Content == arr[startIndex..nextIndex]) &&
    (startIndex > nextIndex ==> Content == arr[startIndex..arr.Length] + arr[0..nextIndex])
  }

  /*
    Constructor.
  */
  constructor WithInitialCapacity(initialCapacity: nat)
    requires initialCapacity > 0
    ensures Valid()
    ensures arr.Length == initialCapacity
    ensures startIndex == 0
    ensures nextIndex == 0
    ensures elementsCount == 0
    ensures Content == []
  {
    arr := new int[initialCapacity];
    startIndex := 0;
    nextIndex := 0;
    elementsCount := 0;
    Content := [];
  }

  /*
    Methods.
  */

  /*
    Enqueue
  */
  method Enqueue(element: int)
    requires Valid()
    ensures Valid()
    ensures elementsCount == old(elementsCount) + 1
  {
    /*
      If the next index is equal to the length of the array, then we need to
      reset it to 0.
    */
    if (nextIndex == arr.Length)
    {
      nextIndex := 0;
    }
    /*
      If the array is full, then we need to create a new array with double
      the capacity of the current array.
    */
    if (elementsCount == arr.Length)
    {
      var newArr := new int[arr.Length * 2];
      var i := 0;
      var j := startIndex;
      while (i < arr.Length)
        invariant 0 <= i <= arr.Length <= newArr.Length
        decreases arr.Length - i
      {
        newArr[i] := arr[j % arr.Length];
        i := i + 1;
        j := j + 1;
      }
      nextIndex := arr.Length;
      startIndex := 0;
      arr := newArr;
    }
    /*
      Add the element to the array.
    */
    arr[nextIndex] := element;
    /*
      Update variables.
    */
    nextIndex := nextIndex + 1;
    elementsCount := elementsCount + 1;
    if (startIndex <= nextIndex)
    {
      Content := arr[startIndex..nextIndex];
    } else
    {
      Content := arr[startIndex..arr.Length] + arr[0..nextIndex];
    }
  }

}

method Main()
{
  var queue := new CircularArray.WithInitialCapacity(5);
  queue.Enqueue(1);
  queue.Enqueue(2);
  print queue.arr;
}
