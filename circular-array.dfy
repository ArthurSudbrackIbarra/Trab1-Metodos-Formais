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
    0 <= this.startIndex <= this.arr.Length &&
    0 <= this.nextIndex <= this.arr.Length &&
    this.elementsCount <= this.arr.Length &&
    this.elementsCount == |this.Content| &&
    this.elementsCount == 0 ==> this.Content == [] &&
    (this.startIndex < this.nextIndex && this.elementsCount > 0 ==> this.Content == this.arr[this.startIndex..this.nextIndex]) &&
    (this.startIndex >= this.nextIndex && this.elementsCount > 0 ==> this.Content == this.arr[this.startIndex..this.arr.Length] + this.arr[0..this.nextIndex])
  }

  /*
    Constructor.
  */
  constructor WithInitialCapacity(initialCapacity: nat)
    requires initialCapacity > 0
    ensures Valid()
    ensures this.arr.Length == initialCapacity
    ensures this.startIndex == 0
    ensures this.nextIndex == 0
    ensures this.elementsCount == 0
    ensures this.Content == []
  {
    this.arr := new int[initialCapacity];
    this.startIndex := 0;
    this.nextIndex := 0;
    this.elementsCount := 0;
    this.Content := [];
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
  {
    /*
      If the array is full, then we need to create a new array with a larger
      capacity and copy the elements from the old array to the new array.
    */
    if (this.elementsCount == this.arr.Length)
    {
      var newArr := new int[this.arr.Length + 10];
      var i := 0;
      var j := this.startIndex;
      while (i < this.arr.Length)
        decreases this.arr.Length - i
        invariant 0 <= i <= this.arr.Length <= newArr.Length
      {
        newArr[i] := arr[j % arr.Length];
        i := i + 1;
        j := j + 1;
      }
      this.startIndex := 0;
      this.nextIndex := i;
      this.arr := newArr;
    }
    /*
      If the next index is equal to the length of the array, then we need to
      reset it to 0.
    */
    if (nextIndex >= arr.Length)
    {
      this.nextIndex := 0;
    }
    /*
      Add the element to the array.
    */
    this.arr[this.nextIndex] := element;
    /*
      Update variables.
    */
    this.nextIndex := nextIndex + 1;
    this.elementsCount := elementsCount + 1;
    if (startIndex < nextIndex)
    {
      this.Content := arr[startIndex..nextIndex];
    } else
    {
      this.Content := arr[startIndex..arr.Length] + arr[0..nextIndex];
    }
  }

}

method Main()
{
  var queue := new CircularArray.WithInitialCapacity(5);
  //queue.Enqueue(1);
  //queue.Enqueue(2);
  print queue.arr;
}
