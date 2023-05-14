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
    forall i :: 0 <= i < count ==> Elements[i] == a[(startIndex + i) % a.Length]
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
  //    Elements := Elements + [element];
  // }

  //  method Dequeue() returns (value: int)
  //   requires Valid()
  //   ensures Valid()
  //   ensures 0 == old(count) ==> count == 0 && value == 0 
  //   ensures 0 < old(count) ==> count == old(count) - 1 && value == a[startIndex]
  // {
  //   if count <= 0 { 
  //     value := 0;
  //     return; 
  //   }
  //   value := a[startIndex];
  //   count := count - 1;
  //   if startIndex + 1 < a.Length {
  //     startIndex := startIndex + 1;
  //   } else {
  //     startIndex := 0;
  //   }
  //    if count > 0 { 
  //      Elements := Elements[1..];
  //      assert count == |Elements|;
  //       return; 
  //     }
  //   Elements := [];
  // }
  /*
    Contains method.
  */

  // wip- não apagar
  method Contains(key: int) returns (index: int)
    ensures 0 <= index ==> index < a.Length && a[index] == key
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  {
    index := 0;
    while index < a.Length
      invariant 0 <= index < a.Length
      invariant forall k :: 0 <= k < index ==> a[k] != key
    {
      if a[index] == key { return; }
      if index + 1 >= a.Length {
        index := -1;
        return;
      }
      index := index + 1;
    }
    index := -1;
  }

  // Esse aqui funciona e deve estar certo.
  method ContainsValid(key: int) returns (index: int)
    requires Valid()
    ensures Valid()
    ensures 0 <= index ==> index < a.Length && a[index] == key 
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  {
    index := 0;
    while index < a.Length 
      invariant 0 <= index < a.Length
      invariant forall k :: 0 <= k < index ==> a[k] != key
      {
      if a[index] == key {
        return;
      }
      if index + 1 >= a.Length {
        index := -1;
        return;
      }
      index := index + 1;
    }
    index := -1;
  }

  method ContainsAlternative(element: int) returns (r: bool)
    requires Valid()
    ensures Valid()
    ensures exists i :: 0 <= i < a.Length && a[i] == element <==> r == true
    ensures forall i :: 0 <= i < a.Length ==> a[i] != element <==> r == false
  {
    var i := 0;
    while (i < a.Length)
      decreases a.Length - i
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> a[j] != element <==> r == false
      invariant exists j :: 0 <= j < i && a[j] == element <==> r == true
    {
      if (a[i] == element) {
        r := true;
      }
      i := i + 1;
    }
  }

  // method Contains(element: int) returns (r: bool)
  //   requires Valid()
  //   ensures Valid()
  //   ensures r == (element in Elements)
  // {
  //   r := false;
  //   var i := 0;
  //   while (i < count)
  //     decreases count - i
  //     invariant 0 <= i <= count
  //     invariant r == (element in Elements[0..i])
  //   {
  //     if (a[(i + startIndex) % a.Length] == element) {
  //       r := true;
  //     }
  //     i := i + 1;
  //   }
  // }

  function min(x: int, y: int): int
    ensures min(x,y) <= x
    ensures min(x,y) <= y
    ensures min(x,y) == x || min(x,y) == y
  {
    if (x < y) then x
    else y
  }

  function max(x: int, y: int): int
    ensures max(x,y) >= x
    ensures max(x,y) >= y
  {
    if (x > y) then x
    else y
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

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/
method Main()
{
  var q := new CircularArray.EmptyQueue();
  var c := q.ContainsValid(80);
  print c;
}