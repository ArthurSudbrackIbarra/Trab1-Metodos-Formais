class {:autocontracts} CircularArray {

  // Implementation.
  var arr: array<int>;
  var maxAmount: nat;
  var tailIndex: nat;

  // Abstraction.
  ghost var Content: seq<int>;
  ghost var MaxAmount: nat;

  // Class invariant.
  ghost predicate Valid()
    {
      maxAmount > 0 &&
      arr.Length == maxAmount &&
      0 <= tailIndex <= maxAmount &&
      Content == arr[0..tailIndex] &&
      MaxAmount == maxAmount
    }

  // Constructor.
  constructor CircularArray(initialSize: int)
    requires initialSize > 0;
    ensures Valid();
    ensures Content == [];
    ensures MaxAmount == initialSize;
  {
    arr := new int[initialSize];
    tailIndex := 0;
    maxAmount := initialSize;
    MaxAmount := initialSize;
    Content := [];
  }
}

method Main()
{
  var a := [1,2,3][0..0];
}