
class {:autocontracts} CircularArray
{
  // Abstraction.
  ghost var Contents: seq<int>;
  ghost var Start: int;
  ghost var Size: int;

  // Implementation.
  var arr: array<int>;
  var capacity: int;

  // Class Invariant.
  ghost predicate Valid()
  {
    Size >= 0 && Size <= capacity &&
    Start >= 0 && Start < capacity &&
    |Contents| == capacity &&
    (forall i :: 0 <= i < Size ==> Contents[(Start + i) % capacity] == arr[(Start + i) % capacity]) &&
    (forall i :: Size <= i < capacity ==> Contents[i] == 0)
  }

  // Constructor.
  constructor(capacity: int)
    requires capacity > 0
    ensures |Contents| == capacity && Contents[..] == 0[..]
    ensures this.capacity == capacity
    ensures Start == 0
    ensures Size == 0
    ensures Valid()
  {
    arr := new int[capacity];
    Contents := [];
  }

  method Get(index: int) returns (result: int)
    requires 0 <= index < Size
    requires Valid()
    ensures result == Contents[(Start + index) % capacity]
    ensures Valid()
  {
    result := arr[(Start + index) % capacity];
  }

  method Set(index: int, value: int)
    requires 0 <= index < Size
    requires Valid()
    modifies arr
    ensures arr[(Start + index) % capacity] == value
    ensures Contents[(Start + index) % capacity] == value
    ensures Valid()
  {
    arr[(Start + index) % capacity] := value;
    Contents[(Start + index) % capacity] := value;
  }

  method Add(value: int)
    requires Valid()
    requires Size < capacity
    modifies arr
    ensures Size == old(Size) + 1
    ensures Contents[(Start + Size - 1) % capacity] == value
    ensures Valid()
  {
    arr[(Start + Size) % capacity] := value;
    Contents := Contents[0..(Start + Size) % capacity] + [value] + Contents[(Start + Size) % capacity + 1..];
    Size := Size + 1;
  }

  method Remove()
    requires Valid()
    requires Size > 0
    modifies arr
    ensures Size == old(Size) - 1
    ensures Start == (old(Start) + 1) % capacity
    ensures Valid()
  {
    Contents := Contents[0..Start] + [0] + Contents[Start + 1..];
    Start := (Start + 1) % capacity;
    Size := Size - 1;
  }

  method IsEmpty() returns (result: bool)
    requires Valid()
    ensures result == (Size == 0)
    ensures Valid()
  {
    result := Size == 0;
  }

  method IsFull() returns (result: bool)
    requires Valid()
    ensures result == (Size == capacity)
    ensures Valid()
  {
    result := Size == capacity;
  }

  method Clear()
    requires Valid()
    modifies arr
    ensures Size == 0
    ensures Contents[..] == 0[..]
    ensures Start == 0
    ensures Valid()
  {
    arr := new int[capacity];
    Contents := [];
    Size := 0;
    Start := 0;
  }
}