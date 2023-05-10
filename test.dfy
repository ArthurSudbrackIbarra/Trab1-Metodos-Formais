method Main()
{
    var a := new int[5];
    a[0] := 1;
    a[1] := 2;
    a[2] := 3;
    a[3] := 4;
    a[4] := 5;
    var startIndex := 0;
    var endIndex := 0;
    var s:seq<int> := [];
    if (startIndex < endIndex)
    {
        s := a[startIndex..endIndex];
    } else {
        s := a[startIndex..a.Length] + a[0..endIndex];
    }
    print s;
    var d := [1,2,3];
    print d[0..2];
}
