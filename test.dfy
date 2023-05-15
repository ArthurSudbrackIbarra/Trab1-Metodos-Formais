method Main()
{
    var a := new int[3];
    a[0] := 1;
    a[1] := 2;
    a[2] := 3;
    var start_a := 0;
    var size_a := 3;

    var b := new int[3];
    b[0] := 4;
    b[1] := 5;
    b[2] := 6;
    var start_b := 2;
    var size_b := 3;

    var s1 := if start_a + size_a <= a.Length
            then a[start_a..start_a + size_a]
            else a[start_a..] + a[..start_a - (a.Length - start_a)];

    print s1;

    var s2 := if start_b + size_b <= b.Length
            then b[start_b..start_b + size_b]
            else b[start_b..] + b[..start_b - (b.Length - start_b) + 1];

    print s2;

    var s3 := s1 + s2;

    print s3;
}
