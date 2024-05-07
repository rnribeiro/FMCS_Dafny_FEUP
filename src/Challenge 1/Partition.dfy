method Partition(a: array<int>, s: int, l: int, X: int) returns (m: int, n: int)
  requires 0 <= s <= l <= a.Length
  modifies a
  ensures 0 <= s <= m <= n <= l <= a.Length
  ensures forall i :: s <= i < m ==> a[i] < X
  ensures forall i :: m <= i < n ==> a[i] == X
  ensures forall i :: n <= i < l ==> a[i] > X
  ensures forall i :: 0 <= i < s || l <= i < a.Length ==> old(a[i]) == a[i]
{
  m, n := s, s;
  var x := l;

  while n < x
    invariant s <= m <= n <= x <= l
    invariant forall i :: s <= i < m ==> a[i] < X
    invariant forall i :: m <= i < n ==> a[i] == X
    invariant forall i :: x <= i < l ==> a[i] > X
    invariant forall i :: 0 <= i < s || l <= i < a.Length ==> old(a[i]) == a[i]
  {
    if a[n] < X {
      a[m], a[n] := a[n], a[m];
      m, n := m+1, n+1;
    } else if a[n] == X {
      n := n+1;
    } else {
      x := x - 1;
      a[n], a[x] := a[x], a[n];
    }
  }
}

method Main() {
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 5, 3, 7, 6, 2, 8, 1, 9, 4, 7;
  var s, l, X := 3, 7, 6;
  var m, n := Partition(a, s, l, X);
  assert m == 5;
  assert n == 6;
  print "m = ", m,", n = ", n, "\n";
  print "Final array: ", a[..], "\n";
  assert 0 <= s <= m <= n <= l <= a.Length;
  assert forall i | s <= i < m :: a[i] < X;
  assert forall i | m <= i < n :: a[i] == X;
  assert forall i | n <= i < l :: a[i] > X;
  assert a[..] == [5, 3, 7, 2, 1, 6, 8, 9, 4, 7];
  print a[..] == [5, 3, 7, 2, 1, 6, 8, 9, 4, 7];

}