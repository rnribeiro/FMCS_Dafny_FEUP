method Partition(A: array<int>, s: int, l: int, X: int) returns (m: int, n: int)
  requires 0 <= s <= l <= A.Length
  // requires exists i :: 0 <= i < A.Length && A[i] == X
  modifies A
  decreases l - s
  ensures 0 <= s <= m <= n <= l <= A.Length
  ensures forall i :: s <= i < m ==> A[i] < X
  ensures forall i :: m <= i < n ==> A[i] == X
  ensures forall i :: n <= i < l ==> A[i] > X
  ensures forall i :: 0 <= i < s || l <= i < A.Length ==> old(A[i]) == A[i]
  ensures multiset(A[..]) == old(multiset(A[..]))
{
  m, n := s, s;
  var x := l;

  while n < x
    invariant s <= m <= n <= x <= l
    invariant forall i :: s <= i < m ==> A[i] < X
    invariant forall i :: m <= i < n ==> A[i] == X
    invariant forall i :: x <= i < l ==> A[i] > X
    invariant forall i :: 0 <= i < s || l <= i < A.Length ==> old(A[i]) == A[i]
    invariant multiset(A[..]) == old(multiset(A[..]))
  {
    if A[n] < X {
      A[m], A[n] := A[n], A[m];
      m, n := m+1, n+1;
    } else if A[n] == X {
      n := n+1;
    } else {
      x := x - 1;
      A[n], A[x] := A[x], A[n];
    }
  }
}


method Main() {
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 5, 3, 7, 6, 2, 8, 1, 9, 4, 7;
  assert A[0..] == [5, 3, 7, 6, 2, 8, 1, 9, 4, 7];
  var s, l, X := 3, 7, A[6];
  var m, n := Partition(A, s, l, X);
  assert (A[0..] == [5, 3, 7, 2, 1, 6, 8, 9, 4, 7]
       || A[0..] == [5, 3, 7, 1, 2, 6, 8, 9, 4, 7]
       || A[0..] == [5, 3, 7, 2, 1, 6, 9, 8, 4, 7]
       || A[0..] == [5, 3, 7, 1, 2, 6, 9, 8, 4, 7]);
  assert m == 5;
  assert n == 6;
  print "m = ", m,", n = ", n, "\n";
  print "Final array: ", A[..], "\n";
  assert 0 <= s <= m <= n <= l <= A.Length;
  assert forall i | s <= i < m :: A[i] < X;
  assert forall i | m <= i < n :: A[i] == X;
  assert forall i | n <= i < l :: A[i] > X;

}