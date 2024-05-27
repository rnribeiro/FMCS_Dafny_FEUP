include "Partition.dfy"

method Main() {
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 5, 3, 7, 6, 2, 8, 1, 9, 4, 7;
  assert A[0..] == [5, 3, 7, 6, 2, 8, 1, 9, 4, 7];
  var s, l, X := 3, 7, 6;
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