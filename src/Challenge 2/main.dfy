include "../Challenge 1/Partition.dfy"
include "Find.dfy"


method Main() {
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 40, 20, 10, 8, 2, 7, 9, 10, -1, 19;

  // assert A[0..] == [5, 3, 7, 6, 2, 8, 1, 9, 4, 7];
  print "Initial array: ", A[..], "\n";
  var K := 6;
  var s, l, done := 0, A.Length, false;
  print "s = ", s,", l = ", l, "\n";

  var i := 0;

  print "\nEntering interation ", i, "\n";
  print "All invariants are " , invariants(A, s, l, done, K), "\n";

  var m, n := Partition(A, s, l, A[K-1]);
  print "Final array: ", A[..], "\n";
  print "m = ", m,", n = ", n, "\n";

  if n < K {
    s := n;
  } else if m < K <= n {
    s, l, done := m, n, true;
  } else if K <= m {
    l := m;
  }
  print "after if-else \n";
  print "s = ", s,", l = ", l, "\n";

  print "done == ", done, "\n";
  print "All invariants are " , invariants(A, s, l, done, K), "\n\n\n";


  i := i + 1;
  print "\nEntering interation ", i, "\n";
  print "All invariants are " , invariants(A, s, l, done, K), "\n";

  m, n := Partition(A, s, l, A[K-1]);
  print "Final array: ", A[..], "\n";
  print "m = ", m,", n = ", n, "\n";

  if n < K {
    s := n;
  } else if m < K <= n {
    s, l, done := m, n, true;
  } else if K <= m {
    l := m;
  }
  print "after if-else \n";
  print "s = ", s,", l = ", l, "\n";
  print "done == ", done, "\n";
  print "All invariants are " , invariants(A, s, l, done, K), "\n\n\n";


  i := i + 1;
  print "\nEntering interation ", i, "\n";
  print "All invariants are " , invariants(A, s, l, done, K), "\n";

  m, n := Partition(A, s, l, A[K-1]);
  print "Final array: ", A[..], "\n";
  print "m = ", m,", n = ", n, "\n";

  if n < K {
    s := n;
  } else if m < K <= n {
    s, l, done := m, n, true;
  } else if K <= m {
    l := m;
  }
  print "after if-else \n";
  print "s = ", s,", l = ", l, "\n";
  print "done == ", done, "\n";
  print "All invariants are " , invariants(A, s, l, done, K), "\n\n\n";

}

predicate invariants(A: array<int>, s: int, l: int, done: bool, K: int)
  reads A
{
  (0 <= s < K <= l <= A.Length)
  &&
  (forall i, j :: 0 <= i < s && s <= j < A.Length ==> A[i] < A[j])
  &&
  (forall i, j :: 0 <= i < l && l <= j < A.Length ==> A[i] < A[j])
  &&
  (done ==> forall i, j :: s <= i < l && s <= j < l ==> A[i] == A[j])
}