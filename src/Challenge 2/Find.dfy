include "../Challenge 1/Partition.dfy"

method FindKSmallest(A: array<int>, K: int) returns (s: int, l: int, done: bool)
  requires 1 <= K <= A.Length
  modifies A
  ensures 0 <= s < K <= l <= A.Length
  ensures forall i, j :: 0 <= i < s && s <= j < A.Length ==> A[i] < A[j]
  ensures forall i, j :: 0 <= i < l && l <= j < A.Length ==> A[i] < A[j]
  ensures done ==> forall i, j :: s <= i < l && s <= j < l ==> A[i] == A[j]
  ensures done ==> forall i, j :: 0 <= i < K && K <= j < A.Length ==> A[i] <= A[j]
  ensures multiset(A[..]) == old(multiset(A[..]))

{
  s, l, done := 0, A.Length, (A.Length <= 1);

  while !done
    decreases l - s
    invariant 0 <= s < K <= l <= A.Length
    invariant forall i, j :: 0 <= i < s && s <= j < A.Length ==> A[i] < A[j]
    invariant forall i, j :: 0 <= i < l && l <= j < A.Length ==> A[i] < A[j]
    invariant (done ==> forall i, j :: s <= i < l && s <= j < l ==> A[i] == A[j])
    invariant multiset(A[..]) == old(multiset(A[..]))
  {
    var X := A[K-1];

    var m, n := Partition(A, s, l, X);

    if n < K {
      s := n;
    } else if m < K <= n {
      s, l, done := m, n, true;
    } else if K <= m {
      l := m;
    }
  }

}