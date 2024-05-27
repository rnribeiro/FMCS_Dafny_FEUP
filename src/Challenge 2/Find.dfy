include "../Challenge 1/Partition.dfy"

// Method to find the k smallest elements in an array.
method FindKSmallest(A: array<int>, K: int) returns (s: int, l: int, done: bool)
  // K must be between 1 and the length of the array.
  requires 1 <= K <= A.Length
  // A may be modified
  modifies A
  // Indices s and l will be set correctly.
  ensures 0 <= s < K <= l <= A.Length
  // Elements before s are less than or equal to elements from s to end.
  ensures forall i, j :: 0 <= i < s && s <= j < A.Length ==> A[i] < A[j]
  // Elements before l are less than or equal to elements from l to end.
  ensures forall i, j :: 0 <= i < l && l <= j < A.Length ==> A[i] < A[j]
  // If done, all elements between s and l are equal.
  ensures done ==> forall i, j :: s <= i < l && s <= j < l ==> A[i] == A[j]
  // If done, all K smallest elements are in the correct place.
  ensures done ==> forall i, j :: 0 <= i < K && K <= j < A.Length ==> A[i] <= A[j]
  // Multiset of elements in A remains unchanged.
  ensures multiset(A[..]) == old(multiset(A[..]))
{
  // Initial setup: set s to 0, l to the length of the array, and done to true if array length is 1 or less.
  s, l, done := 0, A.Length, (A.Length <= 1);

  // Loop until the k smallest elements are found.
  while !done
    // The loop body should either set done to true or narrow down the range of s and l
    decreases l - s, !done
    // Invariant maintaining correct range of s and l
    invariant 0 <= s < K <= l <= A.Length
    // Invariant maintaining order for elements before s
    invariant forall i, j :: 0 <= i < s && s <= j < A.Length ==> A[i] < A[j]
    // Invariant maintaining order for elements before l.
    invariant forall i, j :: 0 <= i < l && l <= j < A.Length ==> A[i] < A[j]
    // Invariant for equality of elements between s and l if done.
    invariant (done ==> forall i, j :: s <= i < l && s <= j < l ==> A[i] == A[j])
    // Invariant for maintaining multiset of elements.
    invariant multiset(A[..]) == old(multiset(A[..]))
  {
    // Choose a pivot element, X, as the (K-1)-th element.
    var X := A[K-1];

    // Partition the array around the pivot X.
    var m, n := Partition(A, s, l, X);

    // Update s or l based on the results of the partition to narrow down the range.
    if n < K {
      s := n; // Narrow the lower bound of the range.
    } else if m < K <= n {
      s, l, done := m, n, true; // Found the correct partition, set done to true.
    } else if K <= m {
      l := m; // Narrow the upper bound of the range.
    }
  }

}
