method Partition(A: array<int>, s: int, l: int, X: int) returns (m: int, n: int)
  // ensures that the given indices are within valid array bounds
  requires 0 <= s <= l <= A.Length
  modifies A
  decreases l - s
  // ensures m and n are within the bounds of the segment [s, l]
  ensures 0 <= s <= m <= n <= l <= A.Length
  // all elements in the segment [s, m) are less than X
  ensures forall i :: s <= i < m ==> A[i] < X
  // all elements in the segment [m, n) are equal to X
  ensures forall i :: m <= i < n ==> A[i] == X
  // all elements in the segment [n, l) are greater than X
  ensures forall i :: n <= i < l ==> A[i] > X
  // elements outside the segment [s, l) remain unchanged
  ensures forall i :: 0 <= i < s || l <= i < A.Length ==> old(A[i]) == A[i]
  // the multiset (bag of elements) of the array remains the same, preserving element count
  ensures multiset(A[..]) == old(multiset(A[..]))
{
  // initialize m and n to the start of the segment
  m, n := s, s;
  // initialize x to the end of the segment
  var x := l;

  while n < x
    // maintain the bounds of m, n, and x within the segment [s, l)
    invariant s <= m <= n <= x <= l
    // elements in the segment [s, m) are less than X
    invariant forall i :: s <= i < m ==> A[i] < X
    // elements in the segment [m, n) are equal to X
    invariant forall i :: m <= i < n ==> A[i] == X
    // elements in the segment [x, l) are greater than X
    invariant forall i :: x <= i < l ==> A[i] > X
    // elements outside the segment [s, l) remain unchanged
    invariant forall i :: 0 <= i < s || l <= i < A.Length ==> old(A[i]) == A[i]
    // the multiset of the array remains unchanged
    invariant multiset(A[..]) == old(multiset(A[..]))
  {
    if A[n] < X {
      // If the current element A[n] is less than X:
      // Swap A[m] and A[n] to move the element to the less-than-X segment.
      // This maintains the invariant forall i :: s <= i < m ==> A[i] < X because A[m] < X after the swap.
      A[m], A[n] := A[n], A[m];
      // Increment both m and n.
      // m is incremented to include the new element less than X in the less-than-X segment.
      // n is incremented to process the next element.
      m, n := m+1, n+1;
    } else if A[n] == X {
      // If the current element A[n] is equal to X:
      // Simply increment n to expand the equal-to-X segment.
      // This maintains the invariant forall i :: m <= i < n ==> A[i] == X.
      n := n+1;
    } else {
      // If the current element A[n] is greater than X:
      // Decrement x to expand the greater-than-X segment.
      x := x - 1;
      // Swap A[n] and A[x] to move the element to the greater-than-X segment.
      // This maintains the invariant forall i :: x <= i < l ==> A[i] > X because A[x] > X after the swap.
      A[n], A[x] := A[x], A[n];
      // n is not incremented because the new A[n] must be processed.
    }
  }
}