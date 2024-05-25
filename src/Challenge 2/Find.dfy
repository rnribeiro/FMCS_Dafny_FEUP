include "../Challenge 1/Partition.dfy"

method FindKSmallest(A: array<int>, K: int) returns (s: int, l: int, done: bool)
  requires 1 <= K <= A.Length
  modifies A
  ensures 0 <= s < K <= l <= A.Length
  ensures forall i, j :: 0 <= i < s && s <= j < A.Length ==> A[i] < A[j]
  ensures forall i, j :: 0 <= i < l && l <= j < A.Length ==> A[i] < A[j]
  ensures done ==> forall i, j :: s <= i < l && s <= j < l ==> A[i] == A[j]
  // ensures done ==> forall i, j :: 0 <= i < K && K <= j < A.Length ==> A[i] <= A[j]
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

// method Main() {
//   var A := new int[10];
//   A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 5, 3, 7, 6, 2, 8, 1, 9, 4, 7;
//   assert A[0..] == [5, 3, 7, 6, 2, 8, 1, 9, 4, 7];
//   print "Final array: ", A[..], "\n";
//   var K := 5;
//   var s, l := 0, A.Length;

//   var m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }

//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }

//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }

//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }

//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }


//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }

//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }

//   m, n := Partition(A, s, l, A[K-1]);
//   print "m = ", m,", n = ", n, "\n";
//   print "Final array: ", A[..], "\n";
//   if n < K {
//     s := n;
//   } else if m < K <= n {
//     s, l := m, n;
//   } else if K <= m {
//     l := m;
//   }


// }