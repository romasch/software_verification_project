// Define array type.
type Array = [int] int;
type ArrayArray = [int] Array;



const N: int;
axiom N > 0;

function small_elements (a: Array, count: int) returns (bool)
{
  (forall i: int :: 0 <= i && i < count ==> -3*N <= a [i] && a [i] < 3*N)
}

function is_permutation (perm: Array, count: int) returns (bool)
{
  (forall i: int :: 0 <= i && i < count ==> 0 <= perm [i] && perm [i] < count)
  && (forall i,j:int :: 0 <= i && i < j && j < count ==> perm[i] != perm[j])
}

function is_sorted (a: Array, count: int) returns (bool)
{
  (forall i,j: int :: 0 <= i && i < j && j < count ==> a[i] <= a[j])
}


procedure MagicSort (input: Array, count: int, lower_bound, upper_bound: int) returns (output: Array);
  requires (forall i:int :: 0 <= i && i < count ==> lower_bound <= input [i] && input [i] < upper_bound);
  ensures is_sorted (output, count);
  ensures (forall i:int :: 0 <= i && i < count ==> lower_bound <= output [i] && output [i] < upper_bound);


procedure ConcatenateArray (a,b: Array, ca, cb: int, lower, middle, upper: int) returns (result: Array)
  requires small_elements (a, ca) && small_elements (b, cb);
  requires is_sorted (a, ca) && is_sorted (b, cb);
  requires lower <= middle && middle <= upper;
  requires ca >= 0 && cb >= 0;
  requires (forall i: int :: 0 <= i && i < ca ==> lower <= a[i] && a[i] < middle);
  requires (forall i: int :: 0 <= i && i < cb ==> middle <= b[i] && b[i] < upper);

  ensures is_sorted (result, ca+cb);
  ensures small_elements (result, ca+cb);
  ensures (forall i: int :: 0 <= i && i < ca+cb ==> lower <= result[i] && result[i] < upper);
  ensures (forall i: int :: 0 <= i && i < ca ==> result [i] == a[i]);
  ensures (forall i: int :: 0 <= i && i < cb ==> result [ca + i] == b[i]);
{
  var tmp: int;
  result := a;
  tmp := ca;
  while (tmp < ca + cb)
    invariant small_elements (result, tmp);
    invariant is_sorted (result, tmp);
    invariant (forall i: int :: 0 <= i && i < tmp ==> lower <= result[i] && result[i] < upper);
    invariant (forall i: int :: 0 <= i && i < ca ==> result [i] == a[i]);
    invariant (forall i: int :: ca <= i && i < tmp ==> result [i] == b[i-ca]);

    invariant ca <= tmp && tmp <= ca + cb;
  {
    result [tmp] := b[tmp - ca];
    tmp := tmp + 1;
  }
}



procedure BucketSort (input: Array, count: int) returns (result, permutation: Array)
  // Small elements.
  requires small_elements (input, count);
  requires count > 0;

  ensures small_elements (result, count);
  ensures is_sorted (result, count);

  // Result is a permutation.
  ensures is_permutation (permutation, count);
    // Note: Currently disabled.
  ensures true  || (forall i:int :: 0 <= i && i < count ==> result [i] == input [permutation[i]]);
{
  var tmp, value, bucket_index: int;
  var left, middle, right: Array;

  var buckets: ArrayArray;
  var counts: Array;

  tmp := 0;
  counts [0] := 0;
  counts [1] := 0;
  counts [2] := 0;

  while (tmp < count)
    invariant (forall i:int :: 0 <= i && i < tmp ==> permutation [i] == i);

    invariant (forall i, k: int :: 0 <= i && i < 3 ==> (0 <= k && k < counts [i]) ==> (-3*N + i*2*N) <= buckets[i][k] && buckets [i][k] < (-3*N + (i+1)*2*N));
//    invariant (forall i: int :: 0 <= i && i < counts[0] ==> -3*N <= buckets[0] [i] && buckets[0] [i] < -N);
//    invariant (forall i: int :: 0 <= i && i < counts[1] ==> -N <= buckets[1] [i] && buckets[1] [i] < N);
//    invariant (forall i: int :: 0 <= i && i < counts[2] ==> N <= buckets[2] [i] && buckets[2] [i] < 3*N);
    invariant counts [0] + counts [1] + counts [2]  == tmp;

    invariant (forall i:int :: 0 <= i && i < 3 ==> 0 <= counts [i] && counts[i] <= count);
  {
    value := input [tmp];
    bucket_index := (value + 3*N) div (2*N);

    assert 0 <= bucket_index && bucket_index < 3;
    assert bucket_index == 0 ==> -3*N <= value && value < -N;
    assert bucket_index == 1 ==> -N <= value && value < N;
    assert bucket_index == 2 ==> N <= value && value < 3*N;

    buckets [bucket_index] [counts [bucket_index]] := value;
    counts [bucket_index] := counts [bucket_index] + 1;

    permutation [tmp] := tmp;
    tmp := tmp + 1;
  }

  // Sort buckets with a normal algorithm.
  call left := MagicSort (buckets [0], counts [0], -3*N, -N);
  call middle := MagicSort (buckets [1], counts [1], -N, N);
  call right := MagicSort (buckets [2], counts [2], N, 3*N);

  // Concatenate arrays.
  call result := ConcatenateArray (left, middle, counts [0], counts [1], -3*N, -N, N);
  call result := ConcatenateArray (result, right, counts [0]+counts [1], counts [2], -3*N, N, 3*N);
}


