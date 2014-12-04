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

procedure BucketSort (input: Array, count: int) returns (result, permutation: Array)
  // Small elements.
  requires small_elements (input, count);
  requires count > 0;

  ensures small_elements (result, count);
  ensures is_sorted (result, count);

  // Result is a permutation.
  ensures is_permutation (permutation, count);
  ensures (forall i:int :: 0 <= i && i < count ==> result [i] == input [permutation[i]]);
{
  var tmp, value, bucket_index: int;
  var left, middle, right: Array;
  var left_count, middle_count, right_count: int;

  var buckets: ArrayArray;
  var counts: Array;


  tmp := 0;
  left_count := 0;
  middle_count := 0;
  right_count := 0;

  counts [0] := 0;
  counts [1] := 0;
  counts [2] := 0;


  while (tmp < count)
    invariant (forall i:int :: 0 <= i && i < tmp ==> permutation [i] == i && input [i] == result [i]);

    invariant (forall i: int :: 0 <= i && i < left_count ==> -3*N <= left [i] && left [i] < -N);
    invariant (forall i: int :: 0 <= i && i < middle_count ==> -N <= middle [i] && middle [i] <= N);
    invariant (forall i: int :: 0 <= i && i < right_count ==> N < right [i] && right [i] <= 3*N);
    invariant left_count + middle_count + right_count  == tmp;

    invariant (forall i: int :: 0 <= i && i < counts[0] ==> -3*N <= buckets[0] [i] && buckets[0] [i] < -N);
    invariant (forall i: int :: 0 <= i && i < counts[1] ==> -N <= buckets[1] [i] && buckets[1] [i] < N);
    invariant (forall i: int :: 0 <= i && i < counts[2] ==> N <= buckets[2] [i] && buckets[2] [i] < 3*N);
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

    if (value < -N) {
      left [left_count] := value;
      left_count := left_count + 1;
    } else if (value <= N) {
      middle [middle_count] := value;
      middle_count := middle_count + 1;
    } else {
      right [right_count] := value;
      right_count := right_count + 1;
    }

    permutation [tmp] := tmp;
    result [tmp] := input [tmp];
    tmp := tmp + 1;
  }

  // Individual sort algorithms.
  //call left := MagicSort (left, left_count, -3*N, -N-1);
  //call middle := MagicSort (middle, middle_count, -N, N);
  //call right := MagicSort (right, right_count, N+1, 3*N);

  left_count := counts [0];
  middle_count := counts [1];
  right_count := counts [2];

  call left := MagicSort (buckets [0], counts [0], -3*N, -N-1);
  call middle := MagicSort (buckets [1], counts [1], -N, N-1);
  call right := MagicSort (buckets [2], counts [2], N, 3*N-1);

  // Concatenate arrays.
  tmp := 0;
  while (tmp < left_count)
    invariant small_elements (result, tmp);
    invariant is_sorted (result, tmp);
    invariant (forall i:int :: 0 <= i && i < tmp ==> result [i] == left [i]);
    invariant tmp <= left_count;
  {
    result [tmp] := left [tmp];
    tmp := tmp + 1;
  }

  while (tmp < left_count + middle_count)
    invariant small_elements (result, tmp);
    invariant is_sorted (result, tmp);
    invariant (forall i:int :: 0 <= i && i < left_count ==> result [i] == left [i]);
    invariant (forall i:int :: left_count <= i && i < tmp ==> result [i] == middle [i-left_count]);
    invariant tmp <= left_count+middle_count;
  {
    result [tmp] := middle [tmp-left_count];
  }

  while (tmp < left_count + middle_count + right_count)
    invariant small_elements (result, tmp);
    invariant is_sorted (result, tmp);
    invariant (forall i:int :: 0 <= i && i < left_count ==> result [i] == left [i]);
    invariant (forall i:int :: left_count <= i && i < left_count + middle_count ==> result [i] == middle [i-left_count]);
    invariant (forall i:int :: left_count + middle_count <= i && i < tmp ==> result [i] == middle [i-left_count-middle_count]);
    invariant tmp <= left_count+middle_count;
  {
    result [tmp] := middle [tmp-left_count];
  }
}

procedure MagicSort (input: Array, count: int, lower_bound, upper_bound: int) returns (output: Array);
  requires (forall i:int :: 0 <= i && i < count ==> lower_bound <= input [i] && input [i] <= upper_bound);
  ensures is_sorted (output, count);
  ensures (forall i:int :: 0 <= i && i < count ==> lower_bound <= output [i] && output [i] <= upper_bound);

