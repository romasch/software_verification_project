// Define array type.
type Array = [int] int;

const N: int;
axiom N > 0;

function small_elements (a: Array, count: int) returns (bool)
{
  (forall i: int :: 0 <= i && i <= count ==> -3*N <= a [i] && a [i] <= 3*N)
}

function is_permutation (perm: Array, count: int) returns (bool)
{
  (forall i: int :: 0 <= i && i < count ==> 0 <= perm [i] && perm [i] < count)
  && (forall i,j:int :: 0 <= i && i < j && j < count ==> perm[i] != perm[j])
}

function is_sorted (a: Array, count: int) returns (bool)
{
  (forall i,j: int :: 0 <= i && i < j && j <= count ==> a[i] <= a[j])
}

procedure BucketSort (input: Array, count: int) returns (result, permutation: Array)
  // Small elements.
  requires small_elements (input, count); 
  
  ensures small_elements (result, count);
  ensures is_sorted (result, count);
  
  // Result is a permutation.
  ensures is_permutation (permutation, count);
  ensures (forall i:int :: 0 <= i && i < count ==> result [i] == input [permutation[i]]);
{
  var tmp, value: int;
  var left, middle, right: Array;
  var left_count, middle_count, right_count: int;
  
  tmp := 0;
  left_count := 0;
  middle_count := 0;
  right_count := 0;
  
  
  while (tmp <= count)
    invariant (forall i:int :: 0 <= i && i < tmp ==> permutation [i] == i && input [i] == result [i]);
    invariant (forall i: int :: 0 <= i && i < left_count ==> -3*N <= left [i] && left [i] < -N);
    invariant (forall i: int :: 0 <= i && i < middle_count ==> -N <= middle [i] && middle [i] <= N);
    invariant (forall i: int :: 0 <= i && i < right_count ==> N < right [i] && right [i] <= 3*N);
  {
    value := input [tmp];
    if (value < -N) {
      left [left_count] := value;
      left_count := left_count + 1;
    } else {
      if (value <= N) {
        middle [middle_count] := value;
        middle_count := middle_count + 1;
      } else {
        right [right_count] := value;
        right_count := right_count + 1;
      }
    }
    
    permutation [tmp] := tmp;
    result [tmp] := input [tmp];
    tmp := tmp + 1;
  }
  
  
  
}
