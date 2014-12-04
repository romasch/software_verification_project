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
  var tmp: int;
  tmp := 0;
  while (tmp <= count)
    invariant (forall i:int :: 0 <= i && i < tmp ==> permutation [i] == i && input [i] == result [i]);
  {
    permutation [tmp] := tmp;
    result [tmp] := input [tmp];
    tmp := tmp + 1;
  }
}
