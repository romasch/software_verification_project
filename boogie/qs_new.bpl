/**
* Boogie solution for Software Verification project.
* Roman Schmocker
*/


// Define array type.
type Array = [int] int;

// Define maximum array.
const N:int;
axiom N > 0;

// Define the global instance of the array to be sorted.
var elems: Array;

// The original array.
var original: Array;

// Keeps track of the permutation to elems.
var permutation: Array;

function is_permutation (perm: Array) returns (bool)
{
  (forall i: int :: 0 <= i && i < N ==> 0 <= perm [i] && perm [i] < N)
  &&
  (forall i,j:int :: 0 <= i && i < j && j < N ==> perm[i] != perm[j])
}

function is_smaller (from, to: int, arr: Array, bound: int) returns (bool)
{
  (forall i:int :: from <= i && i <= to ==> arr [i] < bound)
}

function is_greater_equal (from, to: int, arr: Array, bound: int) returns (bool)
{
  (forall i:int :: from <= i && i <= to ==> bound <= arr [i])
}

procedure Swap (i:int, k:int)
    modifies elems, permutation;
    requires 0 <= i && i < N;
    requires 0 <= k && k < N;

    // Permutation exists.
    requires is_permutation(permutation);
    // Permutation maps to original values.
    requires (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);

    // Elements swapped.
    ensures (elems [i] == old (elems [k]));
    ensures (elems [k] == old (elems [i]));
    ensures (permutation [i] == old (permutation [k]));
    ensures (permutation [k] == old (permutation [i]));

    // Permutation still valid.
    ensures is_permutation (permutation);

    // No excessive modification
    ensures (forall n:int :: n != i && n != k ==> elems [n] == old (elems [n]));
    ensures (forall n:int :: n != i && n != k ==> permutation [n] == old (permutation [n]));

    // Permutation updated.
    ensures (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);
{
  var elem, perm: int;

  if (i != k) {

    perm := permutation [i];
    permutation [i] := permutation [k];
    permutation [k] := perm;

    assert (elems [k] == original [permutation [i]]);
    assert (elems [i] == original [permutation [k]]);

    elem := elems [i];
    elems [i] := elems [k];
    elems [k] := elem;

    assert (elems [i] == original [permutation [i]]);
    assert (elems [k] == original [permutation [k]]);
  }
}

// Sorts elements in elems in range [from, to] using Quicksort.
// Note: Array is zero-indexed, and 'to' has to be a valid index.
procedure QuickSort (from: int, to:int, check_smaller: bool, upper: int, check_greater: bool, lower: int)
    modifies elems, permutation;
    requires 0 <= from;
    requires to < N;
    // Permutation exists.
    requires is_permutation(permutation);

    // Upper and lower bounds
    requires check_smaller ==> is_smaller (from, to, elems, upper);
    requires check_greater ==> is_greater_equal (from, to, elems, lower);

    // Permutation maps to original values.
    requires (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);

    // No additional changes
    ensures (forall n: int :: n < from ==> elems [n] == old (elems [n]) && permutation [n] == old (permutation[n]));
    ensures (forall n: int :: n > to ==> elems [n] == old (elems [n])&& permutation [n] == old (permutation[n]));


    ensures (forall n: int :: from <= n && n <= to ==> elems [n] == original [permutation [n]]);

    // Permutation exists.
    ensures is_permutation(permutation);
    // Permutation maps to original values.
    ensures (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);

    // Upper and lower bounds
    ensures check_smaller ==> is_smaller (from, to, elems, upper);
    ensures check_greater ==> is_greater_equal (from, to, elems, lower);

    // Need to specify at least that the range of input values stays the same...
    ensures (forall i,j: int :: from <= i && i < j && j <= to ==> elems [i] <= elems [j]);
{
    var split_index: int;
    var pivot: int;

    if (from < to)
    {
        call split_index := Split (from, to, check_smaller, upper, check_greater, lower);

        assert (forall i:int :: from < i && i < split_index ==> elems [i] < elems [split_index]);
        assert (forall i:int :: split_index < i && i <= to ==> elems [split_index] <= elems [i]);

        assert (split_index != to ==> elems [split_index] <= elems [split_index + 1]);
        assert (split_index != from ==> elems [split_index-1] <= elems [split_index]);

        assert is_smaller (from, split_index-1, elems, elems [split_index]);
        assert is_greater_equal (split_index+1, to, elems, elems [split_index]);

        pivot := elems [split_index];

        call QuickSort (from, split_index-1, true, pivot, check_greater, lower);

        assert (elems [split_index] == pivot);

        assert (forall i,j: int :: from <= i && i < j && j < split_index ==> elems [i] <= elems [j]);

        assert (forall i: int :: from <= i && i <= split_index-1 ==> elems [i] < pivot);
        assert (split_index != from ==> elems [split_index-1] < elems [split_index]);

        call QuickSort (split_index+1, to, check_smaller, upper, true, elems [split_index]);

        assert (forall i,j: int :: split_index < i && i < j && j <= to  ==> elems [i] <= elems [j]);

        assert (split_index != to ==> elems [split_index] <= elems [split_index + 1]);


        //assert (split_index != to ==> elems [split_index] <= elems [split_index + 1]);
    }
}

/**
 * Split the global array in the range [from, to].
 */
procedure Split (from: int, to:int, check_smaller: bool, upper: int, check_greater: bool, lower:int) returns (position: int)
    modifies elems, permutation;
    requires 0 <= from && from < to && to < N;

    // Permutation exists.
    requires is_permutation(permutation);
    // Permutation maps to original values.
    requires (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);

    // Upper and lower bounds
    requires check_smaller ==> is_smaller (from, to, elems, upper);
    requires check_greater ==> is_greater_equal (from, to, elems, lower);

    // Upper and lower bounds
    ensures check_smaller ==> is_smaller (from, to, elems, upper);
    ensures check_greater ==> is_greater_equal (from, to, elems, lower);


    ensures from <= position && position <= to;
    ensures (forall i: int :: from <= i && i < position ==> elems [i] < elems [position]);
    ensures (forall i: int :: position <= i && i <= to ==> elems [position] <= elems [i]);

    // No additional changes
    ensures (forall n: int :: n < from ==> elems [n] == old (elems [n]));
    ensures (forall n: int :: n > to ==> elems [n] == old (elems [n]));

    ensures (forall n: int :: n < from ==> elems [n] == old (elems [n]) && permutation [n] == old (permutation[n]));
    ensures (forall n: int :: n > to ==> elems [n] == old (elems [n])&& permutation [n] == old (permutation[n]));

    // Permutation exists.
    ensures is_permutation(permutation);
    // Permutation maps to original values.
    ensures (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);

{
    var search_left: int;
    var search_right: int;
    var pivot: int;
    var tmp: int;

    search_left := from;
    search_right := to-1;
    // Use the right-most element as pivot.
    pivot := elems [to];

    // Search from both sides for elements to swap.
    while (search_left < search_right)
        invariant pivot == elems [to];
        invariant (forall i: int :: from <= i && i < search_left ==> elems [i] < pivot);
        invariant (forall i: int :: to > i && i > search_right ==> elems [i] >= pivot);

        invariant (search_left > search_right && search_left < to ==> elems [search_left] >= pivot);

        invariant (from <= search_left && search_left <= to);
        invariant (from-1 <= search_right && search_right < to);

        invariant (forall n: int :: n < from ==> elems [n] == old (elems [n]));
        invariant (forall n: int :: n > to ==> elems [n] == old (elems [n]));

        invariant (forall n: int :: n < from ==> elems [n] == old (elems [n]) && permutation [n] == old (permutation[n]));
        invariant (forall n: int :: n > to ==> elems [n] == old (elems [n]) && permutation [n] == old (permutation[n]));

        invariant check_smaller ==> is_smaller (from, to, elems, upper);
        invariant check_greater ==> is_greater_equal (from, to, elems, lower);


        // Permutation exists.
        invariant is_permutation(permutation);
        // Permutation maps to original values.
        invariant (forall n: int :: 0 <= n && n < N ==> elems [n] == original [permutation [n]]);

    {
        // Find a big element on the left side.
        while (elems [search_left] < pivot && search_left < to)
            invariant (forall i: int :: from <= i && i < search_left  ==> elems [i] < pivot);
            invariant (from <= search_left);
            invariant (search_left <= to);
        {
            search_left := search_left + 1;
        }

        assert (elems [search_left] >= pivot);

        // Find a small element on the right side.
        while (elems [search_right] >= pivot && from <= search_right)
            invariant (forall i: int :: to > i && i > search_right ==> elems [i] >= pivot);
            invariant (search_right < to);
            invariant (from-1 <= search_right);
        {
            search_right := search_right - 1;
        }



        // If indices are still correct, swap them.
        if (search_left < search_right)
        {
            call Swap (search_left, search_right);
//            tmp := elems [search_left];
//            elems [search_left] := elems [search_right];
//            elems [search_right] := tmp;
        }

        assert (search_left >= search_right ==> elems [search_left] >= pivot);
    }

    // Now we have partitioned our array into 4 parts:
    // The first part [from, search_left) contains all elements smaller than pivot.
    assert (forall i: int :: from <= i && i < search_left ==> elems [i] < pivot);

    // The second part is just the element elems[search_left].
    // Unfortunately we can't say anything about it as the loop may never have been executed.

    // The third part is (search_left, to). It contains all elements greater or equal the pivot.
    assert (forall i: int :: search_left < i && i < to ==> pivot <= elems [i]);

    // The fourth part is the pivot itself at the end of the array.
    assert (elems [to] == pivot);


    // Check where to insert the pivot.
    if (elems [search_left] < pivot) {
      position := search_left + 1;
    } else {
      position := search_left;
    }

    // Finally, swap the pivot.
    call Swap (position, to);
}
