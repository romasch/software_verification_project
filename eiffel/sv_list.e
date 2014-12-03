class
    SV_LIST

create
    make, make_from_array

feature {NONE} -- Initialization

    make
            -- Initialize `sequence' to an empty list
        note
            status: creator
        do
            create array.make (0)
        ensure
            array.sequence.is_constant (0)
            count = 0
        end

    make_from_array (a: SIMPLE_ARRAY [INTEGER])
            -- Initialize `sequence' to the content of `a'
        note
            status: creator
        require
            attached a
            a.count <= Max_count
        do
            create array.make_from_array (a)
        ensure
            count = a.count
            array.sequence = a.sequence
        end

feature -- Constant parameters

    max_count: INTEGER = 20
            -- Maximum number of elements in the list.

    N: INTEGER = 5
            -- Boundary value for algorithm selection.

feature -- Basic API

    array: SIMPLE_ARRAY [INTEGER]
            -- Sequence of integers represented as an array

    empty: BOOLEAN
            -- Is `array' empty?
        note
            status: functional
        require
            inv
        do
            Result := (count = 0)
        ensure
            Result = (count = 0)
        end

    in_bound (k: INTEGER): BOOLEAN
            -- Is `k' a position within the bounds of `array'?
        note
            status: functional
        require
            inv_ok: inv
        do
            -- implementation
            Result := 1 <= k and k <= count
        ensure
            -- postconditions
            correct: Result = (1 <= k and k <= count)
        end

    at (k: INTEGER): INTEGER
            -- Element at position `k' in `array'
        require
            -- preconditions
            bounded: in_bound (k)
            inv_ok: inv --??
        do
            -- implementation
            Result := array [k]
        ensure
            -- postconditions
            Result = array [k]
        end

    put (k: INTEGER; val: INTEGER)
            -- Write `val' at position `k' in `array'
        require
            in_bound (k)
        do
            -- implementation
            array [k] := val
        ensure
            array [k] = val
        end

    extend (val: INTEGER)
            -- Extend `array' with an element `val'
        require
            -- preconditions
            enough_space: count < max_count
        do
            array.force (val, count+1)
        ensure
            -- postconditions
            more_elements: count = old count + 1
            in_array: array [count] = val
            inserted: at (count) = val
        end

    remove
            -- Remove the last element of `array'
        require
            -- preconditions
            not_empty: count > 0
        do
            array.remove_at (count)
        ensure
            -- postconditions
            less_elements: count = old count - 1
        end

    count: INTEGER
            -- Number of elements stored in `array'
        note
            status: functional
        require
            inv
        do
            -- implementation
            Result := array.count
        ensure
            -- postconditions
            Result = array.count
        end

feature -- Sorting

    sort
            -- Sort `array'
        do
            if count >= Max_count // 2 and has_small_elements (array) then
                array := bucket_sort (array)
            else
                array := quick_sort (array)
            end
        ensure
            sorted: is_sorted (array)
            permutation: is_permutation (array.sequence, old array.sequence)
        end

feature -- For use in specifications

    has_small_elements (a: SIMPLE_ARRAY [INTEGER]): BOOLEAN
            -- Are all elements of `a' small (i.e., in the range [-3N..3N])?
        note
            status: functional
        require
            a /= Void
        do
            Result := across a.sequence.domain as i all -3*N <= a.sequence[i.item] and a.sequence[i.item] <= 3*N end
        end

    is_sorted (a: SIMPLE_ARRAY [INTEGER]): BOOLEAN
            -- Is `a' sorted?
        note
            status: functional, ghost
        require
            a /= Void
        do
            Result := across a.sequence.domain as i all (i.item < a.count) implies a.sequence [i.item] <= a.sequence [i.item + 1] end
        end

    is_permutation (a, b: MML_SEQUENCE [INTEGER]): BOOLEAN
            -- Is `a' a permuation of `b'?
        note
            status: functional, ghost
        do
            Result := a.to_bag ~ b.to_bag
        end

feature -- Sort implementations

    concatenate_arrays (a: SIMPLE_ARRAY [INTEGER] b: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- return the array comprising the elements of `a' followed by those of `b'
        note
            status: impure
            explicit: contracts
        require
            wrapped: a.is_wrapped and b.is_wrapped
        local
            i: INTEGER
        do
            from
                create Result.make_from_array (a)
                i := 1
            invariant
                Result.is_wrapped
                partial_result: Result.sequence = a.sequence + b.sequence.front (i-1)
            until
                i > b.count
            loop
                Result.force (b[i], Result.count+1)
                i := i + 1
            variant
                b.count + 1 - i
            end
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            same_sequence: Result.sequence = a.sequence + b.sequence
        end

     quick_sort (a: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using quicksort.
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
        do
            -- see quicksort_helper.e.
            create Result.make_empty
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            sorted: is_sorted (Result)
            permutation: is_permutation (Result.sequence, a.sequence)
            same_count: Result.count = a.count
        end

    bucket_sort (input: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- Sort `input' using Bucket Sort
        note
            status: impure
            explicit: contracts
        require
            input.is_wrapped
            small_elems: has_small_elements (input)
        do
            -- see bucketsort_helper.e
            create Result.make_empty
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            sorted: is_sorted (Result)
            permutation: is_permutation (Result.sequence, input.sequence)
            same_count: Result.count = input.count
        end

invariant
    array_not_void: attached array
    owns_array: owns = [array]
    array_size_restriction: 0 <= array.sequence.count and array.sequence.count <= Max_count
    positive_N: N>0
end