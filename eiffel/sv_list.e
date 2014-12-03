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
            a.is_wrapped
            b.is_wrapped
        local
            i, j: INTEGER
        do
            create Result.make_from_array (a)
            from
                i := 1
                j := Result.count + 1
            invariant
                Result.is_wrapped
                -- more loop invariants?
                correct_insert_position: j = Result.count + 1
                partial_result: Result.sequence = a.sequence + b.sequence.front (i-1)
            until
                i > b.count
            loop
                Result.force (b.item (i), j)
                i := i + 1
                j := j + 1
            end
        ensure
            Result.is_wrapped
            Result.is_fresh
            -- more postconditions?
            Result.sequence = a.sequence + b.sequence
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
            -- Sort `a' using Bucket Sort
        note
            status: impure
            explicit: contracts
        require
            input.is_wrapped
            small_elems: has_small_elements (input)
            -- more preconditions?
        local
            left, middle, right: SIMPLE_ARRAY [INTEGER]
            control: SIMPLE_ARRAY [INTEGER]

            index: INTEGER

            current_value: INTEGER

        do
            from
                create left.make_empty
                create middle.make_empty
                create right.make_empty
                create control.make_empty

                index := 1
            invariant
                wrapped: left.is_wrapped and middle.is_wrapped and right.is_wrapped and control.is_wrapped
                count_correct: index = control.count + 1 and index = left.count + middle.count + right.count + 1
                in_bounds: 1 <= index and index <= input.count+1

                -- Sort-related invariants
                correct_split_left: across left.sequence.domain as i all -3*N <= left [i.item] and left [i.item] < -N end
                correct_split_middle: across middle.sequence.domain as i all -N <= middle [i.item] and middle [i.item] <= N end
                correct_split_right: across right.sequence.domain as i all N < right [i.item] and right [i.item] <= 3*N  end

                -- Permutation-related invariants
                permutation: is_permutation (left.sequence + middle.sequence + right.sequence, control.sequence)
                same_array: across control.sequence.domain as i all control [i.item] =  input [i.item] end


            until
                index > input.count
            loop
                current_value := input [index]
                control.force (current_value, control.count+1)

                if current_value < -N then
                    left.force (current_value, left.count+1)
                elseif current_value <= N then
                    middle.force (current_value, middle.count+1)
                else
                    right.force (current_value, right.count+1)
                end
                index := index + 1
            variant
                input.count + 1 - index
            end

            left := quick_sort_impl (left, True, True, -N-1, -3*N-1)
            middle := quick_sort_impl (middle, True, True, N, -N-1)
            right := quick_sort_impl (right, True, True, 3*N, N)

            check correct_split_left: across left.sequence.domain as i all -3*N <= left [i.item] and left [i.item] < -N end end
            check correct_split_middle: across middle.sequence.domain as i all -N <= middle [i.item] and middle [i.item] <= N end end
            check correct_split_right: across right.sequence.domain as i all N < right [i.item] and right [i.item] <= 3*N  end end

            check permutation: is_permutation (left.sequence + middle.sequence + right.sequence, control.sequence) end

                        -- Check that it's sorted. Due to the postcondition that verifies now this is no longer necessary.
            check is_in_fact_sorted:
                is_sorted (left)
                and is_sorted (middle)
                and is_sorted (right)
            end

            -- Check that the left+pivot+right is a correct permutation.
            -- Note: At this point, AutoProof can proof that `control' is a permutation to (left+middle+right).
            -- It can also proof that `control' is equal to `input'.
            -- However, it fails to infer that therefore `input' is a permutation of the combined array.
            check is_in_fact_permutation:
                is_permutation (control.sequence, left.sequence + middle.sequence + right.sequence)
                and input.count = control.count
                and across control.sequence.domain as i all control [i.item] =  input [i.item] end
            end

            check why_not: is_permutation (control.sequence, input.sequence) end

            Result := concatenate_arrays (concatenate_arrays (left, middle), right)
            --create Result.make_empty
            -- note: in loop invariants, you should write X.wrapped for
            -- each array X that the loop modifies
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            sorted: is_sorted (Result)
            permutation: is_permutation (Result.sequence, input.sequence)
            same_count: Result.count = input.count
        end

    quick_sort_impl (a: SIMPLE_ARRAY [INTEGER]; check_smaller, check_greater: BOOLEAN; upper, lower: INTEGER): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using Quicksort
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            decreases(a.sequence)
            modify([])

            smaller: check_smaller implies across a.sequence.domain as idx all a[idx.item] <= upper end
            greater: check_greater implies across a.sequence.domain as idx all a[idx.item] > lower end
        do
            create Result.make_empty
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh

            -- The elements are the same.
            same_elementes: is_permutation (Result.sequence, a.sequence)
            same_count: Result.count = a.count
            -- The result is sorted.
            sorted: is_sorted (Result)

            -- Helper contracts to proof the actual sort routine.
            smaller: check_smaller implies across Result.sequence.domain as idx all Result[idx.item] <= upper end
            greater: check_greater implies across Result.sequence.domain as idx all Result[idx.item] > lower end
        end

invariant
    array_not_void: attached array
    owns_array: owns = [array]
    array_size_restriction: 0 <= array.sequence.count and array.sequence.count <= Max_count
end