class
    QUICKSORT

feature -- API

    quick_sort (a: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using quicksort.
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
        do
            Result := quick_sort_impl (a, 0, 0, false, false)
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            sorted: is_sorted (Result)
            permutation: is_permutation (Result.sequence, a.sequence)
            same_count: Result.count = a.count
        end

feature -- For use in specifications

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

feature {NONE} -- Sort implementation

    quick_sort_impl (a: SIMPLE_ARRAY [INTEGER]; lower, upper: INTEGER; check_lower_bound, check_upper_bound: BOOLEAN): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using Quicksort
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            decreases(a.sequence)
            modify([])

            upper_bound: check_upper_bound implies across a.sequence.domain as idx all a.sequence [idx.item] <= upper end
            lower_bound: check_lower_bound implies across a.sequence.domain as idx all a.sequence [idx.item] > lower end
        local
            left, right: SIMPLE_ARRAY [INTEGER]
            pivot_array, control: SIMPLE_ARRAY [INTEGER]
            intermediate: SIMPLE_ARRAY [INTEGER]
            pivot: INTEGER
            i: INTEGER
            value: INTEGER
        do
            if a.count = 0 then
                create Result.make_from_array (a)
            else
                from
                    create left.make_empty
                    create right.make_empty
                    create pivot_array.make (1)
                    create control.make_from_array (pivot_array) -- works for permutation proof.
                    -- create control.make (1) -- doesn't work for permutation proof.

                    pivot := a [1]
                    pivot_array [1] := pivot
                    control [1] := pivot
                    i := 2
                invariant

                    -- Note: in loop invariants, you should write X.wrapped for each array X that the loop modifies
                    wrapped: a.is_wrapped and left.is_wrapped and right.is_wrapped and pivot_array.is_wrapped and control.is_wrapped

                    -- General loop invariants.
                    in_bounds: 2 <= i and i <= a.count + 1
                    correct_control: i = control.count + 1
                    no_additional_elements: i = left.count + right.count + 2
                    pivot_unchanged: pivot = a[1] and pivot = pivot_array [1] and pivot_array.count = 1

                    -- Invariants related to proving is_sorted.
                    correct_split_left: across left.sequence.domain as z all left [z.item] <= pivot end -- Note also that pivot <= upper.
                    correct_split_right: across right.sequence.domain as y all right [y.item] > pivot end -- Note also that pivot > lower.
                    check_lower_bound: check_lower_bound implies across left.sequence.domain as idx all left.sequence [idx.item] > lower end
                    check_upper_bound: check_upper_bound implies across right.sequence.domain as idx all right.sequence [idx.item] <= upper end

                    -- Invariants related to proving is_permutation.
                    permutation: is_permutation (control.sequence, pivot_array.sequence + left.sequence + right.sequence)
                    same_array: control.sequence ~ a.sequence.front (i-1)

                    -- Note: Due to some weirdness in AutoProof I need to build a `control' array, which
                    -- is always a permutation of the three individual arrays and a subarray of the input.
                    -- I.e. the following check doesn't work:
                    -- check is_permutation (a.sequence.front (i-1), left.sequence + pivot_array.sequence + right.sequence) end
                until
                    i > a.count
                loop
                    value := a [i]
                    if value <= pivot then
                        left.force (value, left.count+1)
                    else
                        right.force (value, right.count+1)
                    end
                    control.force (value, i)
                    i := i + 1
                variant
                    a.count - i
                end

                -- Call quicksort recursively.
                left := quick_sort_impl (left, lower, pivot, check_lower_bound, True)
                right := quick_sort_impl (right, pivot, upper, True, check_upper_bound)

                -- Concatenate the arrays.
                intermediate := concatenate_arrays (left, pivot_array)
                Result := concatenate_arrays (intermediate, right)
            end
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            -- The elements are the same.
            same_elementes: is_permutation (Result.sequence, a.sequence)
            same_count: Result.count = a.count
            -- The result is sorted.
            sorted: is_sorted (Result)
            -- Helper contracts to proof the actual sort routine.
            upper_bound: check_upper_bound implies across Result.sequence.domain as idx all Result.sequence [idx.item] <= upper end
            lower_bound: check_lower_bound implies across Result.sequence.domain as idx all Result.sequence [idx.item] > lower end
        end

feature {NONE} -- Stubs

    concatenate_arrays (a: SIMPLE_ARRAY [INTEGER] b: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- return the array comprising the elements of `a' followed by those of `b'
        note
            status: impure
            explicit: contracts
        require
            wrapped: a.is_wrapped and b.is_wrapped
        do
            create Result.make_empty
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            same_sequence: Result.sequence = a.sequence + b.sequence
        end

end