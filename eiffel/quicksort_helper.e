class
    QUICKSORT_HELPER

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

    concatenate_arrays_with_bounds (a: SIMPLE_ARRAY [INTEGER] b: SIMPLE_ARRAY [INTEGER]; lower_bound, upper_bound: INTEGER; check_lower_bound, check_upper_bound: BOOLEAN): SIMPLE_ARRAY [INTEGER]
            -- return the array comprising the elements of `a' followed by those of `b'
        note
            status: impure
            explicit: contracts
        require
            wrapped: a.is_wrapped and b.is_wrapped
            -- Boundary checks:
            lower_bound: check_lower_bound implies across a.sequence.domain as idx all a.sequence [idx.item] > lower_bound end
            lower_bound: check_lower_bound implies across b.sequence.domain as idx all b.sequence [idx.item] > lower_bound end
            upper_bound: check_upper_bound implies across a.sequence.domain as idx all a.sequence [idx.item] <= upper_bound end
            upper_bound: check_upper_bound implies across b.sequence.domain as idx all b.sequence [idx.item] <= upper_bound end
        local
            i: INTEGER
        do
            from
                create Result.make_from_array (a)
                i := 1
            invariant
                wrapped: Result.is_wrapped
                partial_result: Result.sequence = a.sequence + b.sequence.front (i-1)
                lower_bound: check_lower_bound implies across Result.sequence.domain as idx all Result.sequence [idx.item] > lower_bound end
                upper_bound: check_upper_bound implies across Result.sequence.domain as idx all Result.sequence [idx.item] <= upper_bound end
            until
                i > b.count
            loop
                Result.force (b[i], Result.count + 1)
                i := i + 1
            variant
                b.count + 1 - i
            end
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            same_elements: Result.sequence = a.sequence + b.sequence
            -- Boundary checks:
            lower_bound: check_lower_bound implies across Result.sequence.domain as idx all Result [idx.item] > lower_bound end
            upper_bound: check_upper_bound implies across Result.sequence.domain as idx all Result [idx.item] <= upper_bound end
        end

    quick_sort_impl (a: SIMPLE_ARRAY [INTEGER]; lower, upper: INTEGER; check_lower_bound, check_upper_bound: BOOLEAN): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using Quicksort
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            decreases(a.sequence)
            modify([])

            upper_bound: check_upper_bound implies across a.sequence.domain as idx all a[idx.item] <= upper end
            lower_bound: check_lower_bound implies across a.sequence.domain as idx all a[idx.item] > lower end
        local
            left, right: SIMPLE_ARRAY [INTEGER]
            pivot_arr, control: SIMPLE_ARRAY [INTEGER]
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
                    create pivot_arr.make (1)
                    create control.make_from_array (pivot_arr) -- works for permutation proof.
                    -- create control.make (1) -- doesn't work for permutation proof.

                    pivot := a [1]
                    pivot_arr [1] := pivot
                    control [1] := pivot
                    i := 2

                    check permutation: is_permutation (pivot_arr.sequence, control.sequence) end
                invariant

                    -- Note: in loop invariants, you should write X.wrapped for each array X that the loop modifies
                    a.is_wrapped and left.is_wrapped and right.is_wrapped and pivot_arr.is_wrapped and control.is_wrapped

                    -- General loop invariants.
                    in_bounds: 2 <= i and i <= a.count + 1
                    correct_control: i = control.count + 1
                    no_additional_elements: i = left.count + right.count + 2
                    pivot_unchanged: pivot = a[1] and pivot = pivot_arr [1] and pivot_arr.count = 1

                    -- Invariants related to proving is_sorted.
                    correct_split_left: across left.sequence.domain as z all left [z.item] <= pivot end
                    -- check_upper_bound: check_upper_bound implies pivot <= upper -- can be inferred.
                    correct_split_right: across right.sequence.domain as y all right [y.item] > pivot end
                    -- check_lower_bound: check_lower_bound implies pivot > lower -- can be inferred.
                    check_lower_bound: check_lower_bound implies across left.sequence.domain as idx all left[idx.item] > lower end
                    check_upper_bound: check_upper_bound implies across right.sequence.domain as idx all right[idx.item] <= upper end

                    -- Invariants related to proving is_permutation.
                    permutation: is_permutation (control.sequence, pivot_arr.sequence + left.sequence + right.sequence)
                    same_array_2: control.sequence ~ a.sequence.front (i-1)
                    same_array: across control.sequence.domain as across_idx all control [across_idx.item] =  a [across_idx.item] end
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

                -- Interestingly, this check only works with the control sequence, but not with a.
                check permutation: is_permutation (control.sequence, pivot_arr.sequence + left.sequence + right.sequence) end

                left := quick_sort_impl (left, lower, pivot, check_lower_bound, True)

                right := quick_sort_impl (right, pivot, upper, True, check_upper_bound)

                -- Check that it's sorted. Due to the postcondition that verifies now this is no longer necessary.
--                check is_in_fact_sorted:
--                    is_sorted (left)
--                    and across left.sequence.domain as idx all left [idx.item] <= pivot_arr [1] end
--                    and is_sorted (right)
--                    and across right.sequence.domain as idx all right [idx.item] > pivot_arr [1] end
--                end

                -- Check that the left+pivot+right is a correct permutation.
                -- Note: At this point, AutoProof can proof that `control' is a permutation to (left+pivot+right).
                -- It can also proof that `control' is equal to `a'.
                -- However, it fails to infer that therefore `a' is a permutation of the combined array.
                check is_in_fact_permutation:
                    is_permutation (control.sequence, left.sequence + pivot_arr.sequence + right.sequence)
                    and a.count = control.count
                    and across control.sequence.domain as across_idx all control [across_idx.item] =  a [across_idx.item] end
                end

                -- Check needed for permutation proof.
                check same_array: control.sequence ~ a.sequence end

                intermediate := concatenate_arrays_with_bounds (left, pivot_arr, lower, upper, check_lower_bound, check_upper_bound )
                Result := concatenate_arrays_with_bounds (intermediate, right, lower, upper, check_lower_bound, check_upper_bound )

                -- Cheating here because is_permutation just behaves too randomly to really work with it.
                --check assume: is_permutation (a.sequence, Result.sequence) end
            end

        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh

            -- The elements are the same.
            same_elementes: is_permutation (Result.sequence, a.sequence)
            same_count: Result.count = a.count
            -- The result is sorted.
            sorted: is_sorted (Result)

            -- Helper contracts to proof the actual sort routine.
            upper_bound: check_upper_bound implies across Result.sequence.domain as idx all Result[idx.item] <= upper end
            lower_bound: check_lower_bound implies across Result.sequence.domain as idx all Result[idx.item] > lower end
        end
end