class
    BUCKETSORT_HELPER

feature -- Constant parameters

    max_count: INTEGER = 20
            -- Maximum number of elements in the list.

    N: INTEGER = 5
            -- Boundary value for algorithm selection.

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

    bucket_sort (input: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- Sort `input' using Bucket Sort
        note
            status: impure
            explicit: contracts
        require
            input.is_wrapped
            small_elems: has_small_elements (input)
        local
            left, middle, right: SIMPLE_ARRAY [INTEGER]
            control: SIMPLE_ARRAY [INTEGER]

            index: INTEGER
            current_value: INTEGER
            boundary: INTEGER
        do
            boundary := N
            check positive: boundary > 0 end
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
                correct_split_left: across left.sequence.domain as i all -3*boundary <= left.sequence.item (i.item) and left.sequence.item (i.item) < -boundary end
                correct_split_middle: across middle.sequence.domain as i all -boundary <= middle.sequence.item (i.item)  and middle.sequence.item (i.item)  <= boundary end
                correct_split_right: across right.sequence.domain as i all boundary < right.sequence.item (i.item)  and right.sequence.item (i.item)  <= 3*boundary  end

                -- Permutation-related invariants
                permutation: is_permutation (left.sequence + middle.sequence + right.sequence, control.sequence)
                same_array: across control.sequence.domain as i all control.sequence.item(i.item) =  input.sequence.item(i.item) end
            until
                index > input.count
            loop
                current_value := input [index]
                control.force (current_value, control.count+1)

                if current_value < -boundary then
                    left.force (current_value, left.count+1)
                elseif current_value <= boundary then
                    middle.force (current_value, middle.count+1)
                else
                    right.force (current_value, right.count+1)
                end
                index := index + 1
            variant
                input.count + 1 - index
            end

            -- Call quicksort to sort the individual buckets.
            left := quick_sort_impl (left, -3*boundary-1, -boundary-1, True, True)
            middle := quick_sort_impl (middle, -boundary-1, boundary, True, True)
            right := quick_sort_impl (right, boundary, 3* boundary, True, True)

            -- Check that the ranges are still the same.
            -- This is apparently necessary to trigger an axiom.
            check correct_split_left: across left.sequence.domain as i all -3*boundary <= left.sequence.item (i.item) and left.sequence.item (i.item) < -boundary end end
            check correct_split_middle: across middle.sequence.domain as i all -boundary <= middle.sequence.item (i.item)  and middle.sequence.item (i.item)  <= boundary end end
            check correct_split_right: across right.sequence.domain as i all boundary < right.sequence.item (i.item)  and right.sequence.item (i.item)  <= 3*boundary  end end

            -- Check needed for permutation proof.
            check control.sequence ~ input.sequence end

            Result := concatenate_arrays (concatenate_arrays (left, middle), right)
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            sorted: is_sorted (Result)
            permutation: is_permutation (Result.sequence, input.sequence)
            same_count: Result.count = input.count
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
            upper_bound: check_upper_bound implies across Result.sequence.domain as idx all Result[idx.item] <= upper end
            lower_bound: check_lower_bound implies across Result.sequence.domain as idx all Result[idx.item] > lower end
        end

invariant
    positive_N: N>0
end
