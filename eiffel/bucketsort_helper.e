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

    concatenate_arrays_old (a: SIMPLE_ARRAY [INTEGER] b: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- return the array comprising the elements of `a' followed by those of `b'
        note
            status: skip
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

            sorted: is_sorted (a) and is_sorted (b) and b.count > 0 and then (across a as idx all a[idx.item] <= b[1] end) implies is_sorted (Result)
            same_elems: across a.sequence.domain as idx all Result [idx.item] = a[idx.item] end
            same_elems_2: across b.sequence.domain as idx all Result [idx.item + a.count] = b[idx.item] end
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
            control, left_middle: SIMPLE_ARRAY [INTEGER]

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
                correct_split_left: across left.sequence.domain as i all -3*boundary <= left [i.item] and left [i.item] < -boundary end
                correct_split_middle: across middle.sequence.domain as i all -boundary <= middle [i.item] and middle [i.item] <= boundary end
                correct_split_right: across right.sequence.domain as i all boundary < right [i.item] and right [i.item] <= 3*boundary  end

                -- Permutation-related invariants
                permutation: is_permutation (left.sequence + middle.sequence + right.sequence, control.sequence)
                same_array: across control.sequence.domain as i all control [i.item] =  input [i.item] end


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

            left := quick_sort_impl (left, True, True, -boundary-1, -3*boundary-1)
            middle := quick_sort_impl (middle, True, True, boundary, -boundary-1)
            right := quick_sort_impl (right, True, True, 3*boundary, boundary)

            check correct_split_left: across left.sequence.domain as i all -3*boundary <= left [i.item] and left [i.item] < -boundary end end
            check correct_split_middle: across middle.sequence.domain as i all -boundary <= middle [i.item] and middle [i.item] <= boundary end end
            check correct_split_right: across right.sequence.domain as i all boundary < right [i.item] and right [i.item] <= 3*boundary  end end

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

            --check why_not: is_permutation (control.sequence, input.sequence) end
            check is_in_fact_sorted:
                is_sorted (left)
                and across left.sequence.domain as i all left [i.item] < -boundary end
                and is_sorted (middle)
                and across middle.sequence.domain as i all middle [i.item] >= -boundary end
            end
            

            --left_middle := concatenate_arrays_old (left, middle)
            left_middle := concatenate_arrays (left, middle, True, True, boundary, -3*boundary-1)
            check sorted: is_sorted (left_middle) end
            
            check correct_split_right: across right.sequence.domain as i all boundary < right [i.item] end end
            check splitted: across left_middle.sequence.domain as i all left_middle [i.item] <= boundary end end
            
            check all_bigger: right.count > 0 implies (across left_middle.sequence.domain as i all left_middle[i.item] < right[1] end) end
            
--            check splitted_2: across right.sequence.domain as i all right [i.item] > boundary end end
--            check sorted_2: is_sorted (right) end
            
            Result := concatenate_arrays (left_middle, right, True, True, 3*boundary, -3*boundary-1)

            --Result := concatenate_arrays_old (concatenate_arrays_old (left, middle), right)

            --Result := three_way_merge (left, middle, right, N)

            check is_in_fact_permutation:
                is_permutation (Result.sequence, control.sequence)
                and across control.sequence.domain as i all control [i.item] =  input [i.item] end
            end

            check assume: is_permutation (Result.sequence, input.sequence) end

            --create Result.init (left.sequence + middle.sequence + right.sequence)
            --Result := three_way_merge (left, middle, right)
            --Result := concatenate_arrays (concatenate_arrays (left, middle, True, True, N, -3*N-1), right, True, True, 3*N, -3*N-1 )
            --create Result.make_empty
            -- note: in loop invariants, you should write X.wrapped for
            -- each array X that the loop modifies
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            sorted: is_sorted (Result)
            permutation: is_permutation (Result.sequence, input.sequence)
            same_count: Result.count = input.count
        end

    three_way_merge (a,b,c: SIMPLE_ARRAY [INTEGER]; boundary: INTEGER): SIMPLE_ARRAY [INTEGER]
        note
            status: skip
            status: impure
            explicit: contracts
        require
            wrapped: a.is_wrapped and b.is_wrapped and c.is_wrapped
            sorted: is_sorted (a) and is_sorted (b) and is_sorted (c)
            positive: boundary > 0

            splitted_left: across a.sequence.domain as i all a[i.item] < -boundary end
            splitted_middle: across b.sequence.domain as i all -boundary <= b[i.item] and b[i.item] <= boundary end
            splitted_right: across c.sequence.domain as i all boundary < c[i.item] end
        local
            result_index: INTEGER
            index: INTEGER
        do
--            check across a as i all across b as k all a[i.item] < b[k.item] end end end
--            check across b as i all across c as k all b[i.item] < c[k.item] end end end

            create Result.init (a.sequence + b.sequence + c.sequence)
            --create Result.make_empty
        ensure
            default_stuff: Result.is_wrapped and Result.is_fresh
            same_elems: Result.sequence = a.sequence + b.sequence + c.sequence
            perm: is_permutation (Result.sequence,  a.sequence + b.sequence + c.sequence)
            sorted: is_sorted (Result)
--            in_bounds: (a.count > 0 implies Result [1] = a [1]) and (a.count = 0 implies Result [1] = b[1])
--            in_bounds_2: (c.count > 0 implies Result [Result.count] = c [c.count]) and (c.count = 0 implies Result [Result.count] = b[b.count])
        end

    concatenate_arrays (a: SIMPLE_ARRAY [INTEGER] b: SIMPLE_ARRAY [INTEGER]; check_smaller, check_greater: BOOLEAN; upper, lower: INTEGER): SIMPLE_ARRAY [INTEGER]
            -- return the array comprising the elements of `a' followed by those of `b'
        note
            status:skip
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            b.is_wrapped
            smaller: check_smaller implies across a.sequence.domain as idx all a[idx.item] <= upper end
            greater: check_greater implies across a.sequence.domain as idx all a[idx.item] > lower end
            smaller: check_smaller implies across b.sequence.domain as idx all b[idx.item] <= upper end
            greater: check_greater implies across b.sequence.domain as idx all b[idx.item] > lower end
        do
            create Result.make_empty
        ensure
            Result.is_wrapped
            Result.is_fresh
            -- more postconditions?
            Result.sequence = a.sequence + b.sequence
            sorted: is_sorted (a) and is_sorted (b) and b.count > 0 and then (across a as i all a[i.item] <= b[1] end) implies is_sorted (Result)
            --perm: is_permutation (Result.sequence, a.sequence + b.sequence)
            same_elems: across a.sequence.domain as idx all Result [idx.item] = a[idx.item] end
            same_elems_2: across b.sequence.domain as idx all Result [idx.item + a.count] = b[idx.item] end

            smaller: check_smaller implies across Result.sequence.domain as idx all Result [idx.item] <= upper end
            greater: check_greater implies across Result.sequence.domain as idx all Result [idx.item] > lower end
        end


    quick_sort_impl (a: SIMPLE_ARRAY [INTEGER]; check_smaller, check_greater: BOOLEAN; upper, lower: INTEGER): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using Quicksort
        note
            status: skip
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
    positive_N: N>0
end 
