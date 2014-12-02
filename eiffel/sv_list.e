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
            is_sorted (array)
            is_permutation (array.sequence, old array.sequence)
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
            -- Result := ??
            Result := across a.sequence.domain as i all (i.item < a.count) implies a.sequence [i.item] <= a.sequence [i.item + 1] end
  --          Result := across 1 |..| (a.count-1) as idx all a [idx.item] <= a [idx.item + 1] end
        end

    is_permutation (a, b: MML_SEQUENCE [INTEGER]): BOOLEAN
            -- Is `a' a permuation of `b'?
        note
            status: functional, ghost
        do
            Result := a.to_bag ~ b.to_bag
        end

feature -- Sort implementations
    test_permutation_1 (s: MML_SEQUENCE [INTEGER]): like s
        require
            not_empty: not s.is_empty
        do
            Result := s.but_last.extended (s.last)
        ensure
            same_sequence: s ~ Result
            permutation: is_permutation (s, Result)
        end

    test_permutation_2 (s: MML_SEQUENCE [INTEGER]): like s
        require
            not_empty: not s.is_empty
        do
            Result := s.but_first.extended (s.first)
        ensure
            exact: Result ~ s.tail (2).extended (s.first)
            permutation: is_permutation (s, Result)
        end

    test_permutation_3 (s: MML_SEQUENCE [INTEGER]; v: INTEGER): like s
        require
            not_empty: not s.is_empty
        do
            Result := s.prepended (v)
        ensure
--            exact: Result ~ s.tail (2).extended (s.first)
            permutation: is_permutation (s.extended (v), Result)
        end

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
            -- Sort `a' using Quicksort
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            decreases(a.sequence)
            modify([])
        local
            left, right: SIMPLE_ARRAY [INTEGER]
            pivot_arr: SIMPLE_ARRAY [INTEGER]
            pivot: INTEGER
            i: INTEGER
            value: INTEGER
        do
            if a.count = 0 or else a [1] = a [a.count] then
                create Result.make_from_array (a)
            else
                from
                    create left.make_empty
                    create right.make_empty
                    create pivot_arr.make (1)
                    pivot := a [1]
                    value := a [1]
                    pivot_arr [1] := pivot
                    i := 2
                invariant
                    a.is_wrapped
                    left.is_wrapped
                    right.is_wrapped
                    correct_pivot: a.sequence.first = pivot

                    a.count > 0
                    in_bounds: 2 <= i and i <= a.count + 1
                    value = a [i-1]
                    pivot = a[1]
                        -- This is important for variant of recursive calls.
                    no_additional_elements: i - 2 = left.count + right.count
                    no_additional_elements_2: a.sequence.interval (2, i-1).count = left.sequence.count + right.sequence.count

                    correct_split: across left.sequence.domain as z all left [z.item] <= pivot end
                    correct_split_2: across right.sequence.domain as y all right [y.item] > pivot end
                    correct_split_3: left.count > 0 and right.count > 0 implies left [left.count] /= right [right.count]

                    split_lemma: left.sequence.range.count > 0 implies left.sequence.range.max <= pivot
                    split_lemma_2: right.sequence.range.count > 0 implies right.sequence.range.min > pivot
                    correct_split_4: left.sequence.range.is_disjoint (right.sequence.range)

                    distributed_2: i > 2 implies left.has (value) xor right.has (value)
                    distributed: a[i-1] = pivot or else (left.count > 0 and then left[left.count] = a[i-1]) or (right.count > 0 and then right [right.count] = a[i-1])
--                    distributed_3: i > 2 implies (left.sequence ~ left.sequence.old_ & value) xor (right.sequence ~ right.sequence.old_ & value)

--                    asdf: across a.sequence.interval (2, i-1).domain as z all a[z.item] <= pivot implies left.has (a[z.item]) end

--                    same_elements_3: a.sequence.interval (2,i-1).to_bag ~ (left.sequence + right.sequence).to_bag

--                    same_elements: is_permutation (a.sequence.tail (2), left.sequence + right.sequence + a.sequence.tail (i))


                 --   distributed: i > 2 implies (left.sequence.last = a[i-1] xor right.sequence.last = a[i-1])
--                    same_elements_2: is_permutation (a.sequence.interval (2,i-1), left.sequence + right.sequence)
--                    same_elements_4: is_permutation (a.sequence.interval (1, i-1), (left.sequence + right.sequence).extended (pivot))
                    static_pivot_arr: pivot_arr [1] = pivot and pivot_arr.count = 1
                    same_elements_5: is_permutation (a.sequence.interval (1, i-1), pivot_arr.sequence + left.sequence + right.sequence)
                    pivot_correct: a.sequence.interval (1,1) = create {MML_SEQUENCE[INTEGER]}.singleton (pivot)

--                    test2: create {MML_SEQUENCE[INTEGER]}.singleton (pivot) + a.sequence.but_first ~ a.sequence
--                    test: is_permutation (create {MML_SEQUENCE[INTEGER]}.singleton (pivot) + a.sequence.but_first, a.sequence)

--                    same_elements: is_permutation (a.sequence, left.sequence + right.sequence + a.sequence.tail (i) + pivot)
                until
                    i > a.count
                loop
                    value := a [i]
                    if value <= pivot then
                        left.force (value, left.count+1)
                    else
                        right.force (value, right.count+1)
                    end
                    i := i + 1
                variant
                    a.count - i
                end

                left := quick_sort (left)
                right := quick_sort (right)

                left.force (pivot, left.count+1)

                Result := concatenate_arrays (left, right)
            end

            -- note: in loop invariants, you should write X.wrapped for
            -- each array X that the loop modifies
        ensure
            Result.is_wrapped
            Result.is_fresh
            same_elementes: is_permutation (Result.sequence, a.sequence)
            -- most postconditions?
        end


    quick_sort_2 (a: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
        note
            status: impure
        require
            wrapped: a.is_wrapped

            decreases([])
        local
            pivot: INTEGER
            split_index: INTEGER

            swap_temp: INTEGER

            left_idx, right_idx: INTEGER

            left_part, pivot_part, right_part: SIMPLE_ARRAY [INTEGER]

        do
            create Result.make_from_array (a)
            check is_permutation (a.sequence, Result.sequence) end

            if a.count > 1 then

            from
                left_idx := 1
                right_idx := Result.count -1
                pivot := Result [Result.count]
            invariant
                permutation: is_permutation (a.sequence, Result.sequence)
                wrapped: Result.is_wrapped and a.is_wrapped
                no_termination_proof: decreases([])
                in_bounds: 0 <= right_idx and right_idx <= Result.count - 1

                pivot = Result [Result.count]
                
                Result.count = a.count

                partial_split_left: across Result.sequence.domain as i all i.item < left_idx implies Result [i.item] < pivot end
                partial_split_rigth: across Result.sequence.domain as i all i.item > right_idx implies Result [i.item] >= pivot end
            until
                left_idx > right_idx
            loop
                from
                invariant
                    in_bounds: 1 <= left_idx and left_idx <= Result.count
                    partial_split_left: across Result.sequence.domain as i all i.item < left_idx implies Result [i.item] < pivot end
                until
                    left_idx >= Result.count or else Result [left_idx] >= pivot
                loop
                    left_idx := left_idx + 1
                variant
                    Result.count - left_idx + 1
                end
                from
                invariant
                    -- Why is this necessary on decrementing loops, but not on incrementing loops?
                    in_bounds: 0 <= right_idx and right_idx <= Result.count - 1
                    partial_split_rigth: across Result.sequence.domain as i all i.item > right_idx implies Result [i.item] >= pivot end
                until
                    right_idx < 1 or else Result [right_idx] < pivot
                loop
                    right_idx := right_idx - 1
                variant
                    right_idx + 1
                end

                if left_idx < right_idx then
                    swap_temp := Result [left_idx]
                    Result [left_idx] := Result[right_idx]
                    Result [right_idx] := swap_temp
                end
            end

            check across Result.sequence.domain as i all i.item < left_idx implies Result [i.item] < pivot end end
            check across Result.sequence.domain as i all i.item > right_idx implies Result [i.item] >= pivot end end


            if Result [left_idx] < pivot then
                split_index := left_idx + 1
            else
                split_index := left_idx
            end
            swap_temp := Result [split_index]
            Result [split_index] := Result[Result.count]
            Result [Result.count] := swap_temp

            check across Result.sequence.domain as i all i.item < split_index implies Result [i.item] < Result [split_index] end end
            check across Result.sequence.domain as i all i.item > split_index implies Result [i.item] >= Result [split_index] end end
            check is_permutation (Result.sequence, a.sequence) end

            left_part := get_subarray (Result, 1, split_index - 1)
            right_part := get_subarray (Result, split_index + 1, Result.count)
            
            check right_part.count + left_part.count + 1 = Result.count end
--            check assume: across right_part.sequence.domain as i all right_part [i.item] >= Result [split_index] end end

            check (left_part.sequence + Result [split_index] + right_part.sequence) ~ Result.sequence end
            check is_permutation (left_part.sequence, Result.sequence.interval (1, split_index-1)) end

            check across left_part.sequence.domain as i all left_part [i.item] < Result [split_index] end end
            left_part := quick_sort_2 (left_part)
            check perm_left: is_permutation (left_part.sequence, Result.sequence.interval (1, split_index-1)) end
            check still_sorted_left: across left_part.sequence.domain as i all left_part [i.item] < Result [split_index] end end

            check across right_part.sequence.domain as i all right_part [i.item] >= Result [split_index] end end
            check is_permutation (right_part.sequence, Result.sequence.interval (split_index + 1, Result.count)) end
            right_part := quick_sort_2 (right_part)
            check perm_right: is_permutation (right_part.sequence, Result.sequence.interval (split_index + 1, Result.count)) end
            check still_sorted_right: across right_part.sequence.domain as i all right_part [i.item] >= Result [split_index] end end

            create Result.init (left_part.sequence.extended (Result[split_index]) + right_part.sequence)


            end -- if a.count > 1
        ensure
            same_count: a.count = Result.count
            permutation: is_permutation (a.sequence, Result.sequence)
            sorted: is_sorted (a)
        end

    get_subarray (a: SIMPLE_ARRAY [INTEGER]; l,u: INTEGER): SIMPLE_ARRAY [INTEGER]
        require
            l_in_bounds: 1 <= l
            u_in_bounds: u <= a.count
        do
            create Result.make_empty
        ensure
            wrapped: Result.is_wrapped
            correct_empty: l > u implies Result.count = 0
            same_elements: l <= u implies a.sequence.interval (l,u) ~ Result.sequence
    		result_count_definition: l <= u implies Result.count = (u - l + 1)
        end

    bucket_sort (a: SIMPLE_ARRAY [INTEGER]): SIMPLE_ARRAY [INTEGER]
            -- Sort `a' using Bucket Sort
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            -- more preconditions?
        local

        do
            -- note: in loop invariants, you should write X.wrapped for
            -- each array X that the loop modifies
        ensure
            Result.is_wrapped
            Result.is_fresh
            -- more postconditions?
        end

invariant
    array_not_void: attached array
    owns_array: owns = [array]
    array_size_restriction: 0 <= array.sequence.count and array.sequence.count <= Max_count
end
