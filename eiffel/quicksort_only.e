class
    SV_LIST
    
create
    make

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
feature -- Constant parameters

    max_count: INTEGER = 20
            -- Maximum number of elements in the list.

    N: INTEGER = 5
            -- Boundary value for algorithm selection.

feature -- Basic API

    array: SIMPLE_ARRAY [INTEGER]
            -- Sequence of integers represented as an array

feature

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
                array := quick_sort (array, false, false, 0, 0)
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
            Result := a.count > 1 implies across a.sequence.domain as i all (i.item < a.count) implies a.sequence [i.item] <= a.sequence [i.item + 1] end
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

    concatenate_arrays (a: SIMPLE_ARRAY [INTEGER] b: SIMPLE_ARRAY [INTEGER]; check_smaller, check_greater: BOOLEAN; upper, lower: INTEGER): SIMPLE_ARRAY [INTEGER]
            -- return the array comprising the elements of `a' followed by those of `b'
        note
            status: impure
            explicit: contracts
        require
            a.is_wrapped
            b.is_wrapped
            smaller: check_smaller implies across a.sequence.domain as idx all a[idx.item] <= upper end
            greater: check_greater implies across a.sequence.domain as idx all a[idx.item] > lower end
            smaller: check_smaller implies across b.sequence.domain as idx all b[idx.item] <= upper end
            greater: check_greater implies across b.sequence.domain as idx all b[idx.item] > lower end
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

                smaller: check_smaller implies across Result.sequence.domain as idx all Result [idx.item] <= upper end
                
                greater: check_greater implies across Result.sequence.domain as idx all Result [idx.item] > lower end
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
            --perm: is_permutation (Result.sequence, a.sequence + b.sequence)
            same_elems: across a.sequence.domain as idx all Result [idx.item] = a[idx.item] end
            same_elems_2: across b.sequence.domain as idx all Result [idx.item + a.count] = b[idx.item] end
            
            smaller: check_smaller implies across Result.sequence.domain as idx all Result [idx.item] <= upper end
            greater: check_greater implies across Result.sequence.domain as idx all Result [idx.item] > lower end
        end

    quick_sort (a: SIMPLE_ARRAY [INTEGER]; check_smaller, check_greater: BOOLEAN; upper, lower: INTEGER): SIMPLE_ARRAY [INTEGER]
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
        local
            left, right: SIMPLE_ARRAY [INTEGER]
            pivot_arr, control: SIMPLE_ARRAY [INTEGER]
            pivot: INTEGER
            i: INTEGER
            value: INTEGER
        do
            if a.count = 0 then --else a [1] = a [a.count] then
                create Result.make_from_array (a)
            else
                from
                    create left.make_empty
                    create right.make_empty
                    create pivot_arr.make (1)
                    create control.make_from_array (pivot_arr) -- works.
                    check is_permutation (pivot_arr.sequence, control.sequence) end
--                    create control.make (1) -- doesn't work.
--                    check is_permutation (pivot_arr.sequence, control.sequence) end
                    
                    pivot := a [1]
                    value := a [1]
                    pivot_arr [1] := pivot
                    control [1] := pivot
                    
                    check perm: is_permutation (pivot_arr.sequence, control.sequence) end
                    check equal: pivot_arr.sequence ~ control.sequence end
                    i := 2
                    
                invariant
                    
            -- note: in loop invariants, you should write X.wrapped for
            -- each array X that the loop modifies
                    a.is_wrapped
                    left.is_wrapped
                    right.is_wrapped
                    pivot_arr.is_wrapped
                    control.is_wrapped
                    correct_pivot: a.sequence.first = pivot

                    stupid_i: i = control.count + 1
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
                    same_elements_6: is_permutation (control.sequence, pivot_arr.sequence + left.sequence + right.sequence)
                    control_equal_a: across control.sequence.domain as across_idx all control [across_idx.item] =  a [across_idx.item] end
                    --same_elements_7: is_permutation (control.sequence, a.sequence.front (i-1))
--                    same_elements_5: is_permutation (a.sequence.interval (1, i-1), pivot_arr.sequence + left.sequence + right.sequence)
                    pivot_correct: a.sequence.interval (1,1) = create {MML_SEQUENCE[INTEGER]}.singleton (pivot)

--                    test2: create {MML_SEQUENCE[INTEGER]}.singleton (pivot) + a.sequence.but_first ~ a.sequence
--                    test: is_permutation (create {MML_SEQUENCE[INTEGER]}.singleton (pivot) + a.sequence.but_first, a.sequence)

--                    same_elements: is_permutation (a.sequence, left.sequence + right.sequence + a.sequence.tail (i) + pivot)

                    smaller: check_smaller implies across left.sequence.domain as idx all left[idx.item] <= upper end
                    smaller: check_smaller implies across right.sequence.domain as idx all right[idx.item] <= upper end
                    smaller: check_smaller implies pivot <= upper
                    greater: check_greater implies across left.sequence.domain as idx all left[idx.item] > lower end
                    greater: check_greater implies across right.sequence.domain as idx all right[idx.item] > lower end
                    greater: check_greater implies pivot > lower


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
                
                check same_count: a.count = control.count end
                check control_equal_a: across control.sequence.domain as across_idx all control [across_idx.item] =  a [across_idx.item] end end
                check permutation: is_permutation (control.sequence, pivot_arr.sequence + left.sequence + right.sequence) end
                
                check smaller: across left.sequence.domain as idx all left [idx.item] <= pivot end end
                check greater_equal: across right.sequence.domain as idx all right [idx.item] > pivot end end

                left := quick_sort (left, True, check_greater, pivot, lower)
                check smaller: across left.sequence.domain as idx all left[idx.item] <= pivot end end
                check pivot_smaller: check_smaller implies pivot <= upper end
                check greater: check_greater implies across left.sequence.domain as idx all left[idx.item] > lower end end
                
                
                right := quick_sort (right, check_smaller, True, upper, pivot)
                check smaller: check_smaller implies across right.sequence.domain as idx all right[idx.item] <= upper end end
                check pivot_greater: check_greater implies pivot > lower end
                check greater: across right.sequence.domain as idx all right[idx.item] > pivot end end
                
                check same_count: a.count = control.count end
                check control_equal_a: across control.sequence.domain as across_idx all control [across_idx.item] =  a [across_idx.item] end end
                check permutation: is_permutation (control.sequence, pivot_arr.sequence + left.sequence + right.sequence) end

                check effectively_sorted:
                    is_sorted (left)
                    and across left.sequence.domain as idx all left [idx.item] <= pivot_arr [1] end 
                    and is_sorted (right)
                    and across right.sequence.domain as idx all right [idx.item] > pivot_arr [1] end
                end
                
                check effectively_permutation:
                    is_permutation (control.sequence, left.sequence + pivot_arr.sequence + right.sequence) and
                    a.count = control.count
                    and across control.sequence.domain as across_idx all control [across_idx.item] =  a [across_idx.item] end
                end
                      
                Result := concatenate_arrays (concatenate_arrays (left, pivot_arr, check_smaller, check_greater, upper, lower), right, check_smaller, check_greater, upper, lower)
                
                check assume: is_permutation (a.sequence, Result.sequence) end

            end

        ensure
            Result.is_wrapped
            Result.is_fresh
            same_elementes: is_permutation (Result.sequence, a.sequence)
            sorted: is_sorted (Result)
            
            
            smaller: check_smaller implies across Result.sequence.domain as idx all Result[idx.item] <= upper end
            greater: check_greater implies across Result.sequence.domain as idx all Result[idx.item] > lower end
            -- most postconditions?
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