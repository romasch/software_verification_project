class
    EXPERIMENTS

feature

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

    test_permutation_4 (piv: INTEGER)
        local
            a,b: SIMPLE_ARRAY [INTEGER]
        do
            create a.make (1)
            create b.make (1)
            a [1] := piv
            b [1] := piv
            check a.sequence ~ b.sequence end
            check is_permutation (a.sequence,b.sequence) end
        end

feature -- For use in specifications

    is_permutation (a, b: MML_SEQUENCE [INTEGER]): BOOLEAN
            -- Is `a' a permuation of `b'?
        note
            status: functional, ghost
        do
            Result := a.to_bag ~ b.to_bag
        end
end