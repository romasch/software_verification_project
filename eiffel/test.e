note
	description: "Summary description for {TEST}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	TEST

--inherit
--	EQA_TEST_SET

create
	make

feature
	make
		local
			list: SV_LIST
		do
		end

feature

--	test_empty_list
--		local
--			list: SV_LIST
--		do
--			create list.make
--			assert ("not_empty", list.empty)
--		end

end
