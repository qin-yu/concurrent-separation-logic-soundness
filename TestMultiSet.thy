theory TestMultiSet imports Main "~~/src/HOL/Library/Multiset" begin

value "{} :: 'a set"
value "multiset_of [1, 1]"
value "count (multiset_of [1, 1])"

value "mset [1, 0]"
value "mset"
thm "mset_def"
lemma "count (mset [1, 1]) 1 = Suc (Suc 0)" by auto
value "mset [1] + mset [1] + mset [2]"

end

