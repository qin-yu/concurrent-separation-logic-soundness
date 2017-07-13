theory TestMultiSet imports Main "~~/src/HOL/Library/Multiset" begin

value "{} :: 'a set"
value "multiset_of [1, 1]"
value "count (multiset_of [1, 1])"

value "mset [1, 0]"
value "mset"
thm "mset_def"
lemma "count (mset [1, 1]) 1 = Suc (Suc 0)" by auto
value "mset [1] + mset [1] + mset [2]"
value "mset [1, 1, 2] - mset [1]"

value "{#}"
value "{#a, b#}"
value "(inv multiset_of) {#1, 1#}"
value "(inv multiset_of) {#}"
lemma "(inv multiset_of {#1, 1#}) = [1, 1]" 
oops
lemma "(inv multiset_of {#}) = []" 
oops
value "(inv mset) {#}"
value "(inv mset) {#1#}"

value "[x. x\<in>#{#1, 0#}]"
value "1 \<in># {#1, 0#}"
value "0 \<in># {#1, 0#}"
value "remove1 0 [x. x\<in>#{#1, 0#}]"

value "[x. x\<in>{0, 1}]"
lemma "\<forall>x. x\<in>#(mset xs) \<Longrightarrow> x\<in>(set xs)"

value "int (count {#1, 1, 1, 1, 1, 1#} 1)"

value "filter_mset (\<lambda>x. \<not>(x=0)) {#0, (Suc 0)#}"

value "[\<lambda>x. x \<in># {#0, (Suc 0), (Suc (Suc 0))#}]"

end

