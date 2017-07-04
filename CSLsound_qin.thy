theory CSLsound_qin
imports Main VHelper Lang
begin

text {* This file contains a soundness proof for CSL (with multiple resources)
  as presented by O'Hearn and Brookes including the data-race freedom property
  of CSL.  For simplicity, there is a slight difference regarding variable
  side-conditions: we do not allow resource-owned variables. *}

subsection {* Separation logic assertions *}

text {* A deep embedding of separation logic assertions. *}

datatype assn = 
    Aemp                                           (*r Empty heap *)
  | Apointsto exp exp    (infixl "\<longmapsto>" 200)        (*r Singleton heap *)
  | Astar assn assn      (infixl "**" 100)         (*r Separating conjunction *)
  | Awand assn assn                                (*r Separating implication *)
  | Apure bexp                                     (*r Pure assertion *)
  | Aconj assn assn                                (*r Conjunction *)
  | Adisj assn assn                                (*r Disjunction *)
  | Aex "(nat \<Rightarrow> assn)"                            (*r Existential quantification *)

text {* Separating conjunction of a finite list of assertions is 
  just a derived assertion. *}

primrec 
  Aistar :: "assn list \<Rightarrow> assn"
where
  "Aistar [] = Aemp"
| "Aistar (P # Ps) = Astar P (Aistar Ps)"

primrec
  sat :: "state \<Rightarrow> assn \<Rightarrow> bool" (infixl "\<Turnstile>" 60)
where
  "(\<sigma> \<Turnstile> Aemp)      = (snd \<sigma> = empty)" 
| "(\<sigma> \<Turnstile> E \<longmapsto> E')  = (dom (snd \<sigma>) = { edenot E (fst \<sigma>) } \<and> (snd \<sigma>) (edenot E (fst \<sigma>)) = Some (edenot E' (fst \<sigma>)))" 
| "(\<sigma> \<Turnstile> P ** Q)    = (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> P \<and> (fst \<sigma>, h2) \<Turnstile> Q \<and> snd \<sigma> = (h1 ++ h2) \<and> disjoint (dom h1) (dom h2))" 
| "(\<sigma> \<Turnstile> Awand P Q) = (\<forall>h. disjoint (dom (snd \<sigma>)) (dom h) \<and> (fst \<sigma>, h) \<Turnstile> P \<longrightarrow> (fst \<sigma>, snd \<sigma> ++ h) \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Apure B)   = bdenot B (fst \<sigma>)" 
| "(\<sigma> \<Turnstile> Aconj P Q) = (\<sigma> \<Turnstile> P \<and> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Adisj P Q) = (\<sigma> \<Turnstile> P \<or> \<sigma> \<Turnstile> Q)" 
| "(\<sigma> \<Turnstile> Aex PP)    = (\<exists>v. \<sigma> \<Turnstile> PP v)" 

definition 
  implies :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixl "\<sqsubseteq>" 60)
where
  "P \<sqsubseteq> Q \<equiv> (\<forall>\<sigma>. \<sigma> \<Turnstile> P \<longrightarrow> \<sigma> \<Turnstile> Q)"

lemma sat_resemble: "(\<sigma> \<Turnstile> P ** Q) \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> P \<and> (fst \<sigma>, h2) \<Turnstile> Q \<and> snd \<sigma> = (h1 ++ h2) \<and> disjoint (dom h1) (dom h2))"
by auto

lemma sat_PQ_commute: "\<sigma> \<Turnstile> P ** Q \<longleftrightarrow> \<sigma> \<Turnstile> Q ** P"
apply auto
apply (rule_tac x="h2" in exI, simp, rule_tac x="h1" in exI, simp add: hsimps)+
done

lemma sat_PQR_commute: "\<sigma> \<Turnstile> P ** (Q ** R) \<longleftrightarrow> \<sigma> \<Turnstile> Q ** (P ** R)"
apply (auto)
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1 ++ h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1 ++ h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
done

lemma sat_PQL_commute: "\<sigma> \<Turnstile> P ** (Q ** Aistar (map f l)) \<longleftrightarrow> \<sigma> \<Turnstile> Q ** (P ** Aistar (map f l))"
by (rule sat_PQR_commute)

lemma set_testing: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> set l = set (r # (remove1 r l))"
by (induct l, auto)

lemma set_testing2: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> set (r # (remove1 r l)) = set l"
by (induct l, auto)

lemma aistar_testing2_aux: "r ** Aistar (remove1 r (a # l)) = Aistar (r # remove1 r (a # l))"
by auto

lemma aistar_testing2: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> Aistar (r # (remove1 r l)) = \<sigma> \<Turnstile> Aistar l"
apply (induct l)
apply simp
apply (simp auto)
sorry

lemma set_testing3: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> set (r # (remove1 r (a#l))) = set (a#l)"
apply (induct l)
apply simp
(*apply force*)
apply (rule_tac l="a # aa # l" in set_testing2)
apply auto
done

lemma set_testing4: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> set (a # (remove1 r l)) = set (remove1 r (a#l))"
apply (induct l)
apply simp
by force

value "Aistar [a, b]"
lemma "Aistar [a, b] = a ** (b ** Aemp)"
by auto
value "(a ** b) ** Aemp"

lemma "\<sigma> \<Turnstile> (a ** b) ** Aemp = \<sigma> \<Turnstile> a ** (b ** Aemp)"
by simp

lemma "\<sigma> \<Turnstile> Aistar [a, b] = \<sigma> \<Turnstile> Aistar [b, a]"
apply auto
by (rule, auto simp add: hsimps)+

lemma "\<sigma> \<Turnstile> Aistar [a, b, c] = \<sigma> \<Turnstile> Aistar [c, a, b]"
apply auto
apply (rule_tac x="h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1 ++ h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1 ++ h2a" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
done

lemma set_testing5: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> Aistar (a # (remove1 r l)) = \<sigma> \<Turnstile> Aistar (remove1 r (a#l))"
apply (induct l)
apply simp
apply (rename_tac b l)
apply (safe, clarsimp)
apply (rule, auto simp add: hsimps)
sorry

lemma set_testing_comb: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> Aistar (r # (remove1 r l)) = Aistar l \<and> Aistar (a # (remove1 r l)) = Aistar (remove1 r (a#l)"

lemma sat_resemble2_pre: "Aistar (a # l) = a ** Aistar l"
by auto
lemma sat_resemble2: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> Aistar l = r ** Aistar (remove1 r l)"
apply (induct l)
apply simp
apply (simp only: sat_resemble2_pre)
sorry

lemma sat_resemble3_pre: "\<sigma> \<Turnstile> Aistar (a # l) = \<sigma> \<Turnstile> a ** Aistar l"
by auto
lemma sat_resemble3: "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> Aistar l \<longleftrightarrow> \<sigma> \<Turnstile> r ** Aistar (remove1 r l)"
apply (induct l)
apply (simp)
apply (simp only: sat_resemble3_pre)
sorry

lemma sat_istar_map_expand_pre:
  "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<Turnstile> Aistar l
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> r
              \<and> (fst \<sigma>, h2) \<Turnstile> Aistar (remove1 r l)
              \<and> snd \<sigma> = (h1 ++ h2)
              \<and> disjoint (dom h1) (dom h2))"
apply (case_tac \<sigma>, rename_tac s h, clarify)
apply (induction l arbitrary: \<sigma>)
apply auto
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1++h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1++h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
done

lemma sat_istar_map_expand:
  "\<lbrakk> r \<in> set l \<rbrakk> \<Longrightarrow>  
     \<sigma> \<Turnstile> Aistar (map f l)
     \<longleftrightarrow> (\<exists>h1 h2. (fst \<sigma>, h1) \<Turnstile> f r
              \<and> (fst \<sigma>, h2) \<Turnstile> Aistar (map f (remove1 r l))
              \<and> snd \<sigma> = (h1 ++ h2)
              \<and> disjoint (dom h1) (dom h2))"
apply (case_tac \<sigma>, rename_tac s h, clarify)
apply (induction l arbitrary: \<sigma>)
apply auto
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1++h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1a" in exI, simp add: hsimps)
apply (rule_tac x="h1++h2a" in exI, simp add: hsimps)
apply (rule_tac x="h1" in exI, simp add: hsimps)
apply (rule_tac x="h2a" in exI, simp add: hsimps)
done

value "r \<in> set []"