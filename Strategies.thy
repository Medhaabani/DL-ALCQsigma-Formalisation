(* TODO in this theory: separate lemmas required for termination 
   from lemmas for proving rule invertibility results 
 *)

theory Strategies imports Decide_satisfiability ALC_PrInfrastruc "~~/src/HOL/Library/Multiset"
begin


(*--------------- Basic definitions and properties -------------------------*)

(* Strategies and strategy combinators *)

definition progress_with :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where 
"progress_with r = (\<lambda> y.  (\<exists> z. z \<noteq> y \<and> r y z))"

definition rexhaust :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"rexhaust r = (\<lambda> x y. (r^** x y) \<and> \<not> progress_with r y)"

(* strict part of rexhaust *)
definition srexhaust :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"srexhaust r = (\<lambda> x y. rexhaust r x y \<and> x \<noteq> y)"

definition exhaust :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"exhaust r = (\<lambda> x y. (r^++ x y) \<and> \<not> (\<exists> z. z \<noteq> y \<and> r y z))"


definition complete_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"complete_rel r = (\<forall> x. \<exists> y. r x y)"

definition induces_change :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where 
"induces_change r = (\<lambda> y.  (\<forall> z. r y z \<longrightarrow> y \<noteq> z))"


(*--------------- Proofs of properties of combinators  -------------------------*)


lemma rexhaust_saturated_abox:
   "rexhaust r ab1 ab2 \<Longrightarrow> induces_change r ab2 \<Longrightarrow> saturated_abox ab2 r"
by (clarsimp simp add: rexhaust_def induces_change_def saturated_abox_def progress_with_def) 
   blast

lemma srexhaust_saturated_abox:
   "srexhaust r ab1 ab2 \<Longrightarrow> induces_change r ab2 \<Longrightarrow> saturated_abox ab2 r"
by (clarsimp simp add: srexhaust_def rexhaust_saturated_abox)



lemma exhausts_equal_with_progress: "progress_with r ab1 \<Longrightarrow> 
   rexhaust r ab1 ab2 = srexhaust r ab1 ab2"
by (simp add: induces_change_def rexhaust_def srexhaust_def progress_with_def)
   blast


lemma "(r^**) = (alternative_rule (r^++)(op =))"    
apply (clarsimp simp add: alternative_rule_def fun_eq_iff)
apply (rule iffI)
apply (drule rtranclpD) apply blast
apply (elim disjE)
apply (erule tranclp_into_rtranclp)
apply simp
done


lemma "((r1 = (op =)) \<and>  (r2 = (op =))) \<Longrightarrow> (alternative_rule r1 r2 = (op =))"
by (clarsimp simp add: complete_rel_def alternative_rule_def fun_eq_iff)

lemma "complete_rel r1 \<Longrightarrow> complete_rel r2 \<Longrightarrow>
  (alternative_rule r1 r2 = (op =)) = ((r1 = (op =)) \<and>  (r2 = (op =)))"
apply (clarsimp simp add: complete_rel_def alternative_rule_def fun_eq_iff)
by metis


lemma "rexhaust r x y \<Longrightarrow> alternative_rule (exhaust r) (op =) x y"    
apply (clarsimp simp add: rexhaust_def exhaust_def 
  alternative_rule_def progress_with_def fun_eq_iff)
apply (drule rtranclpD) apply blast
done

(* TODO: rename *)
lemma foobar: "(r^++ x y) \<Longrightarrow> \<exists> z. r x z"
apply (erule tranclp_induct)
apply blast+
done

lemma "\<not> (\<exists> z. r a z) \<Longrightarrow> \<not> (\<exists> z. exhaust r a z)"
apply (clarsimp simp add: rexhaust_def exhaust_def alternative_rule_def fun_eq_iff)
apply (erule tranclp_induct)
apply blast
apply (drule foobar)
apply blast
done


lemma srexhaust_rtrancl_incl: 
  "{(x, y). r\<^sup>*\<^sup>* x y \<and> (\<forall>z. z = y \<or> \<not> r y z) \<and> x \<noteq> y} \<subseteq> {(x, y). r\<^sup>+\<^sup>+ x y}"
by (fastforce dest: rtranclpD)


lemma wfP_srexhaust: "wfP r \<Longrightarrow> wfP (srexhaust r)"
apply (rule wfP_subset)
apply (erule wfP_trancl)
apply (simp add: srexhaust_def rexhaust_def progress_with_def)
apply (rule srexhaust_rtrancl_incl [to_pred])
done

(*--------------- Proofs of properties of individual rules -------------------------*)


lemma rename_in_form_rename_in_abox:
  "f \<in> ab \<Longrightarrow> fr = rename_in_form f ren  \<Longrightarrow> fr \<in> rename_in_abox ab ren"
by (simp add: rename_in_abox_def)

lemma rename_in_form_rename_in_abox_direct:
  "f \<in> ab \<Longrightarrow> rename_in_form f ren  \<in> rename_in_abox ab ren"
by (simp add: rename_in_abox_def)

lemma rename_in_form_rename_in_abox_rewr:
  "(fr \<in> rename_in_abox ab ren) = (\<exists> f. f \<in> ab \<and> fr = rename_in_form f ren)"
by (simp add: rename_in_abox_def) fastforce

lemma rename_in_form_rename_in_abox_impl:
  "(fr \<in> rename_in_abox ab ren) \<Longrightarrow> (\<exists> f. f \<in> ab \<and> rename_in_form f ren = fr)"
by (simp add: rename_in_abox_def) fastforce

lemma rename_in_form_FactFm: "(rename_in_form f ren = FactFm fctr) = 
(\<exists> fct. (f = FactFm fct) \<and> rename_in_fact fct ren = fctr)"
by (case_tac f) auto

lemma rename_in_fact_Inst: "(rename_in_fact fct ren = Inst x c) = 
(\<exists> xf cf. (fct = Inst xf cf) \<and> rename_in_var xf ren = x \<and> rename_in_concept cf ren = c)"
by (case_tac fct) auto

lemma rename_in_fact_Atom: "(rename_in_fact fct ren = AtomR b r x y) = 
(\<exists> xf yf. (fct = AtomR b r xf yf) \<and> rename_in_var xf ren = x \<and> rename_in_var yf ren = y)"
by (case_tac fct) auto

lemma rename_in_fact_Eq: "(rename_in_fact fct ren = Eq b x y) = 
(\<exists> xf yf. (fct = Eq b xf yf) \<and> rename_in_var xf ren = x \<and> rename_in_var yf ren = y)"
by (case_tac fct) auto

lemma rename_in_form_ConjFm: "(rename_in_form f ren = ConjFm fr1 fr2) =
(\<exists> f1 f2. (f = ConjFm f1 f2) \<and> fr1 = rename_in_form f1 ren \<and> fr2 = rename_in_form f2 ren)"
by (case_tac f) auto

lemma rename_in_form_DisjFm: "(rename_in_form f ren = DisjFm fr1 fr2) =
(\<exists> f1 f2. (f = DisjFm f1 f2) \<and> fr1 = rename_in_form f1 ren \<and> fr2 = rename_in_form f2 ren)"
by (case_tac f) auto

lemma rename_in_form_SubstFm: "(rename_in_form f ren = SubstFm fmr sbr) =
(\<exists> fm sb. (f = SubstFm fm sb) \<and> fmr = rename_in_form fm ren \<and> sbr = rename_in_subst sb ren)"
by (case_tac f) auto

lemma rename_in_concept_ConjC: "(rename_in_concept c ren = ConjC cr1 cr2) =
(\<exists> c1 c2. (c = ConjC c1 c2) \<and> cr1 = rename_in_concept c1 ren \<and> cr2 = rename_in_concept c2 ren)"
by (case_tac c) auto

lemma rename_in_concept_DisjC: "(rename_in_concept c ren = DisjC cr1 cr2) =
(\<exists> c1 c2. (c = DisjC c1 c2) \<and> cr1 = rename_in_concept c1 ren \<and> cr2 = rename_in_concept c2 ren)"
by (case_tac c) auto

lemma rename_in_concept_NumRestrC: "(rename_in_concept c ren = NumRestrC nro n r cr1) =
(\<exists> c1. (c = NumRestrC nro n r c1) \<and> cr1 = rename_in_concept c1 ren)"
by (case_tac c) auto

lemma rename_in_concept_SubstC: "(rename_in_concept c ren = SubstC c1r sbr) =
(\<exists> c1 sb.  (c = SubstC c1 sb) \<and>  c1r = rename_in_concept c1 ren \<and> sbr = rename_in_subst sb ren)"
by (case_tac c) auto


lemma saturated_rename_conjc: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (conjc_rule_indiv f) \<Longrightarrow> 
   saturated_abox (rename_in_abox ab sbsts) (conjc_rule_indiv (rename_in_form f sbsts))"
apply (clarsimp simp add: saturated_abox_def conjc_rule_indiv.simps conjc_applicable.simps)
apply (clarsimp simp add: rename_in_form_FactFm  rename_in_fact_Inst rename_in_concept_ConjC)
apply (clarsimp simp add: rename_in_form_rename_in_abox)
done

lemma saturated_rename_disjc: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (disjc_rule_indiv f) \<Longrightarrow> 
   saturated_abox (rename_in_abox ab sbsts) (disjc_rule_indiv (rename_in_form f sbsts))"
apply (clarsimp simp add: saturated_abox_def disjc_rule_indiv.simps disjc_applicable.simps)
apply (clarsimp simp add: rename_in_form_FactFm  rename_in_fact_Inst rename_in_concept_DisjC)
apply (clarsimp simp add: all_conj_distrib)
apply (elim disjE)
apply (clarsimp simp add: rename_in_form_rename_in_abox)+
done

lemma saturated_rename_substc: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (substc_rule_indiv f) \<Longrightarrow> 
  saturated_abox (rename_in_abox ab ren) (substc_rule_indiv (rename_in_form f ren))"
apply (simp add: saturated_abox_def substc_rule_indiv.simps substc_applicable.simps)
apply (clarsimp simp add: rename_in_form_FactFm  rename_in_fact_Inst rename_in_concept_SubstC
  simp del: push_subst_form.simps rename_in_form.simps)
apply (rename_tac x c sb)

apply (subgoal_tac "push_subst_form (rename_in_form (FactFm (Inst x (SubstC c sb))) ren) [] \<in> rename_in_abox ab ren")
apply simp
apply (subgoal_tac "push_subst_form (rename_in_form (FactFm (Inst x (SubstC c sb))) ren) [] =
  rename_in_form (push_subst_form (FactFm (Inst x (SubstC c sb))) []) ren")
  prefer 2 apply (simp only: rename_in_form_push_subst_form) apply simp
apply (fast intro: rename_in_form_rename_in_abox)
done

lemma saturated_rename_conjfm: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (conjfm_rule_indiv f) \<Longrightarrow> 
   saturated_abox (rename_in_abox ab ren) (conjfm_rule_indiv (rename_in_form f ren))"
apply (simp add: saturated_abox_def conjfm_rule_indiv.simps conjfm_applicable.simps)
apply (clarsimp simp add: rename_in_form_rename_in_abox rename_in_form_ConjFm)
done

lemma saturated_rename_disjfm: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (disjfm_rule_indiv f) \<Longrightarrow> 
  saturated_abox (rename_in_abox ab ren) (disjfm_rule_indiv (rename_in_form f ren))"
by (clarsimp simp add: saturated_abox_def disjfm_rule_indiv.simps disjfm_applicable.simps
       rename_in_form_DisjFm)
   (auto simp add: rename_in_form_rename_in_abox) 

lemma saturated_rename_substfm: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (substfm_rule_indiv f) \<Longrightarrow> 
  saturated_abox (rename_in_abox ab ren) (substfm_rule_indiv (rename_in_form f ren))"
apply (simp add: saturated_abox_def substfm_rule_indiv.simps substfm_applicable.simps)
apply (clarsimp simp add: rename_in_form_SubstFm
  simp del: push_subst_form.simps rename_in_form.simps)
apply (rename_tac fm sb)

apply (subgoal_tac "push_subst_form (rename_in_form (SubstFm fm sb) ren) [] \<in> rename_in_abox ab ren")
apply simp
apply (subgoal_tac "push_subst_form (rename_in_form (SubstFm fm sb) ren) [] =
  rename_in_form (push_subst_form (SubstFm fm sb) []) ren")
  prefer 2 apply (simp only: rename_in_form_push_subst_form) apply simp
apply (fast intro: rename_in_form_rename_in_abox)
done


lemma saturated_rename_choose_stable_aux: " f \<in> ab \<Longrightarrow>
       choose_stable_rule_indiv (rename_in_form f ren) (rename_in_abox ab ren) ab2 \<Longrightarrow>
       \<exists> ab2. choose_stable_rule_indiv f ab ab2"
apply (clarsimp simp add: choose_stable_rule_indiv.simps)
apply (drule rename_in_form_rename_in_abox_impl)+
apply (clarsimp simp add: rename_in_form_FactFm rename_in_fact_Inst
  rename_in_fact_Atom rename_in_fact_Eq rename_in_concept_NumRestrC)

apply (rename_tac n r x1 x2 x' y c1 c2)

apply (intro exI conjI)
apply assumption
apply (clarsimp simp add: rename_in_form_rename_in_abox)
apply (clarsimp simp add: rename_in_form_rename_in_abox)
prefer 2 apply (rule disjI1) apply (rule refl)
apply clarify

apply (subgoal_tac "rename_in_form (FactFm (Inst y (neg_norm_concept False c1))) ren \<in> rename_in_abox ab ren")
   prefer 2 apply (simp add:  rename_in_form_rename_in_abox)
apply (simp add: rename_in_concept_neg_norm_concept)

done


lemma saturated_rename_choose_stable: 
  "f \<in> ab \<Longrightarrow> saturated_abox ab (choose_stable_rule_indiv f) \<Longrightarrow> 
   saturated_abox (rename_in_abox ab ren) (choose_stable_rule_indiv (rename_in_form f ren))"
by (clarsimp simp add: saturated_abox_def) (fast dest: saturated_rename_choose_stable_aux)


declare rename_in_var.simps [simp del]

(* The precondition \<not> contains_clash ... is required:
   if numrestrc_ge is blocked for x: ([\<le>] 2 r C), (x r y1), (x r y2), y1 \<noteq> y2, 
   it becomes unblocked for subst [y1 := y2], but this produces a clash 
 *)
lemma numrestrc_ge_not_blocked: "
   \<not> numrestrc_ge_blocked
       (rename_in_abox ab [ISubst v1 v2])
       (rename_in_var x1 [ISubst v1 v2]) n r
       (rename_in_concept c2 [ISubst v1 v2]) \<Longrightarrow>
   \<not> contains_clash (rename_in_abox ab [ISubst v1 v2]) \<Longrightarrow>
   rename_in_var x2 [ISubst v1 v2] = rename_in_var x1 [ISubst v1 v2] \<Longrightarrow>
   rename_in_concept c1 [ISubst v1 v2] = rename_in_concept c2 [ISubst v1 v2] \<Longrightarrow>
   \<not> numrestrc_ge_blocked ab x1 n r c1"

apply (case_tac "v2 = v1") apply simp 
apply (clarsimp simp add: numrestrc_ge_blocked_def)
apply (rename_tac S)

(* case v2 \<noteq> v1 *)

apply (case_tac "v1 \<in> S")


apply (case_tac "v2 \<in> S")

(* ---- case v1\<in>S and v2\<in>S *)

apply (rule_tac x=v1 in rev_bexI) apply assumption
apply clarsimp
apply (drule_tac x=v1 in bspec, assumption)
apply (drule_tac x=v2 in bspec, assumption)
apply simp
apply (subgoal_tac "FactFm (Eq False v2 v2) \<in>rename_in_abox ab [ISubst v1 v2]" )
apply (simp add: contains_clash_def)
apply (fastforce simp add: rename_in_form_rename_in_abox rename_in_var.simps)

(* ---- case v1\<in>S and v2\<notin>S *)

apply (drule_tac x= "(insert v2 S) - {v1}" in spec)
apply clarsimp

apply (elim disjE)

(* first disjunction *)
apply clarsimp
apply (case_tac "z = v1") apply simp

apply (elim disjE)
apply clarsimp+
apply (fastforce simp add: rename_in_form_rename_in_abox)

apply (subgoal_tac "(rename_in_var z [ISubst v1 v2]) = z") 
   prefer 2 apply (simp add: rename_in_var.simps) 
apply (fastforce simp add: rename_in_form_rename_in_abox)

(* second disjunction *)
apply clarsimp
apply (rename_tac S z1 z2)
apply (case_tac "z2 = v1") apply simp
apply (subgoal_tac "(rename_in_var z1 [ISubst v1 v2]) = z1") 
   prefer 2 apply (simp add: rename_in_var.simps)
apply (subgoal_tac "(rename_in_var z2 [ISubst v1 v2]) = z2") 
   prefer 2 apply (simp add: rename_in_var.simps)

apply (elim disjE)
apply simp_all
apply clarsimp

(* 4 subgoals *)
apply (fastforce simp add: rename_in_form_rename_in_abox)
(* 3 subgoals *)
apply (fastforce simp add: rename_in_form_rename_in_abox)

(* 2 subgoals *)
apply (subgoal_tac "FactFm (Eq False z1 z2) \<in> ab \<or> FactFm (Eq False z2 z1) \<in> ab") 
  prefer 2 apply blast
  
apply (elim disjE)
apply (fastforce simp add: rename_in_form_rename_in_abox)
apply (fastforce simp add: rename_in_form_rename_in_abox)


(* ---- case v1\<notin>S *)

apply (drule_tac x= S in spec) apply simp

apply (elim disjE)

(* first disjunction *)
apply clarsimp
apply (rename_tac S z)
apply (rule_tac x=z in rev_bexI) apply assumption
apply clarsimp

apply (subgoal_tac "rename_in_form (FactFm (AtomR True r x1 z)) [ISubst v1 v2]\<in> rename_in_abox ab [ISubst v1 v2]")
  prefer 2 apply (fast elim: rename_in_form_rename_in_abox_direct)
apply (subgoal_tac "rename_in_form (FactFm (Inst z c1)) [ISubst v1 v2]\<in> rename_in_abox ab [ISubst v1 v2]")
  prefer 2 apply (fast elim: rename_in_form_rename_in_abox_direct)
apply (simp add: rename_in_var.simps split : if_split_asm)

(* second disjunction *)
apply clarsimp
apply (rename_tac S z1 z2)

apply (drule_tac x=z1 in bspec, assumption)
apply (drule_tac x=z2 in bspec, assumption)
apply simp
apply (elim disjE)

apply (subgoal_tac "rename_in_form (FactFm (Eq False z1 z2)) [ISubst v1 v2] \<in> rename_in_abox ab [ISubst v1 v2]")
  prefer 2 apply (fast elim: rename_in_form_rename_in_abox_direct)
apply (simp add: rename_in_var.simps split : if_split_asm)
apply (subgoal_tac "rename_in_form (FactFm (Eq False z2 z1)) [ISubst v1 v2] \<in> rename_in_abox ab [ISubst v1 v2]")
  prefer 2 apply (fast elim: rename_in_form_rename_in_abox_direct)
apply (simp add: rename_in_var.simps split : if_split_asm)
done

(* TODO: neq_complete subgoal still open.
   To be noted: these are invertibility results that are nice to have, 
   but not essential for the rest.
*)
lemma saturated_rename_numrestrc_ge_aux: 
" f \<in> (ab ::('nr, 'nc, 'ni::new_var_set_incr_class) abox)  \<Longrightarrow>
  finite ab \<Longrightarrow> 
  \<not> contains_clash (rename_in_abox ab [ISubst v1 v2]) \<Longrightarrow>
  v2 < v1 \<Longrightarrow>
  numrestrc_ge_rule_indiv (rename_in_form f [ISubst v1 v2]) (rename_in_abox ab [ISubst v1 v2]) ab2 \<Longrightarrow>
  \<exists> ab2. numrestrc_ge_rule_indiv f ab ab2"
apply (clarsimp simp add: numrestrc_ge_rule_indiv.simps)
apply (drule rename_in_form_rename_in_abox_impl)+
apply (clarsimp simp add: rename_in_form_FactFm rename_in_fact_Inst
  rename_in_fact_Atom rename_in_fact_Eq rename_in_concept_NumRestrC)

apply (rename_tac r Y x1 x2 c1 c2)
apply (clarsimp simp add: numrestrc_ge_applicable.simps)
apply (intro conjI impI allI)

prefer 3
apply (rule_tac x="gen_set_incr_varname (card Y) ab x1" in exI)
apply (simp add: fresh_set_def gen_set_varname_notin_fv_abox)

apply (erule  numrestrc_ge_not_blocked) apply assumption+

sorry


declare rename_in_var.simps [simp add]


lemma saturated_rename_numrestrc_ge: 
  "f \<in> (ab ::('nr, 'nc, 'ni::new_var_set_incr_class) abox) \<Longrightarrow>
  finite ab \<Longrightarrow>
  \<not> contains_clash (rename_in_abox ab [ISubst v1 v2]) \<Longrightarrow>
  v2 < v1 \<Longrightarrow>
  saturated_abox ab (numrestrc_ge_rule_indiv f) \<Longrightarrow> 
   saturated_abox (rename_in_abox ab [ISubst v1 v2]) (numrestrc_ge_rule_indiv (rename_in_form f [ISubst v1 v2]))"
by (clarsimp simp add: saturated_abox_def)
   (fast dest: saturated_rename_numrestrc_ge_aux)



lemma saturated_conjc_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (conjc_rule_indiv f)"
by (simp add: saturated_abox_def conjc_rule_indiv.simps conjc_applicable.simps)

lemma saturated_disjc_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (disjc_rule_indiv f)"
by (simp add: saturated_abox_def disjc_rule_indiv.simps disjc_applicable.simps)

lemma saturated_allc_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (allc_rule_indiv f)"
by (simp add: saturated_abox_def allc_rule_indiv.simps allc_applicable.simps)

lemma saturated_somec_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (somec_rule_indiv (z, f))"
by (simp add: saturated_abox_def somec_rule_indiv.simps somec_applicable.simps)

lemma saturated_substc_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (substc_rule_indiv f)"
by (simp add: saturated_abox_def substc_rule_indiv.simps substc_applicable.simps)

lemma saturated_eq_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (eq_rule_indiv f)"
by (simp add: saturated_abox_def eq_rule_indiv.simps eq_applicable.simps)

lemma saturated_conjfm_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (conjfm_rule_indiv f)"
by (simp add: saturated_abox_def conjfm_rule_indiv.simps conjfm_applicable.simps)
         
lemma saturated_disjfm_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (disjfm_rule_indiv f)"
by (simp add: saturated_abox_def disjfm_rule_indiv.simps disjfm_applicable.simps)

lemma saturated_substfm_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (substfm_rule_indiv f)"
by (simp add: saturated_abox_def substfm_rule_indiv.simps substfm_applicable.simps)

lemma saturated_choose_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (choose_rule_indiv f)"
by (simp add: saturated_abox_def choose_rule_indiv.simps)

lemma saturated_choose_stable_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (choose_stable_rule_indiv f)"
by (simp add: saturated_abox_def choose_stable_rule_indiv.simps)

lemma saturated_numrestrc_ge_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (numrestrc_ge_rule_indiv f)"
by (simp add: saturated_abox_def numrestrc_ge_rule_indiv.simps numrestrc_ge_applicable.simps)

lemma saturated_numrestrc_lt_non_elem: "f \<notin> ab \<Longrightarrow> saturated_abox ab (numrestrc_lt_rule_indiv f)"
by (simp add: saturated_abox_def numrestrc_lt_rule_indiv.simps numrestrc_lt_applicable.simps)


lemma saturated_abox_ex_rule_closure:
   "saturated_abox ab (ex_rule_closure r) = (\<forall> f. saturated_abox ab (r f))"
by (fastforce simp add: saturated_abox_def ex_rule_closure_def)


lemma saturated_preserving_eq_rule_reduction: 
     "(alternative_rule_of_set {eq_rule, numrestrc_lt_rule}) ab1 ab2 \<Longrightarrow>
            \<forall> f. saturated_abox ab1 (rl f) \<Longrightarrow>
            f \<notin> ab2 \<longrightarrow> saturated_abox ab2 (rl f) \<Longrightarrow> 
             \<forall> ren f'. f' \<in> ab1 \<longrightarrow>  saturated_abox ab1 (rl f') \<longrightarrow> 
     saturated_abox (rename_in_abox ab1 ren) (rl (rename_in_form f' ren)) 
 \<Longrightarrow> saturated_abox ab2 (rl f)"
apply (case_tac "f \<notin> ab2") 
apply simp+
apply (simp add: alternative_rule_of_set_def)
apply (elim disjE)
apply (clarsimp simp add: eq_rule_def ex_rule_closure_def eq_rule_indiv.simps)
apply (clarsimp simp add: rename_in_form_rename_in_abox_rewr)
apply (clarsimp simp add: numrestrc_lt_rule_def ex_rule_closure_def numrestrc_lt_rule_indiv.simps)
apply (clarsimp simp add: rename_in_form_rename_in_abox_rewr)
done

lemma saturated_preserving_under_eq_rule_conjfm: 
    "(alternative_rule_of_set {eq_rule, numrestrc_lt_rule}) ab1 ab2 \<Longrightarrow>
    saturated_abox ab1 conjfm_rule \<Longrightarrow> saturated_abox ab2 conjfm_rule" 
apply (clarsimp simp add: saturated_abox_ex_rule_closure conjfm_rule_def)
apply (erule saturated_preserving_eq_rule_reduction, assumption)
apply (clarsimp simp add: saturated_conjfm_non_elem saturated_rename_conjfm)+
done

lemma saturated_preserving_under_eq_rule_disjfm: 
    "(alternative_rule_of_set {eq_rule, numrestrc_lt_rule}) ab1 ab2 \<Longrightarrow>
    saturated_abox ab1 disjfm_rule \<Longrightarrow> saturated_abox ab2 disjfm_rule" 
apply (clarsimp simp add: saturated_abox_ex_rule_closure disjfm_rule_def)
apply (erule saturated_preserving_eq_rule_reduction, assumption)
apply (clarsimp simp add: saturated_disjfm_non_elem saturated_rename_disjfm)+
done


lemma saturated_preserving_under_eq_rule_numrestrc_ge: 
    "(alternative_rule_of_set {eq_rule, numrestrc_lt_rule}) ab1 ab2 \<Longrightarrow>
    saturated_abox (ab1::('nr, 'nc, 'ni::new_var_set_incr_class) abox) numrestrc_ge_rule \<Longrightarrow> 
    finite ab1 \<Longrightarrow>  \<not> contains_clash ab2 \<Longrightarrow>
    saturated_abox ab2 numrestrc_ge_rule" 
apply (clarsimp simp add: saturated_abox_ex_rule_closure numrestrc_ge_rule_def)
apply (case_tac "f \<notin> ab2") 
apply (simp add: saturated_numrestrc_ge_non_elem)
apply (simp add: alternative_rule_of_set_def)
apply (elim disjE)
apply (clarsimp simp add: eq_rule_def ex_rule_closure_def eq_rule_indiv.simps)
apply (clarsimp simp add: rename_in_form_rename_in_abox_rewr saturated_rename_numrestrc_ge
       split : if_split_asm)
apply (clarsimp simp add: numrestrc_lt_rule_def ex_rule_closure_def numrestrc_lt_rule_indiv.simps)
apply (clarsimp simp add: rename_in_form_rename_in_abox_rewr saturated_rename_numrestrc_ge)
done

(* TODO: the lemma is still incomplete, other rules still to be added *) 
lemma "(alternative_rule_of_set {eq_rule, numrestrc_lt_rule}) ab1 ab2 \<Longrightarrow>
       saturated_abox ab1 (alternative_rule_of_set {conjfm_rule, disjfm_rule}) \<Longrightarrow>
       saturated_abox ab2 (alternative_rule_of_set {conjfm_rule, disjfm_rule})"
by (simp add: saturated_preserving_under_eq_rule_conjfm
              saturated_preserving_under_eq_rule_disjfm)


(*==========================================================================*)
(* All the following: currently not used *)
(*==========================================================================*)

lemma rename_in_abox_inversion: 
   "(f' \<in> rename_in_abox ab sbsts) = (\<exists> f. f' = (rename_in_form f sbsts) \<and> f \<in> ab)"
by (fastforce simp add: rename_in_abox_def) 

lemma rename_in_form_inversion_ConstFm: 
   "(ConstFm c = rename_in_form f sbsts) = (f = (ConstFm c))"
by (case_tac f) auto

lemma rename_in_form_inversion_FactFm: 
   "((FactFm fct') = rename_in_form f sbsts) = 
     (\<exists> fct. (f = FactFm fct) \<and> fct' = rename_in_fact fct sbsts)"
by (case_tac f) auto

lemma rename_in_form_inversion_BinopFm:
   "((BinopFm bop f1' f2') = rename_in_form f sbsts) = 
     (\<exists> f1 f2. (f = BinopFm bop f1 f2) \<and> 
      f1' = rename_in_form f1 sbsts \<and> f2' = rename_in_form f2 sbsts)"
by (case_tac f) auto

lemma rename_in_form_inversion_SubstFm: 
   "((SubstFm f1' sb') = rename_in_form f sbsts) = 
     (\<exists> f1 sb. (f = SubstFm f1 sb) \<and> 
        f1' = rename_in_form f1 sbsts \<and> sb' = rename_in_subst sb sbsts)"
by (case_tac f) auto

lemma rename_in_fact_inversion_Inst:
   "((Inst x' c') = rename_in_fact f sbsts) = 
     (\<exists> x c. (f = Inst x c) \<and> x' = rename_in_var x sbsts \<and> c' = rename_in_concept c sbsts)"
by (case_tac f) simp_all

lemma rename_in_fact_inversion_AtomR:
   "((AtomR sign r x' y') = rename_in_fact f sbsts) = 
     (\<exists> x y. (f = AtomR sign r x y) \<and> 
     x' = rename_in_var x sbsts \<and> y' = rename_in_var y sbsts)"
by (case_tac f) auto

lemma rename_in_fact_inversion_Eq:
   "((Eq sign x' y') = rename_in_fact f sbsts) = 
     (\<exists> x y. (f = Eq sign x y) \<and> 
     x' = rename_in_var x sbsts \<and> y' = rename_in_var y sbsts)"
by (case_tac f) auto


lemma rename_in_concept_inversion_BinopC:
   "((BinopC bop c1' c2') = rename_in_concept c sbsts) = 
     (\<exists> c1 c2. (c = BinopC bop c1 c2) \<and> 
      c1' = rename_in_concept c1 sbsts \<and> c2' = rename_in_concept c2 sbsts)"
apply (case_tac c) 
apply simp_all
apply (case_tac bop) 
apply fastforce+
done

lemma rename_in_concept_inversion_NumRestrC:
   "((NumRestrC nro n r c1') = rename_in_concept c sbsts) = 
     (\<exists> c1. (c = (NumRestrC nro n r c1) \<and> c1' = rename_in_concept c1 sbsts))"
apply (case_tac c) 
apply simp_all
apply fastforce
done


(* TODO: currently not needed *)
lemma foo : "conjc_applicable f' (rename_in_abox ab sbsts) \<Longrightarrow> 
  \<exists> f. f' = (rename_in_form f sbsts) \<and> conjc_applicable f ab"
apply (simp add: conjc_applicable.simps rename_in_abox_inversion)
apply clarsimp
apply (clarsimp simp add: rename_in_form_inversion_FactFm)
apply (clarsimp simp add: rename_in_fact_inversion_Inst)
apply (clarsimp simp add: rename_in_concept_inversion_BinopC)
apply (intro conjI exI)
apply (rule refl)+
apply assumption
apply fastforce
done
(*
lemma "saturated_abox ab conjc_rule \<Longrightarrow> saturated_abox (rename_in_abox ab sbsts) conjc_rule"
apply (clarsimp simp add: saturated_abox_def conjc_rule_def ex_rule_closure_def)
apply (rename_tac ab2 f)

apply (simp add: conjc_rule_indiv.simps)
apply clarsimp
apply (subgoal_tac "\<exists> x' c1' c2'. FactFm (Inst x' (ConjC c1' c2')) \<in> ab \<and> 
   x = rename_in_var x' sbsts \<and> c1 = rename_in_concept c1' sbsts \<and> c2 = rename_in_concept c2' sbsts")
   prefer 2
   apply (clarsimp simp add: rename_in_abox_inversion)
   apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)
   apply blast
   
apply clarsimp
apply (rename_tac x' c1' c2')
apply (drule_tac x=" insert (FactFm (Inst x' c2')) (insert (FactFm (Inst x' c1')) ab)" in spec)
apply (drule_tac x="FactFm (Inst x' (ConjC c1' c2'))" in spec)
apply clarsimp
apply (subgoal_tac "(\<forall>c2. c2' \<noteq> c2) = False") prefer 2 apply blast
apply (clarsimp simp add: conjc_applicable.simps)

apply (case_tac "FactFm (Inst (rename_in_var x' sbsts) (rename_in_concept c1' sbsts))
       \<in> rename_in_abox ab sbsts")
apply (clarsimp simp add: rename_in_abox_inversion)+
done
*)
lemma schlubs1: "(\<forall>f. (\<exists>f2. f = g f2 \<and> P f2) \<longrightarrow> Q f) = (\<forall> f2. P f2 \<longrightarrow> Q (g f2))"
by blast

lemma schlubs2: "(\<forall>f. (\<exists>f2 f3. f = g f2 f3 \<and> P f2 f3) \<longrightarrow> Q f) 
    = (\<forall> f2 f3. P f2 f3 \<longrightarrow> Q (g f2 f3))"
by blast


lemma "\<not> (saturated_abox (rename_in_abox ab sbsts) conjc_rule) 
   \<Longrightarrow> \<not> (saturated_abox ab conjc_rule)"
apply (clarsimp simp add: saturated_abox_def conjc_rule_def ex_rule_closure_def)
apply (clarsimp simp add: conjc_rule_indiv.simps)
apply (rename_tac x c1 c2)

apply (case_tac "FactFm (Inst x c1) \<in> rename_in_abox ab sbsts")
apply simp
   apply (clarsimp simp add: rename_in_abox_inversion)
   apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)
   apply (simp add: schlubs1 schlubs2)
   apply (simp add: conjc_applicable.simps)
   apply (intro conjI exI)
   apply assumption
   apply clarsimp
   
apply simp
   apply (clarsimp simp add: rename_in_abox_inversion)
   apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
   apply (simp add: schlubs1 schlubs2)
   apply (simp add: conjc_applicable.simps)
   apply (intro conjI exI)
   apply assumption
   apply clarsimp
done

lemma "\<not> (saturated_abox (rename_in_abox ab sbsts) disjc_rule) 
   \<Longrightarrow> \<not> (saturated_abox ab disjc_rule)"
apply (clarsimp simp add: saturated_abox_def disjc_rule_def ex_rule_closure_def)
apply (clarsimp simp add: disjc_rule_indiv.simps)
apply (rename_tac ab2 x c1 c2)
   apply (clarsimp simp add: rename_in_abox_inversion)
   apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
   apply (simp add: schlubs1 schlubs2)
   apply (simp add: disjc_applicable.simps)
   apply (intro conjI exI)
   apply assumption
   apply clarsimp
   apply clarsimp
   apply blast
done



lemma extract_subst_Some_rename_in_fact: "extract_subst fct = Some a \<Longrightarrow>
  \<exists> x c sb. a = (x, c, sb) \<and> 
       (extract_subst (rename_in_fact fct rens) = 
           Some (rename_in_var x rens, rename_in_concept c rens, rename_in_subst sb rens))"
by (case_tac a) (simp add: extract_subst_Some)

lemma "\<not> (saturated_abox (rename_in_abox ab sbsts) substfm_rule) 
   \<Longrightarrow> \<not> (saturated_abox ab substfm_rule)"
apply (clarsimp simp add: saturated_abox_def substfm_rule_def ex_rule_closure_def)
apply (clarsimp simp add: substfm_rule_indiv.simps)
apply (rename_tac fm sb)
   apply (clarsimp simp add: rename_in_abox_inversion)
   apply (clarsimp simp add: rename_in_form_inversion_SubstFm)
   apply (simp add: substfm_applicable.simps)
apply (intro exI conjI)
apply (rule refl)
apply assumption
apply (simp  add: rename_in_form_push_subst_form)
done

   
(* The following does not hold, take abox with:    x1 : ([<] n r c), (x2 r y), x1 == x2
   where the choose rule is blocked, but becomes applicable after the substitution x1 := x2
lemma "\<not> (saturated_abox (rename_in_abox ab sbsts) choose_rule) 
   \<Longrightarrow> \<not> (saturated_abox ab choose_rule)"
*)

(*------------------------------------------------------*)


(*
lemma eq_applicable_progress: "eq_applicable f ab \<Longrightarrow> progress_with eq_rule ab"
apply (clarsimp simp add: progress_with_def eq_rule_def ex_rule_closure_def 
  eq_rule_indiv.simps eq_applicable.simps)
apply (intro exI conjI)
prefer 4
apply (rule refl)
defer
apply assumption+
apply clarsimp
sorry  -- in comment

lemma rexhaust_eq_applicable: 
   "rexhaust eq_rule ab1 ab2 \<Longrightarrow> \<not> (\<exists> f \<in> ab2. eq_applicable f ab2)"
apply (clarsimp simp add: rexhaust_def)
apply (subgoal_tac "\<not> eq_applicable (FactFm (Eq True x y)) ab2") 
  prefer 2 apply (intro notI) apply (drule eq_applicable_progress, simp)
apply (clarsimp simp add: eq_applicable.simps)
done
*)
(* still better than the two above: *)



lemma saturated_no_progress: "saturated_abox ab r \<Longrightarrow> \<not> progress_with r ab"
by (clarsimp simp add: progress_with_def saturated_abox_def)

lemma no_progress_saturated: 
  "\<not> progress_with r ab \<Longrightarrow> induces_change r ab \<Longrightarrow> saturated_abox ab r"
by (fastforce simp add: progress_with_def saturated_abox_def induces_change_def)




(*------------------------------------------------------*)


(* TODO: instead of a ... set, maybe only use a boolean *)
type_synonym ('nr, 'nc, 'ni) appcond_set = "(('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool) set"

(* TODO: active_set and active really needed ? *)
definition active_set :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> ('nr, 'nc, 'ni) appcond_set \<Rightarrow> bool" where
   "active_set f ab appcs = (\<exists> appc \<in> appcs. appc f ab)"

definition active :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) appcond_indiv \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
   "active f appc ab = (f \<in> ab \<and> appc f ab)"
   
definition blocked :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) appcond_indiv \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
   "blocked f appc ab = (f \<in> ab \<and> \<not> appc f ab)"

definition invariant :: "(('nr, 'nc, 'ni) abox \<Rightarrow> bool) \<Rightarrow> ('nr, 'nc, 'ni) rule => bool" where
  "invariant P rl = (\<forall> ab ab'. (P ab) \<longrightarrow> rl ab ab' \<longrightarrow> (P ab'))"

definition cumulative_rule :: "('nr, 'nc, 'ni) rule => bool" where
  "cumulative_rule rl = (\<forall> ab ab'. rl ab ab' \<longrightarrow> ab \<subseteq> ab')"

definition appcond_decreasing :: "('nr, 'nc, 'ni) appcond_indiv \<Rightarrow> bool" where
  "appcond_decreasing appc = (\<forall> f ab ab'. ab \<subseteq> ab' \<longrightarrow> f \<in> ab \<longrightarrow> appc f ab' \<longrightarrow> appc f ab)"

lemma invariant_alternative_rule: 
"invariant P r1 \<Longrightarrow>  invariant P r2 \<Longrightarrow> invariant P (alternative_rule r1 r2)"
apply (simp add: alternative_rule_def )
apply (unfold invariant_def)
apply blast
done

lemma invariant_relcompp:
"invariant P r1 \<Longrightarrow>  invariant P r2 \<Longrightarrow> invariant P (r1 OO r2)"
apply (unfold invariant_def)
apply clarify
apply blast
done


lemma blocked_alternative_appcond:
  "blocked f (alternative_appcond appc1 appc2) ab = (blocked f appc1 ab \<and> blocked f appc2 ab)"
by (fastforce simp add: alternative_appcond_def blocked_def)


lemma invariant_alternative_rule_of_set:
  "Ball S (invariant P) \<Longrightarrow> invariant P (alternative_rule_of_set S)"
by (clarsimp simp add: alternative_rule_of_set_def invariant_def)

(* properties of cumulative *)
lemma cumulative_rule_empty_rule [simp]: "cumulative_rule empty_rule"
by (fastforce simp add: cumulative_rule_def empty_rule_def)

lemma cumulative_rule_alternative_rule [simp]:
  "cumulative_rule r1 \<Longrightarrow> cumulative_rule r2 \<Longrightarrow> cumulative_rule (alternative_rule r1 r2)"
by (fastforce simp add: cumulative_rule_def alternative_rule_def)

lemma cumulative_rule_sound: "cumulative_rule rl \<Longrightarrow> sound TYPE('d) rl"
by (fastforce simp add: cumulative_rule_def sound_def satisfiable_def)

(* properties of appcond_decreasing *)

lemma invariant_blocked: 
  "cumulative_rule rl \<Longrightarrow> appcond_decreasing appc \<Longrightarrow> invariant (blocked f appc) rl"
apply (simp add: cumulative_rule_def appcond_decreasing_def)
apply (clarsimp simp add: invariant_def)
apply (clarsimp simp add: blocked_def active_def)
apply blast
done

(* cumulativity: specific rules *)
lemma cumulative_rule_conjc_rule [simp]: "cumulative_rule conjc_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def conjc_rule_def conjc_rule_indiv.simps)
lemma cumulative_rule_disjc_rule [simp]: "cumulative_rule disjc_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def disjc_rule_def disjc_rule_indiv.simps)
lemma cumulative_rule_substc_rule [simp]: "cumulative_rule substc_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def substc_rule_def substc_rule_indiv.simps)
lemma cumulative_rule_conjfm_rule [simp]: "cumulative_rule conjfm_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def conjfm_rule_def conjfm_rule_indiv.simps)
lemma cumulative_rule_disjfm_rule [simp]: "cumulative_rule disjfm_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def disjfm_rule_def disjfm_rule_indiv.simps)
lemma cumulative_rule_substfm_rule [simp]: "cumulative_rule substfm_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def substfm_rule_def substfm_rule_indiv.simps)
lemma cumulative_rule_choose_rule [simp]: "cumulative_rule choose_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def choose_rule_def choose_rule_indiv.simps)
lemma cumulative_rule_numrestrc_ge_rule [simp]: "cumulative_rule numrestrc_ge_rule"
by (fastforce simp add: cumulative_rule_def ex_rule_closure_def numrestrc_ge_rule_def numrestrc_ge_rule_indiv.simps)


(* appcond_decreasing: specific rules *)
lemma appcond_decreasing_conjc_applicable [simp]: "appcond_decreasing conjc_applicable"
by (fastforce simp add: appcond_decreasing_def conjc_applicable.simps)
lemma appcond_decreasing_disjc_applicable [simp]: "appcond_decreasing disjc_applicable"
by (fastforce simp add: appcond_decreasing_def disjc_applicable.simps)
lemma appcond_decreasing_substc_applicable [simp]: "appcond_decreasing substc_applicable"
by (fastforce simp add: appcond_decreasing_def substc_applicable.simps)
(* TODO: does not work immediately
lemma appcond_decreasing_choose_applicable [simp]: "appcond_decreasing choose_applicable"
by (fastforce simp add: appcond_decreasing_def choose_applicable.simps)
lemma appcond_decreasing_numrestrc_lt_applicable [simp]: 
    "appcond_decreasing numrestrc_lt_applicable_to_form"
apply (clarsimp simp add: appcond_decreasing_def numrestrc_lt_applicable_to_form_def numrestrc_lt_applicable.simps)
apply (intro conjI exI)
apply (rule refl)
apply assumption
apply (intro conjI ballI)
apply fast
done
*)

(*
lemma appcond_decreasing_numrestrc_ge_applicable [simp]: "appcond_decreasing numrestrc_ge_applicable"
by (fastforce simp add: appcond_decreasing_def numrestrc_ge_applicable.simps)
*)
lemma appcond_decreasing_eq_applicable [simp]: "appcond_decreasing eq_applicable"
by (fastforce simp add: appcond_decreasing_def eq_applicable.simps)
lemma appcond_decreasing_conjfm_applicable [simp]: "appcond_decreasing conjfm_applicable"
by (fastforce simp add: appcond_decreasing_def conjfm_applicable.simps)
lemma appcond_decreasing_disjfm_applicable [simp]: "appcond_decreasing disjfm_applicable"
by (fastforce simp add: appcond_decreasing_def disjfm_applicable.simps)
lemma appcond_decreasing_substfm_applicable [simp]: "appcond_decreasing substfm_applicable"
by (fastforce simp add: appcond_decreasing_def substfm_applicable.simps)

(* TODO: by means of example; can probably be deleted *)
lemma "invariant (blocked f conjc_applicable) conjc_rule"
by (simp add: invariant_blocked)

fun elementary_form :: "('nr, 'nc, 'ni) form \<Rightarrow> bool" where
  "elementary_form (ConstFm cn) = True"
| "elementary_form (FactFm f) = True"
| "elementary_form _ = False"

definition all_applicable_elementary :: "('nr, 'nc, 'ni) appcond_indiv \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
"all_applicable_elementary appc ab = (\<forall> f \<in> ab. appc f ab \<longrightarrow> elementary_form f)"

definition set_concept_appconds ::"(('nr, 'nc, 'ni::linorder) appcond_indiv) set" where  
  "set_concept_appconds =  
  {conjc_applicable, disjc_applicable, substc_applicable, 
  choose_applicable, numrestrc_ge_applicable }"

definition set_concept_rules ::"(('nr, 'nc, 'ni::linorder) rule) set" where  
  "set_concept_rules =  
  {conjc_rule, disjc_rule, choose_rule, numrestrc_ge_rule }"

definition "concept_rule = (alternative_rule_of_set set_concept_rules)"

(* give rise to renaming substitutions, hence the name
  definition set_renaming_appconds ::"(('nr, 'nc, 'ni) appcond_indiv) set" where  
  "set_renaming_appconds =  {eq_applicable, numrestrc_lt_applicable_to_form}"

  
  definition set_alc_core_appconds ::"(('nr, 'nc, 'ni) appcond_indiv) set" where  
  "set_alc_core_appconds =  
  {conjc_applicable, disjc_applicable, substc_applicable, eq_applicable, 
  conjfm_applicable, disjfm_applicable, substfm_applicable, choose_applicable, 
  numrestrc_ge_applicable, numrestrc_lt_applicable_to_form}"

definition "alc_core_appcond = (alternative_appcond_of_set set_alc_core_appconds)"
 *)
 
lemma all_applicable_elementary_alternative_appcond [simp]:
 "all_applicable_elementary (alternative_appcond appc1 appc2) ab = 
  (all_applicable_elementary appc1 ab \<and> all_applicable_elementary appc2 ab)"
by (fastforce simp add: all_applicable_elementary_def alternative_appcond_def)

lemma alternative_appcond_of_set_union:
  "(alternative_appcond_of_set (S1 \<union> S2)) = 
  alternative_appcond (alternative_appcond_of_set S1) (alternative_appcond_of_set S2)"
by (clarsimp simp add:  alternative_appcond_of_set_def alternative_appcond_def fun_eq_iff)
blast

lemma inv_all_appl_elem_alt_union: 
  "(invariant (all_applicable_elementary (alternative_appcond_of_set S1)) r \<and> 
    invariant (all_applicable_elementary (alternative_appcond_of_set S2)) r)
 \<Longrightarrow> invariant (all_applicable_elementary (alternative_appcond_of_set (S1 \<union> S2))) r"
by (simp add: alternative_appcond_of_set_union) (clarsimp simp add: invariant_def)

lemma inv_all_appl_elem_alternative:
"\<forall> appc \<in> S. invariant (all_applicable_elementary appc) r
\<Longrightarrow> invariant (all_applicable_elementary (alternative_appcond_of_set S)) r"
by (fastforce simp add: invariant_def all_applicable_elementary_def alternative_appcond_of_set_def)

definition "new_in_rule_app r P = (\<forall> ab ab'. (r ab ab') \<longrightarrow> (\<forall> f \<in> (ab' - ab). (P f)))"  

lemma invariant_all_applicable_elementary_reduction:
   "cumulative_rule rl \<Longrightarrow> appcond_decreasing appc 
   \<Longrightarrow> new_in_rule_app rl elementary_form 
   \<Longrightarrow> invariant (all_applicable_elementary appc) rl"
apply (clarsimp simp add: invariant_def all_applicable_elementary_def cumulative_rule_def)
apply (simp add: appcond_decreasing_def)
apply (subgoal_tac "ab \<subseteq> ab'") prefer 2 apply blast
apply (case_tac "f \<in> ab")
apply blast
apply (simp add: new_in_rule_app_def)
done

lemma new_in_rule_app_conjc_rule [simp]: "new_in_rule_app conjc_rule elementary_form"
by (fastforce simp add: new_in_rule_app_def conjc_rule_def 
  ex_rule_closure_def conjc_rule_indiv.simps)
lemma new_in_rule_app_disjc_rule [simp]: "new_in_rule_app disjc_rule elementary_form"
by (fastforce simp add: new_in_rule_app_def disjc_rule_def 
  ex_rule_closure_def disjc_rule_indiv.simps)
lemma new_in_rule_app_choose_rule [simp]: "new_in_rule_app choose_rule elementary_form"
by (fastforce simp add: new_in_rule_app_def choose_rule_def 
  ex_rule_closure_def choose_rule_indiv.simps)
lemma new_in_rule_app_numrestrc_ge_rule [simp]: "new_in_rule_app numrestrc_ge_rule elementary_form"
by (clarsimp simp add: new_in_rule_app_def numrestrc_ge_rule_def 
  ex_rule_closure_def numrestrc_ge_rule_indiv.simps)
 (fastforce simp add: numrestrc_ge_rule_facts_def)

 (*
lemma invariant_all_app_elem_choose:
"invariant (all_applicable_elementary choose_applicable) rl"
by (clarsimp simp add: invariant_def all_applicable_elementary_def)
*)
lemma invariant_all_app_elem_numrestrc_lt_applicable_to_form:
"invariant (all_applicable_elementary numrestrc_lt_applicable_to_form) rl"
apply (clarsimp simp add: invariant_def all_applicable_elementary_def cumulative_rule_def)
apply (clarsimp simp add: numrestrc_lt_applicable_to_form_def)
done

(*
lemma invariant_all_app_elem_concept_rule:
   "invariant (all_applicable_elementary alc_core_appcond) concept_rule"
apply (simp add: alc_core_appcond_def concept_rule_def)
apply (rule inv_all_appl_elem_alternative)
apply (rule ballI)
apply (rule invariant_alternative_rule_of_set)
apply (rule ballI)
apply (simp add: set_alc_core_appconds_def set_concept_rules_def)
apply (elim disjE)
apply (simp_all add: 
  invariant_all_applicable_elementary_reduction 
  invariant_all_app_elem_choose invariant_all_app_elem_numrestrc_lt_applicable_to_form)
done
*)
lemma elementary_form_rename_in_form [rule_format, simp]:
  "elementary_form fm \<longrightarrow> elementary_form (rename_in_form fm sbsts)"
by (induct fm) auto

(*
lemma invariant_all_app_elem_numrestrc_lt_rule_general:
   "\<forall> fm ab sbsts. \<not> elementary_form fm \<longrightarrow> appc (rename_in_form fm sbsts) (rename_in_abox ab sbsts) \<longrightarrow> appc fm ab
   \<Longrightarrow> invariant (all_applicable_elementary appc) numrestrc_lt_rule"
apply (clarsimp simp add: invariant_def all_applicable_elementary_def)
apply (clarsimp simp add: numrestrc_lt_rule_def ex_rule_closure_def numrestrc_lt_rule_indiv.simps)
apply (rule elementary_form_rename_in_form)
apply (drule_tac x=fa in spec)
apply (fastforce simp add: rename_in_abox_def)
done

lemma invariant_all_app_elem_numrestrc_lt_rule_general:
   "invariant (all_applicable_elementary alc_core_appcond) numrestrc_lt_rule"
apply (simp add: alc_core_appcond_def)
apply (rule inv_all_appl_elem_alternative)
apply (rule ballI)
apply (simp add: set_alc_core_appconds_def)
apply (elim disjE)
apply (simp_all)

apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  

apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  

apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
 
apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  


(* conjfm *)
apply (clarsimp simp add: invariant_def all_applicable_elementary_def)
apply (clarsimp simp add:   numrestrc_lt_rule_def ex_rule_closure_def numrestrc_lt_rule_indiv.simps)

(* disjfm *)
(*
apply (clarsimp simp add: invariant_def all_applicable_elementary_def 
  numrestrc_lt_rule_def ex_rule_closure_def numrestrc_lt_rule_indiv.simps)
*)

apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: disjfm_applicable.simps)
apply (rename_tac fm ab sbsts f1' f2')
apply (subgoal_tac "(\<exists> f1 f2. (fm = DisjFm f1 f2) \<and> 
      f1' = rename_in_form f1 sbsts \<and> f2' = rename_in_form f2 sbsts)"

apply (case_tac fm)
apply simp
apply simp
apply simp
apply clarsimp

apply (simp add: rename_in_form_inversion_BinopFm)
apply (elim exE conjE)
apply simp
apply (simp add: rename_in_abox_inversion)
apply (drule sym)
apply clarsimp
apply (drule sym)
apply (simp add: rename_in_form_inversion_BinopFm)
apply clarsimp
apply (clarsimp simp add: rename_in_abox_inversion)





apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: conjfm_applicable.simps)

apply (subgoal_tac "\<exists> f1' f2'. (ConjFm f1' f2') = fm \<and> fm \<in> ab \<and> 
   f1 = rename_in_form f1' sbsts \<and> f2 = rename_in_form f2' sbsts")
   prefer 2
   apply (clarsimp simp add: rename_in_abox_inversion)
   apply (clarsimp simp add: rename_in_form_inversion_BinopFm rename_in_fact_inversion_Inst)
   apply blast
   apply clarsimp
   apply (intro conjI exI) prefer 2
   apply clarsimp
apply (clarsimp simp add: rename_in_form_inversion_BinopFm rename_in_fact_inversion_Inst)

apply (case_tac "rename_in_form f1a sbsts \<in> rename_in_abox ab sbsts")
   apply (clarsimp simp add: rename_in_abox_inversion) 
apply (clarsimp simp add: rename_in_form_inversion_BinopFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  

apply (simp add: schlubs1 schlubs2)
defer
defer
apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
 
apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
 
apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
 

apply (rule invariant_all_app_elem_numrestrc_lt_rule_general)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst rename_in_concept_inversion_BinopC)  
 
   
   apply (clarsimp simp add: conjc_applicable.simps)
*)

end
