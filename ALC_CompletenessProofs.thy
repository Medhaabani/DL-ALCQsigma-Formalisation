(*<*)
theory ALC_CompletenessProofs imports ALC_SoundnessProofs
begin
(*>*)

section {* Completeness of Tableau Calculus *}


definition saturated_abox :: "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> bool" where
  "saturated_abox ab1 r \<equiv> \<forall> ab2. \<not> r ab1 ab2"

  (* Apply rule to abox if possible, otherwise keep abox 
 TODO: is that notion really needed? *)
definition conserv_appl :: "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> ('ni,'nr,'nc) abox set" where
 "conserv_appl ab1 r = (if saturated_abox ab1 r then {ab1} else  {ab2. r ab1 ab2})" 
 
  (* complete means: no loss of models *)
definition complete ::"('nr, 'nc, 'ni) rule \<Rightarrow> bool" where 
  "complete r \<equiv> \<forall> a1. satisfiable TYPE('d) a1 \<longrightarrow> \<not> (saturated_abox a1 r) 
  \<longrightarrow>  (\<exists> a2. r a1 a2 \<and> satisfiable TYPE('d) a2)"

definition fully_complete ::"('nr, 'nc, 'ni) rule \<Rightarrow> bool" where 
  "fully_complete r \<equiv> \<forall> a1. satisfiable TYPE('d) a1 
  \<longrightarrow>  (\<forall> a2. r a1 a2 \<longrightarrow> satisfiable TYPE('d) a2)"

lemma "fully_complete TYPE('d) r \<Longrightarrow> complete TYPE('d) r"
by (fastforce simp add: fully_complete_def complete_def saturated_abox_def)


  (*----------------------------------------------------------------------------------------*)

definition completeness_pres_weakening :: "('nr,'nc,'ni) rule \<Rightarrow> ('nr,'nc,'ni) rule \<Rightarrow> bool" where
"completeness_pres_weakening r r_weak = 
  (\<forall> ab. (((Collect (r ab)) = (Collect (r_weak ab))) \<or> saturated_abox ab r))"

lemma complete_weaken: "complete TYPE('d) r_weak
\<Longrightarrow> completeness_pres_weakening r r_weak 
\<Longrightarrow> complete TYPE('d) r"
  apply (clarsimp simp add: complete_def completeness_pres_weakening_def)
  apply (drule_tac x=a1 in spec, drule mp, assumption)
  apply (drule_tac x=a1 in spec)
  apply (clarsimp simp add: saturated_abox_def)
  apply blast
done

  (*----------------------------------------------------------------------------------------*)
  (* General properties of completeness *)

lemma complete_unsatisfiable: "complete TYPE('d) r 
\<Longrightarrow> \<not> (saturated_abox ab1 r)
\<Longrightarrow> \<forall> ab2 \<in> (Collect (r ab1)).  \<not> (satisfiable TYPE('d) ab2) 
\<Longrightarrow>  \<not> (satisfiable TYPE('d) ab1)"
by (fastforce simp add: complete_def)

lemma saturated_abox_weaken: "\<forall> ab. (Collect (r1 ab)) \<subseteq> (Collect (r2 ab))
\<Longrightarrow> \<not> saturated_abox ab r1 \<longrightarrow> \<not> saturated_abox ab r2"
by (fastforce simp add: saturated_abox_def)

lemma complete_ex_rule_closure [rule_format, simp]: 
"(\<forall> f. complete TYPE('d) (ir f)) \<Longrightarrow> complete TYPE('d) (ex_rule_closure ir)"
by (fastforce simp add: complete_def saturated_abox_def ex_rule_closure_def)

lemma fully_complete_ex_rule_closure [rule_format, simp]: 
"(\<forall> f. fully_complete TYPE('d) (ir f)) \<Longrightarrow> fully_complete TYPE('d) (ex_rule_closure ir)"
by (fastforce simp add: fully_complete_def ex_rule_closure_def)

(* TODO: continue using this lemma *)
lemma saturated_abox_alc_ruleD: "saturated_abox ab alc_rule \<Longrightarrow> r \<in> set_alc_rules \<Longrightarrow> saturated_abox ab r"
by (fastforce simp add: saturated_abox_def alc_rule_def set_alc_rules_def alternative_rule_of_set_def)

  (* ----------------------------------------------------------------------  *)
  (* Rule combinators *)

lemma empty_rule_complete [simp]: "complete TYPE('d) empty_rule"
by (simp add: complete_def saturated_abox_def empty_rule_def)

lemma alternative_rule_complete [simp]: 
"complete TYPE('d) r1 \<Longrightarrow> complete TYPE('d) r2 \<Longrightarrow> complete TYPE('d) (alternative_rule r1 r2)"
by (fastforce simp add: complete_def saturated_abox_def alternative_rule_def)

lemma alternative_rule_of_set_complete [simp]: 
"Ball rs (complete TYPE('d)) \<Longrightarrow> complete TYPE('d) (alternative_rule_of_set rs)"
by (fastforce simp add: complete_def saturated_abox_def alternative_rule_of_set_def)

(* a rule analogous to relcompp_rule_sound does not hold *)

lemma rtranclp_rule_complete_for_induct:
  "r\<^sup>*\<^sup>* a1 a2 \<Longrightarrow>
  satisfiable TYPE('d) a1 \<Longrightarrow>
  \<forall>a1. satisfiable TYPE('d) a1 \<longrightarrow>
            (\<exists>a3. r a1 a3) \<longrightarrow>
            (\<exists>a3. r a1 a3 \<and> satisfiable TYPE('d) a3) \<Longrightarrow>     
        \<exists>a2. r\<^sup>*\<^sup>* a1 a2 \<and> satisfiable TYPE('d) a2"
by (induct rule: rtranclp.induct) auto

lemma rtranclp_rule_complete [simp]: "complete TYPE('d) r \<Longrightarrow> complete TYPE('d) r\<^sup>*\<^sup>*"
  by (clarsimp simp add: complete_def saturated_abox_def rtranclp_rule_complete_for_induct)

lemma tranclp_rule_complete_for_induct:
  "r\<^sup>+\<^sup>+ a1 a2 \<Longrightarrow>
  satisfiable TYPE('d) a1 \<Longrightarrow>
  \<forall>a1. satisfiable TYPE('d) a1 \<longrightarrow>
            (\<exists>a3. r a1 a3) \<longrightarrow>
            (\<exists>a3. r a1 a3 \<and> satisfiable TYPE('d) a3) \<Longrightarrow>     
        \<exists>a2. r\<^sup>+\<^sup>+ a1 a2 \<and> satisfiable TYPE('d) a2"
by (induct rule: tranclp.induct) auto

lemma tranclp_rule_complete [simp]: "complete TYPE('d) r \<Longrightarrow> complete TYPE('d) r\<^sup>+\<^sup>+"
  by (clarsimp simp add: complete_def saturated_abox_def tranclp_rule_complete_for_induct)

  
  (*----------------------------------------------------------------------------------------*)
  (* Properties of specific rules *)

lemma conjc_rule_indiv_complete [simp]: "complete TYPE('d) (conjc_rule_indiv f)"
apply (clarsimp simp add: complete_def saturated_abox_def)
apply (erule conjc_rule_indiv_cases)
apply (clarsimp simp add: satisfiable_def)
apply (rule exI)
apply (intro conjI)
apply (rule mk_conjc_rule_indiv)
apply (rule refl)
apply (clarsimp simp add: satisfiable_def conjc_applicable.simps)
apply (rule refl)
apply (rule_tac x=i in exI)
apply (clarsimp simp add: satisfiable_def conjc_applicable.simps)
apply  (fastforce elim: conjc_rule_indiv_cases simp add: satisfiable_def)
done

(* TODO: much better than previous proof *)
lemma conjc_rule_indiv_fully_complete [simp]: "fully_complete TYPE('d) (conjc_rule_indiv f)"
apply (clarsimp simp add: fully_complete_def saturated_abox_def)
apply (erule conjc_rule_indiv_cases)
apply (fastforce simp add: satisfiable_def)
done

lemma disjc_rule_appcond: "disjc_rule_indiv f b1 b2 
  \<Longrightarrow>  \<exists> x c1 c2. f = (FactFm (Inst x (DisjC c1 c2))) \<and> (disjc_applicable f b1)"
  by (blast elim: disjc_rule_indiv_cases)

lemma disjc_rule_indiv_complete [simp]: "complete TYPE('d) (disjc_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (drule disjc_rule_appcond)
  apply clarsimp
  apply (frule bspec, assumption)
  apply simp
  apply (erule disjE)
  
  apply (intro exI conjI mk_disjc_rule_indiv) apply (rule refl)
  apply (rule App_disjc) apply (rule refl) apply assumption+
  apply (rule disjI1) apply (rule refl) apply assumption apply fastforce
  apply (intro exI conjI mk_disjc_rule_indiv) apply (rule refl)
  apply (rule App_disjc) apply (rule refl) apply assumption+
  apply (rule disjI2) apply (rule refl) apply assumption apply fastforce
done

lemma allc_rule_indiv_complete [simp]: "complete TYPE('d) (allc_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (rule exI)
  apply (rule conjI) 
  apply assumption
  apply (rule_tac x=i in  exI)
  apply clarsimp
  apply (erule allc_rule_indiv_cases)
  apply clarsimp
  apply (erule disjE)
  apply clarsimp
  apply (rename_tac a1 i x r c y y')
  apply (frule_tac x="FactFm (Inst x (AllC r c))" in bspec)
  apply assumption
  apply (simp only: interp_form.simps interp_fact.simps interp_concept_AllC)
  apply auto
done

 lemma interp_i_var_equivalent_notin_vars [simp]:
  "z \<notin> V \<Longrightarrow> interp_i_var_equivalent (interp_i_modif (Free z) zi i) i V"
  apply (unfold interp_i_var_equivalent_def)
  apply simp
  apply (simp add: interp_i_modif_def)
  done

lemma interp_i_equivalent_notin_vars [simp]:
  "z \<notin> V \<Longrightarrow> interp_i_equivalent (interp_i_modif z zi i) i V"
by (unfold interp_i_equivalent_def) (simp add: interp_i_modif_def)

lemma somec_rule_indiv_complete [simp]: "complete TYPE('d) (somec_rule_indiv (z,f))" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (rule exI)
  apply (rule conjI)
  apply assumption
  apply (erule somec_rule_indiv_cases)  
  apply clarsimp
  apply (rename_tac a1 i x r c)
  apply (subgoal_tac "interp_form (FactFm (Inst x (SomeC r c))) i") prefer 2 apply fast
  apply (simp del: interp_concept.simps add: interp_concept_SomeC)
  apply (clarsimp)
  apply (rename_tac a1 i x r c zi)
  apply (rule_tac x="interp_i_modif z zi i" in  exI)
  apply (clarsimp simp add:fv_abox_def)
  apply (subgoal_tac "z \<notin> fv_form (FactFm (Inst x (SomeC r c)))") prefer 2 apply fast 
  apply (subgoal_tac "interp_i_equivalent (interp_i_modif z zi i) i {x}") 
    prefer 2 apply (rule interp_i_equivalent_notin_vars) apply simp
  apply (intro conjI ballI)
  apply (simp only: interp_i_equivalent_interp_i)
  apply (subgoal_tac "interp_concept c (interp_i_modif z zi i) = interp_concept c i")  
  prefer 2 apply clarsimp apply (clarsimp simp add: interp_i_equivalent_interp_concept)
  apply (simp only:)
  apply (rename_tac a1 i x r c zi ff)
  apply (subgoal_tac "interp_form ff (interp_i_modif z zi i) = interp_form ff i")  
  prefer 2
  apply (rule interp_i_equivalent_interp_form)
  apply simp
  apply fastforce
done

lemma substc_rule_indiv_complete [simp]: "complete TYPE('d) (substc_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (rule exI,rule conjI, assumption)
  apply (intro exI conjI) apply assumption
  apply (clarsimp)
  apply (erule substc_rule_indiv_cases)
  apply (erule substc_applicable_cases)
  apply (clarsimp simp del: push_subst_form.simps)
  apply (elim disjE)
  apply (simp only: interp_form_push_subst_form)
  apply clarsimp
done

lemma substfm_rule_indiv_complete [simp]: "complete TYPE('d) (substfm_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (rule exI,rule conjI, assumption)
  apply (intro exI conjI) apply assumption
  apply (clarsimp)
  apply (erule substfm_rule_indiv_cases)
  apply (erule substfm_applicable_cases)
  apply (clarsimp simp del: push_subst_form.simps)
  apply (elim disjE)
  apply (simp only: interp_form_push_subst_form)
  apply clarsimp
done

lemma interp_form_rename_in_form: "well_formed_interp i
  \<Longrightarrow> interp_i i x = interp_i i y 
  \<Longrightarrow> interp_form (rename_in_form f [ISubst x y]) i = interp_form f i"
  apply (subgoal_tac "(interp_rename (ISubst x y) i) = i") 
    prefer 2 apply (simp add: interp_i_modif_def fun_eq_iff)
  apply (simp only: interp_form_rename_in_form_interp_rename_closure)
  apply simp
done

lemma eq_rule_indiv_complete [simp]: "complete TYPE('d) (eq_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (rule exI)
  apply (rule conjI)
  apply assumption
  apply (erule eq_rule_indiv_cases)
  apply (erule eq_applicable_cases)
  apply clarsimp 
  apply (rename_tac a1 i x y)
  apply (frule_tac x="FactFm (Eq True x y)" in bspec)
  apply clarsimp

  apply (intro conjI impI)
  apply (rule_tac x="interp_i_modif x (interp_i i y) i" in  exI)
  apply (simp add: rename_in_abox_def interp_form_rename_in_form)

  apply (rule_tac x="interp_i_modif x (interp_i i y) i" in  exI)
  apply (simp add: rename_in_abox_def interp_form_rename_in_form)
done


lemma eq_compl_rule_complete [simp]: "complete TYPE('d) eq_compl_rule"
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (elim eq_compl_rule_cases)
  apply (rename_tac a1 a2 i x y)
  apply (case_tac "interp_i i x = interp_i i y")
  
  apply (intro exI conjI mk_eq_compl_rule)
  prefer 5 apply (rule disjI2) apply (rule refl) apply assumption apply simp
  apply assumption+
  apply (simp add: rename_in_abox_def interp_form_rename_in_form)

  apply (intro exI conjI mk_eq_compl_rule)
  prefer 5 apply (rule disjI1) apply (rule refl) apply assumption apply simp
  apply assumption+
  apply (simp add: rename_in_abox_def interp_form_rename_in_form)
done

lemma conjfm_rule_indiv_complete [simp]: "complete TYPE('d) (conjfm_rule_indiv f)" 
  by (clarsimp simp add: complete_def saturated_abox_def)
     (fastforce elim: conjfm_rule_indiv_cases simp add: satisfiable_def)

lemma disjfm_rule_indiv_appcond: "disjfm_rule_indiv f b1 b2 
  \<Longrightarrow>  \<exists> f1 f2. f = (DisjFm f1 f2) \<and> (disjfm_applicable f b1)"
  by (erule disjfm_rule_indiv_cases) (fastforce intro: App_disjfm)


lemma disjfm_rule_indiv_complete [simp]: "complete TYPE('d) (disjfm_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (drule disjfm_rule_indiv_appcond)
  apply clarsimp
  apply (frule bspec, assumption)
  apply simp
  apply (blast intro: mk_disjfm_rule_indiv App_disjfm)
done

lemma choose_rule_complete [simp]: "complete TYPE('d) (choose_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (erule choose_rule_indiv_cases)
  apply clarsimp
  
  apply (case_tac  " interp_form (FactFm (Inst y c)) i")
  apply ( rule_tac  x= " insert (FactFm (Inst y c)) a1" in exI)
  apply (intro conjI)
  apply (rule mk_choose_rule) apply (rule refl)  apply assumption+
  apply clarsimp
  apply fastforce+
  apply ( rule_tac  x= " insert (FactFm (Inst y (neg_norm_concept False c))) a1" in exI)
  apply (intro conjI)
  apply (rule mk_choose_rule) apply (rule refl) apply assumption+
  apply fastforce+
done

(*
lemma choose_stable_rule_complete [simp]: "complete TYPE('d) (choose_stable_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (erule choose_stable_rule_indiv_cases)
  apply clarsimp
  apply (rename_tac b1 b2 i x n r c x' y)
  apply (case_tac "interp_form (FactFm (Inst y c)) i")
  apply (rule_tac  x= "insert (DisjFm (ConjFm (FactFm (Eq True x x')) (FactFm (Inst y c))) (FactFm (Eq False x x'))) b1" in exI)
  apply (intro conjI)
  apply (rule mk_choose_stable_rule) apply (rule refl) apply assumption+
  apply fastforce
  apply fastforce

  apply (rule_tac  x="insert (DisjFm (ConjFm (FactFm (Eq True x x')) (FactFm (Inst y (neg_norm_concept False c)))) (FactFm (Eq False x x'))) b1" in exI)
  apply (intro conjI)
  apply (rule mk_choose_stable_rule) apply (rule refl) apply assumption+
  apply fastforce
  apply fastforce
  done
*)

lemma choose_stable_rule_complete [simp]: "complete TYPE('d) (choose_stable_rule_indiv f)" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (erule choose_stable_rule_indiv_cases)
  apply clarsimp
  apply (rename_tac b1 b2 i x n r c x' y)
  (* case insert (FactFm (Eq False x x')) b1 *)
  apply (case_tac "interp_form (FactFm (Eq False x x')) i")
  apply (rule_tac  x= "insert (FactFm (Eq False x x')) b1" in exI)
  apply (intro conjI)
  apply (rule mk_choose_stable_rule) apply (rule refl) apply assumption+ apply simp apply fastforce
  
  apply (case_tac "interp_form (FactFm (Inst y c)) i")

  (* case insert (FactFm (Eq True x x')) (insert (FactFm (Inst y c)) b1) *)
  apply (rule_tac  x= "insert (FactFm (Eq True x x')) (insert (FactFm (Inst y c)) b1)" in exI)
  apply (intro conjI)
  apply (rule mk_choose_stable_rule) apply (rule refl) apply assumption+ apply simp apply fastforce
  
  
  (* case insert (FactFm (Eq True x x')) (insert (FactFm (Inst y (neg_norm_concept False c))) b1) *)
  apply (rule_tac x="insert (FactFm (Eq True x x')) (insert (FactFm (Inst y (neg_norm_concept False c))) b1)" in exI)  
  apply (intro conjI)
  apply (rule mk_choose_stable_rule) apply (rule refl) apply assumption+ apply simp  apply fastforce
  done
  

lemma finite_ge_card_eq_card_induct [rule_format]:  "\<forall> A . (n + i = card A) \<longrightarrow> finite A \<longrightarrow> (\<exists>A'\<subseteq>A. card A' = n)"
apply (induct i)
apply fastforce
apply clarsimp
apply (drule sym)
apply (drule card_eq_SucD)
apply clarsimp
apply (drule_tac x=B in spec)
apply auto
done

lemma finite_ge_card_eq_card: "finite A \<longrightarrow> n \<le> card A \<Longrightarrow> \<exists> A'. A' \<subseteq> A \<and> card A' = n"
apply (case_tac "finite A")
apply simp
apply (rule finite_ge_card_eq_card_induct [of n "(card A) - n" A])
apply arith
apply assumption
apply simp
apply (drule infinite_arbitrarily_large [of A n]) apply blast
done

lemma interp_concept_Numrestrc_Ge_impl:
  "x \<in> interp_concept ([\<ge>] n r c) i \<Longrightarrow>
  (\<exists>Yi. finite Yi \<and> (card Yi = n) \<and> (\<forall> y \<in> Yi. ((x,y) \<in>(interp_r i r) \<and> y \<in> (interp_concept c i))))"
apply (clarsimp simp add: card_ge_def)
apply (simp add: rel_restrict_def)
apply (case_tac "finite (Range (interp_r i r \<inter> {x} \<times> interp_concept c i))")
apply (drule finite_ge_card_eq_card)
apply clarsimp
apply (rule_tac x=A' in exI)
apply (fastforce dest: finite_subset)
apply (drule infinite_arbitrarily_large)
apply fastforce
done

lemma Numrestrc_Ge_interp_concept_impl: 
"x \<in> interp_d i 
\<Longrightarrow> \<exists>Yi. finite Yi \<and> (card Yi = n) \<and> (\<forall> y \<in> Yi. ((x,y) \<in>(interp_r i r) \<and> y \<in> (interp_concept c i)))
\<Longrightarrow> x \<in> interp_concept ([\<ge>] n r c) i"
apply (clarsimp simp add: card_ge_def)
apply (simp add: rel_restrict_def)
apply (erule card_mono)
apply blast
done

definition interp_i_override_on :: 
  "('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('ni \<Rightarrow> 'd) \<Rightarrow> 'ni set \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp" where
  "interp_i_override_on i h A = i\<lparr>interp_i := override_on (interp_i i) h A \<rparr>"

lemma interp_c_interp_i_override_on [simp]:
  "interp_c (interp_i_override_on i h Y) = interp_c i"
by (case_tac i) (simp add: interp_i_override_on_def)

lemma interp_r_interp_i_override_on [simp]:
  "interp_r (interp_i_override_on i h Y) = interp_r i"
by (case_tac i) (simp add: interp_i_override_on_def)

lemma interp_i_interp_i_override_on_in_set [simp]: 
"x \<notin> Y \<Longrightarrow> interp_i (interp_i_override_on i h Y) x = interp_i i x"
by (case_tac i) (simp add: interp_i_override_on_def)


lemma interp_i_interp_i_override_on_notin_set [simp]: 
"y \<in> Y \<Longrightarrow> interp_i (interp_i_override_on i h Y) y = h y"
by (case_tac i) (clarsimp simp add: interp_i_override_on_def) 

lemma bij_betw_transfer: "bij_betw h Y Yi \<Longrightarrow> y \<in> Y \<Longrightarrow>  (h y) \<in> Yi"
by (auto simp add: bij_betw_def)

lemma bij_betw_lt_unequal: "bij_betw h Y Yi \<Longrightarrow>
       (y1::'a::linorder) \<in> Y \<Longrightarrow>  y2 \<in> Y \<Longrightarrow> y1 < y2 \<Longrightarrow> h y1 \<noteq> h y2"
by (auto simp add: bij_betw_def inj_on_def)

lemma interp_concept_interp_i_override_on_fv [simp]:
  "fv_concept c \<inter> Y = {} \<Longrightarrow> 
    interp_concept c (interp_i_override_on i h Y) = interp_concept c i"
apply (rule interp_i_equivalent_interp_concept)
apply (clarsimp simp add: interp_i_equivalent_def)
apply (intro conjI)
apply (case_tac i)
apply  (simp add: interp_i_override_on_def)

apply (fastforce intro: interp_i_interp_i_override_on_in_set)
done

lemma interp_form_interp_i_override_on_fv [simp]:
  "fv_form f \<inter> Y = {} \<Longrightarrow> 
    interp_form f (interp_i_override_on i h Y) = interp_form f i"
apply (rule interp_i_equivalent_interp_form)
apply (clarsimp simp add: interp_i_equivalent_def)
apply (intro conjI)
apply (case_tac i)
apply  (simp add: interp_i_override_on_def)

apply (fastforce intro: interp_i_interp_i_override_on_in_set)
done

lemma well_formed_interp_interp_i_override: "well_formed_interp i \<Longrightarrow>
  \<forall>y\<in>Yi. (interp_i i x, y) \<in> interp_r i r \<and> y \<in> interp_concept c i \<Longrightarrow>
  bij_betw h Y Yi \<Longrightarrow>
  well_formed_interp (interp_i_override_on i h Y)"
  apply (subgoal_tac "Yi \<subseteq> interp_d i") 
    prefer 2 apply (blast dest: well_formed_interp_interp_concept_subset_interp_d)
apply (simp add: well_formed_interp_def interp_i_override_on_def)
by (metis bij_betw_transfer contra_subsetD override_on_apply_in override_on_apply_notin)

lemma numrestrc_ge_rule_indiv_complete[simp] : "complete TYPE('d) (numrestrc_ge_rule_indiv f)"
apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (rule exI,rule conjI, assumption)
  apply (erule  numrestrc_ge_rule_indiv_cases)
  apply (clarsimp simp add: numrestrc_ge_blocked_def)
  apply (case_tac "finite Y")
  apply (subgoal_tac "\<exists> z. z\<in> Y")
  prefer 2
  apply blast
  
  apply (clarsimp simp add: in_fresh_set_incr_notin_abox numrestrc_ge_rule_facts_def)
  apply (subgoal_tac "interp_form (FactFm (Inst x ([\<ge>] (card Y) r c))) i") 
  prefer 2 apply fast
  apply (simp del: interp_concept.simps)
  apply (drule interp_concept_Numrestrc_Ge_impl)
  apply (clarsimp simp add: numrestrc_ge_blocked_def)
  apply (rename_tac a1 i x r c Y z Yi)
  apply (subgoal_tac "\<exists> h. bij_betw h Y Yi") 
     prefer 2 apply (fastforce intro: finite_same_card_bij)
  apply clarsimp
  apply (rule_tac x="interp_i_override_on i h Y" in exI)

  apply (clarsimp simp add: well_formed_interp_interp_i_override)
  apply (subgoal_tac "x \<notin> Y") 
  prefer 2 apply (drule fresh_set_incr_fv_form, assumption) apply simp
  apply (elim disjE exE)
  apply (fastforce simp add: image_def dest: bij_betw_transfer)
  
  apply (subgoal_tac "fv_concept c \<inter> Y = {}")
     prefer 2 apply (drule fresh_set_incr_fv_form, assumption) apply simp
  apply (fastforce simp add: image_def dest: bij_betw_transfer)
  
  apply (clarsimp simp add: bij_betw_lt_unequal)
  
  apply (rename_tac a1 i x r c Y z Yi h ff)
  apply (subgoal_tac "fv_form ff \<inter> Y = {}") 
     prefer 2 apply (erule fresh_set_incr_fv_form, assumption)
  apply clarsimp
apply clarsimp
done

lemma interp_i_image_Fact: 
  "\<forall>f\<in>a1. interp_form f i \<Longrightarrow>
   \<forall>y\<in>S. FactFm (AtomR True r x y) \<in> a1 \<and> FactFm (Inst y c) \<in> a1 \<Longrightarrow>
   interp_i i ` S \<subseteq> {y. (interp_i i x, y) \<in> interp_r i r} \<inter> interp_concept c i"
by (clarsimp simp add: image_def subset_eq) fastforce

lemma card_ge_one: 
  "finite S \<Longrightarrow> y1 \<in> S \<Longrightarrow> y2 \<in> S \<Longrightarrow> y1 \<noteq> y2 \<Longrightarrow> 1 < card S"
apply (subgoal_tac "card {y1, y2} \<le> card S")
apply simp
apply (fast intro: card_mono)
done

(* ---------------- lt_rule_indiv ------------------------------------*)

lemma numrestrc_lt_rule_orig_indiv_move: 
  "\<forall>f\<in>a1. interp_form f i \<Longrightarrow>
   well_formed_interp i \<Longrightarrow> 
   interp_i (i::('d, 'nr, 'nc, 'ni) Interp) y1 = interp_i i y2 \<Longrightarrow>
   (y1::'ni::linorder) \<in> S \<Longrightarrow> y2 \<in> S \<Longrightarrow> finite S \<Longrightarrow>
   \<forall>y\<in>S. FactFm (AtomR True r x y) \<in> a1 \<and> FactFm (Inst y c) \<in> a1 \<Longrightarrow>
   FactFm (Inst x ([<] (card S) r c)) \<in> a1 \<Longrightarrow>
   y1 \<noteq> y2 \<Longrightarrow>
   \<exists>a2. numrestrc_lt_rule_orig_indiv (S, (FactFm (Inst x ([<] (card S) r c)))) a1 a2 \<and>
       (\<exists> (i::('d, 'nr, 'nc, 'ni) Interp). well_formed_interp i \<and> (\<forall>f\<in>a2. interp_form f i))"
apply (rule_tac x="if y1 < y2 then (rename_in_abox a1 [ISubst y2 y1])
     else (rename_in_abox a1 [ISubst y1 y2])" in exI)
apply (rule conjI)
apply (case_tac "y1 < y2")
apply simp

apply (rule mk_numrestrc_lt_rule_orig_indiv) apply (rule refl)
apply (rule App_numrestrc_lt)
prefer 8 apply assumption
apply ((rule refl)+, assumption+)+
apply (rule refl)
apply (rule card_ge_one) prefer 4 apply assumption+ 
apply (rule refl)

apply (subgoal_tac "y2 < y1") prefer 2 apply simp
apply (rule mk_numrestrc_lt_rule_orig_indiv) apply (rule refl)
apply (rule App_numrestrc_lt)
prefer 8 apply assumption
apply ((rule refl)+, assumption+)+
apply (rule refl)
apply (rule card_ge_one) prefer 4 apply assumption+ 
apply simp

apply (case_tac "y1 < y2") 
apply (fastforce simp add: interp_form_rename_in_form rename_in_abox_def)+ 
done


lemma numrestrc_lt_rule_orig_indiv_complete [simp]: "complete TYPE('d) (numrestrc_lt_rule_orig_indiv (S, f))"
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (erule numrestrc_lt_rule_orig_indiv_cases)
  apply clarsimp
  apply (rename_tac a1 i y1 y2 x r c) 
  apply (frule bspec) apply assumption
  apply simp
  apply (clarsimp simp add: card_lt_def rel_restrict_def Range_Image)
  apply (simp add: Image_def)
  
  apply (subgoal_tac "card (interp_i i ` S) \<le> card ({y. (interp_i i x, y) \<in> interp_r i r} \<inter> interp_concept c i)")
  prefer 2 
    apply (rule card_mono) apply assumption apply (rule interp_i_image_Fact) apply assumption+
  apply (subgoal_tac "card (interp_i i ` S) < card S") prefer 2 apply arith
  
  apply (drule pigeonhole)
  apply (clarsimp simp add: inj_on_def)
  apply (erule numrestrc_lt_rule_orig_indiv_move)
 
apply assumption+  apply (rule card_ge_0_finite) apply arith
apply assumption+
done 


(* ---------------- lt_rule_indiv ------------------------------------*)

lemma numrestrc_lt_rule_indiv_move: 
  "\<forall>f\<in>a1. interp_form f i \<Longrightarrow>
   well_formed_interp i \<Longrightarrow> 
   interp_i (i::('d, 'nr, 'nc, 'ni) Interp) y1 = interp_i i y2 \<Longrightarrow>
   (y1::'ni::linorder) \<in> S \<Longrightarrow> y2 \<in> S \<Longrightarrow> finite S \<Longrightarrow>
   \<forall>y\<in>S. FactFm (AtomR True r x y) \<in> a1 \<and> FactFm (Inst y c) \<in> a1 \<Longrightarrow>
   FactFm (Inst x ([<] (card S) r c)) \<in> a1 \<Longrightarrow>
   y1 \<noteq> y2 \<Longrightarrow>
   \<exists>a2. numrestrc_lt_rule_indiv (FactFm (Inst x ([<] (card S) r c))) a1 a2 \<and>
       (\<exists> (i::('d, 'nr, 'nc, 'ni) Interp). well_formed_interp i \<and> (\<forall>f\<in>a2. interp_form f i))"
apply (rule_tac x="if y1 < y2 then rename_in_abox a1 [ISubst y2 y1] 
     else (rename_in_abox a1 [ISubst y1 y2])" in exI)
apply (rule conjI)
apply (case_tac "y1 < y2")
apply simp

apply (rule mk_numrestrc_lt_rule_indiv) apply (rule refl)
apply (rule App_numrestrc_lt)
prefer 8 apply assumption
apply ((rule refl)+, assumption+)+
apply (rule refl)
apply (rule card_ge_one) prefer 4 apply assumption+ 
apply (rule refl)

apply (subgoal_tac "y2 < y1") prefer 2 apply simp
apply (rule mk_numrestrc_lt_rule_indiv) apply (rule refl)
apply (rule App_numrestrc_lt)
prefer 8 apply assumption
apply ((rule refl)+, assumption+)+
apply (rule refl)
apply (rule card_ge_one) prefer 4 apply assumption+ 
apply simp

apply (case_tac "y1 < y2")
apply (fastforce simp add: interp_form_rename_in_form rename_in_abox_def)+ 
done

lemma numrestrc_lt_rule_indiv_complete [simp]: "complete TYPE('d) (numrestrc_lt_rule_indiv f)"
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply (clarsimp simp add: satisfiable_def)
  apply (erule numrestrc_lt_rule_indiv_cases)
  apply clarsimp
  apply (rename_tac a1 i S y1 y2 x r c) 
  apply (frule bspec) apply assumption
  apply simp
  apply (clarsimp simp add: card_lt_def rel_restrict_def Range_Image)
  apply (simp add: Image_def)
  
  apply (subgoal_tac "card (interp_i i ` S) \<le> card ({y. (interp_i i x, y) \<in> interp_r i r} \<inter> interp_concept c i)")
  prefer 2 
    apply (rule card_mono) apply assumption apply (rule interp_i_image_Fact) apply assumption+
  apply (subgoal_tac "card (interp_i i ` S) < card S") prefer 2 apply arith
  
  apply (drule pigeonhole)
  apply (clarsimp simp add: inj_on_def)
  apply (erule numrestrc_lt_rule_indiv_move)
apply assumption+  apply (rule card_ge_0_finite) apply arith
apply assumption+
done


lemma somec_rule_complete [simp]: "complete TYPE('d) somec_rule"
apply (simp add: somec_rule_def)
apply (rule complete_ex_rule_closure)
apply (case_tac f)
apply simp
done

lemma numrestrc_lt_rule_orig_complete [simp]: "complete TYPE('d) numrestrc_lt_rule_orig"
apply (simp add: numrestrc_lt_rule_orig_def)
apply (rule complete_ex_rule_closure)
apply (case_tac f)
apply simp
done

lemma alc_rule_complete : "complete TYPE('d) alc_rule"
  apply (simp add: alc_rule_def set_alc_rules_def)
  apply (simp add: conjc_rule_def disjc_rule_def allc_rule_def substc_rule_def eq_rule_def
    conjfm_rule_def disjfm_rule_def choose_rule_def substfm_rule_def 
    numrestrc_ge_rule_def numrestrc_lt_rule_def)
done



(*---------------------------------------------------*)
(* TODO: the following lemmas show that soundness and completeness of the extended (tableau) rules 
can be reduced to soundness and completeness of the abox rules.

*)



lemma completeness_pres_weakening_numrestrc_ge: 
   "completeness_pres_weakening 
           (restrict_tableau_rule (numrestrc_ge_tableau_rule_indiv f)) 
           (numrestrc_ge_rule_indiv f) "
apply (clarsimp simp add: completeness_pres_weakening_def)
apply (clarsimp simp add: set_eq_iff)
apply (clarsimp simp add: restrict_tableau_rule_def)
apply (rule iffI)
apply (fastforce simp add: numrestrc_ge_tableau_rule_indiv.simps 
  numrestrc_ge_rule_indiv.simps numrestrc_ge_applicable.simps)
apply (clarsimp simp add: numrestrc_ge_tableau_rule_indiv.simps 
  numrestrc_ge_rule_indiv.simps numrestrc_ge_applicable.simps)
apply (rename_tac ab x r c Y)
apply (rule_tac x="\<lparr>abox = ab, varbounds = (\<lambda> v. {}) \<rparr>" in exI)
apply fastforce
done

lemma complete_restr_numrestrc_ge:
  "complete TYPE('d) (restrict_tableau_rule (numrestrc_ge_tableau_rule_indiv f))"
apply (rule complete_weaken)
apply (rule numrestrc_ge_rule_indiv_complete)
apply (rule completeness_pres_weakening_numrestrc_ge)
done

lemma soundness_pres_weakening_numrestrc_ge: 
   "soundness_pres_weakening 
           (restrict_tableau_rule (numrestrc_ge_tableau_rule_indiv f)) 
           (numrestrc_ge_rule_indiv f) "
apply (clarsimp simp add: soundness_pres_weakening_def)
apply (clarsimp simp add: restrict_tableau_rule_def)
apply (fastforce simp add: numrestrc_ge_tableau_rule_indiv.simps 
  numrestrc_ge_rule_indiv.simps numrestrc_ge_applicable.simps)
done

lemma sound_restr_numrestrc_ge:
  "sound TYPE('d) (restrict_tableau_rule (numrestrc_ge_tableau_rule_indiv f))"
apply (rule sound_weaken)
apply (rule numrestrc_ge_rule_indiv_sound)
apply (rule soundness_pres_weakening_numrestrc_ge)
done


lemma restrict_lift_to_tableau_rule [simp]: "(restrict_tableau_rule (lift_to_tableau_rule rl)) = rl"
apply (simp add: fun_eq_iff restrict_tableau_rule_def lift_to_tableau_rule_def)
apply clarsimp
apply (rename_tac ab1 ab2)
apply (rule iffI)
apply clarsimp
apply (rule_tac x="\<lparr>abox = ab1, varbounds = (\<lambda> v. {}) \<rparr>" in exI)
apply (rule_tac x="\<lparr>abox = ab2, varbounds = (\<lambda> v. {}) \<rparr>" in exI)
apply simp
done

lemma restrict_tableau_rule_alternative_rule:
    "restrict_tableau_rule (alternative_rule rl1 rl2) = 
       alternative_rule (restrict_tableau_rule rl1) (restrict_tableau_rule rl2)"
by (fastforce simp add: fun_eq_iff restrict_tableau_rule_def alternative_rule_def)

lemma restrict_tableau_rule_alternative_rule_of_set:
    "restrict_tableau_rule (alternative_rule_of_set rls) =
     alternative_rule_of_set (restrict_tableau_rule ` rls)"
by (fastforce simp add: fun_eq_iff restrict_tableau_rule_def alternative_rule_of_set_def)


(*<*)
end
(*>*)
