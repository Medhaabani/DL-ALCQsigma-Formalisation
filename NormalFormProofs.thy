(*<*)
theory NormalFormProofs imports NormalForm SemanticsProofs VariablesProofs
begin
(*>*)

section {* Normal Forms (Proofs) *}

lemma is_neg_norm_concept_neg_norm_concept [rule_format,simp]: 
  "\<forall> sign. is_neg_norm_concept (neg_norm_concept sign c)"
by (induct c) auto

lemma is_neg_norm_fact_neg_norm_fact [simp]: "is_neg_norm_fact (neg_norm_fact sign f)"
  by (case_tac f) auto

lemma is_neg_norm_form_neg_norm_form [simp]: "\<forall> sign. (is_neg_norm_form (neg_norm_form sign f))"
  by (induct f) auto

lemma is_neg_norm_form_nnf_IfThenElseFm [simp]: "is_neg_norm_form (nnf_IfThenElseFm c a b)"
by (simp add: nnf_IfThenElseFm_def)

lemma neg_norm_concept_is_neg_norm_concept : "is_neg_norm_concept  c \<Longrightarrow> neg_norm_concept True c = c"
by (induct c) simp_all

lemma neg_norm_form_is_neg_norm_form :" is_neg_norm_form  f \<Longrightarrow> neg_norm_form True f = f  "
  apply (induct f)
  apply simp_all
  apply (rename_tac fact)
  apply (case_tac fact)
  apply (simp add: neg_norm_concept_is_neg_norm_concept )
  apply simp+
done

lemma neg_norm_concept_idem [rule_format, simp] :
   "(\<forall> b1 b2. (neg_norm_concept b1 (neg_norm_concept b2 c) = neg_norm_concept (b1 = b2) c))"
by (induct c) auto

lemma neg_norm_fact_idem [rule_format, simp] :
   "(\<forall> b1 b2. (neg_norm_fact b1 (neg_norm_fact b2 f) = neg_norm_fact (b1 = b2) f))"
by (induct f) auto

lemma neg_norm_form_idem [rule_format, simp] :
   "(\<forall> b1 b2. (neg_norm_form b1 (neg_norm_form b2 f) = neg_norm_form (b1 = b2) f))"
by (induct f) auto


lemma neg_norm_concept_inj [rule_format, simp]:
  "\<forall> b1 b2. (neg_norm_concept b1 c = neg_norm_concept b2 c) = (b1 = b2)"
by (induct c) simp_all

lemma neg_norm_fact_inj [rule_format, simp]:
  "\<forall> b1 b2. (neg_norm_fact b1 f = neg_norm_fact b2 f) = (b1 = b2)"
by (induct f) simp_all

lemma neg_norm_form_inj [rule_format, simp]:
  "\<forall> b1 b2. (neg_norm_form b1 f = neg_norm_form b2 f) = (b1 = b2)"
by (induct f) simp_all

(* Normal forms and variables *)

lemma fv_concept_neg_norm_concept [rule_format, simp]: 
  "\<forall> b. fv_concept (neg_norm_concept b c) = fv_concept c"
by (induct c) auto

lemma fv_concept_sub_concepts_neg_norm_concept [rule_format, simp]:
  "\<forall> b. (\<Union>i\<in>sub_concepts (neg_norm_concept b c). fv_concept i) = fv_concept c"
by (induct c) auto

lemma sub_concepts_pn_neg_norm_concept [rule_format, simp]:
  "\<forall> b. sub_concepts_pn (neg_norm_concept b c) \<subseteq> sub_concepts_pn c"
apply (induct c)
apply (auto simp add: Let_def)
apply fastforce+
done

lemma neg_norm_concept_sub_concepts_pn [rule_format, simp]:
   "\<forall> b. neg_norm_concept b c \<in> sub_concepts_pn c"
apply (induct c)
apply (auto simp add: Let_def)
apply fastforce+
done


(* ----------------------------------------- *)
(* Preservation of interpretations under nnf *)
(* ----------------------------------------- *)

(* TODO: move elsewhere ? *)
lemma well_formed_interp_interp_concept_subset_interp_d [rule_format, simp]:
  "\<forall> i. well_formed_interp i \<longrightarrow> interp_concept c i \<subseteq> interp_d i"
apply (induct c)
apply simp_all
apply (fastforce simp add: well_formed_interp_def)
apply fastforce
apply (rename_tac bop c1 c2) apply (case_tac bop) 
apply fastforce+
apply (intro allI impI) apply (drule spec, drule mp) prefer 2 apply (rule subset_trans) apply assumption apply simp+
apply fastforce+
done

(* Note: proof of this lemma takes very much time *)
(* TODO: include the proof itself *)
lemma well_formed_interp_interp_i_modif_interp_c [simp]:
  "well_formed_interp i \<Longrightarrow> xi \<in> interp_concept c i \<Longrightarrow> 
   well_formed_interp (interp_i_modif x xi i)"
sorry (* long runtime*)
(*
by (frule well_formed_interp_interp_concept_subset_interp_d)
   (fastforce simp add: well_formed_interp_def interp_i_modif_def)
*)

lemma well_formed_interp_i_double_interp_d_minus [simp]: 
"well_formed_interp i \<Longrightarrow> interp_d i - (interp_d i - interp_concept c i) = interp_concept c i"
by (blast dest: well_formed_interp_interp_concept_subset_interp_d)


lemma interp_fact_neg_norm_concept [rule_format, simp]:
  "\<forall> sign i. well_formed_interp i \<longrightarrow> 
  interp_concept (neg_norm_concept sign c) i = 
  (if sign then (interp_concept c i) else (interp_d i -  (interp_concept c i)))"
  apply (induct c)
  apply simp
  apply simp
  apply (simp add: well_formed_interp_def) apply blast
  apply simp_all
  
  apply (rename_tac binop c1 c2)
  apply (case_tac binop)
  apply simp apply blast
  apply simp apply blast
  
  apply (rename_tac numres_ord n nr c)
  apply (case_tac numres_ord)
  apply (clarsimp simp add: set_eq_iff)+
done

lemma interp_fact_neg_norm_fact [rule_format, simp]:
  "\<forall> sign i.  well_formed_interp i \<longrightarrow> interp_fact (neg_norm_fact sign f) i = (interp_sign sign (interp_fact f i))"
by (induct f) simp_all

lemma interp_form_neg_norm_form [rule_format, simp]:
  "\<forall> sign i. well_formed_interp i \<longrightarrow> 
  interp_form (neg_norm_form sign f) i = (interp_sign sign (interp_form f i))"
  apply (induct f)
  apply simp_all
  apply (rename_tac binop f1 f2)
  apply (case_tac binop)
  apply simp_all
done

lemma interp_form_nnf_IfThenElseFm [simp]: 
   "well_formed_interp i \<Longrightarrow> interp_form (nnf_IfThenElseFm c a b) i = interp_form (IfThenElseFm c a b) i"
by (simp add: nnf_IfThenElseFm_def)

(*<*)
end
(*>*)
