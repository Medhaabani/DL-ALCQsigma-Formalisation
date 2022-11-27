(*<*)
theory SubstProofs imports Subst NormalFormProofs
begin
(*>*)

section {* Explicit substitutions (Proofs)  \label{sec:subst_proofs} *}

  (* ----------------------------------------------------------------------  *)
subsection {* Functions used in termination arguments *}
  (* ----------------------------------------------------------------------  *)

fun subst_closure_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) subst list \<Rightarrow> ('nr, 'nc, 'ni) concept" where
    "subst_closure_concept c [] = c"
  | "subst_closure_concept c (sb # sbsts) = subst_closure_concept (SubstC c sb) sbsts"

fun subst_closure_form :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) subst list \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "subst_closure_form fm [] = fm"
  | "subst_closure_form fm (sb # sbsts) = subst_closure_form (SubstFm fm sb) sbsts"

fun subst_closure_qform :: "('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni var) subst list \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "subst_closure_qform fm [] = fm"
  | "subst_closure_qform fm (sb # sbsts) = subst_closure_qform (QSubstFm fm sb) sbsts"

fun rename_closure_qform :: "('nr, 'nc, 'ni) qform \<Rightarrow> 'ni var rename list \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "rename_closure_qform fm [] = fm"
  | "rename_closure_qform fm (sb # sbsts) = rename_closure_qform (QRenameFm fm sb) sbsts"

fun height_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> nat" where
    "height_concept Bottom = 1"
  | "height_concept Top = 1"
  | "height_concept (AtomC sign a) = 1"
  | "height_concept (BinopC bop c1 c2) = Suc (max (height_concept c1) (height_concept c2))"
  | "height_concept (NegC c) = Suc (height_concept c)"
  | "height_concept (NumRestrC nro n r c) = Suc (height_concept c)"
  | "height_concept (SubstC c sb) = Suc (height_concept c)"
  | "height_concept (SomeC r c) = Suc (height_concept c)"
  | "height_concept (AllC r c) = Suc (height_concept c)"

fun height_fact ::  "('nr, 'nc, 'ni) fact \<Rightarrow> nat" where
    "height_fact (Inst x c) = height_concept c"
  | "height_fact _  = 0"

fun height_form ::  "('nr, 'nc, 'ni) form \<Rightarrow> nat" where
    "height_form (ConstFm cn) = 0"
  | "height_form (FactFm fct) = Suc (height_fact fct)"
  | "height_form (NegFm f) = Suc (height_form f)"
  | "height_form (BinopFm bop f1 f2) = Suc (max (height_form f1) (height_form f2))"
  | "height_form (SubstFm f sb) = Suc (height_form f)"


  (* ----------------------------------------------------------------------  *)
subsection {* Termination of pushing substititutions *}
  (* ----------------------------------------------------------------------  *)


fun subst_height_concept ::  "('nr, 'nc, 'ni) concept \<Rightarrow> nat" where
    "subst_height_concept Bottom = 0"
  | "subst_height_concept Top = 0"
  | "subst_height_concept (AtomC sign a) = 0"
  | "subst_height_concept (BinopC bop c1 c2) = max (subst_height_concept c1) (subst_height_concept c2)"
  | "subst_height_concept (NegC c) = subst_height_concept c"
  | "subst_height_concept (NumRestrC nro n r c) = subst_height_concept c"
  | "subst_height_concept (SubstC c sb) = height_concept c + subst_height_concept c"
  | "subst_height_concept (SomeC r c) = subst_height_concept c"
  | "subst_height_concept (AllC r c) = subst_height_concept c"

fun subst_height_fact ::  "('nr, 'nc, 'ni) fact \<Rightarrow> ('nr, 'nc, 'ni) subst list \<Rightarrow> nat" where
    "subst_height_fact (Inst x c) sbsts = subst_height_concept (subst_closure_concept c sbsts)"
  | "subst_height_fact _ sbsts = length sbsts"


fun subst_height_form ::  "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) subst list \<Rightarrow> nat" where
    "subst_height_form (ConstFm cn) sbsts = length sbsts"
  | "subst_height_form (FactFm fct) sbsts = subst_height_fact fct sbsts"
  | "subst_height_form (NegFm f) sbsts = subst_height_form f sbsts"
  | "subst_height_form (BinopFm bop f1 f2) sbsts = max (subst_height_form f1 sbsts) (subst_height_form f2 sbsts)"
  | "subst_height_form (SubstFm f sb) sbsts = subst_height_form f (sb # sbsts)"

definition "satis_induct_order_level == measures [\<lambda> fm. subst_height_form fm [], height_form]"

lemma wf_satis_induct_order_level: "wf satis_induct_order_level"
by (simp add: satis_induct_order_level_def)



lemma height_concept_positive [simp]: "0 < height_concept c"
by (induct c) auto

lemma subst_height_concept_mono_closure [rule_format]:
  "\<forall> c1 c2. subst_height_concept c1 < subst_height_concept c2 \<longrightarrow> height_concept c1 \<le> height_concept c2 \<longrightarrow>
  subst_height_concept (subst_closure_concept c1 sbsts) < subst_height_concept (subst_closure_concept c2 sbsts)"
by (induct sbsts) simp_all


lemma height_concept_neg_norm_concept [rule_format, simp]:
  "\<forall> sign. height_concept (neg_norm_concept sign c) \<le> height_concept c"
apply (induct c)
apply clarsimp+
apply (drule_tac x="\<not> sign" in spec) apply arith
apply (clarsimp,(drule_tac x=sign in spec)+, arith)
apply clarsimp+
done

lemma subst_height_concept_neg_norm_concept [rule_format, simp]:
  "\<forall> sign. subst_height_concept (neg_norm_concept sign c) \<le> subst_height_concept c"
apply (induct c)
apply auto
apply ((drule_tac x=sign in spec)+, arith)+
apply (drule_tac x=sign in spec)
apply (subgoal_tac "height_concept (neg_norm_concept sign c) \<le> height_concept c")
apply arith
apply (rule height_concept_neg_norm_concept)
done

lemma subst_height_concept_mono_closure_nnc:
  "subst_height_concept c1 < subst_height_concept c2 \<Longrightarrow>
  height_concept c1 \<le> height_concept c2 \<Longrightarrow>
  subst_height_concept (subst_closure_concept (neg_norm_concept sign c1) sbsts) < subst_height_concept (subst_closure_concept c2 sbsts)"
apply (rule subst_height_concept_mono_closure) 
apply (rule le_less_trans) apply (rule subst_height_concept_neg_norm_concept) apply simp
apply (rule le_trans) apply (rule height_concept_neg_norm_concept) apply simp
done

lemma length_subst_height_concept [simp]:
  "length sbsts < subst_height_concept (subst_closure_concept (SubstC c sb) sbsts)"
apply (induct sbsts)
apply clarsimp
apply clarsimp
apply (subgoal_tac "subst_height_concept (subst_closure_concept (SubstC c sb) sbsts)
        < subst_height_concept (subst_closure_concept (SubstC (SubstC c sb) a) sbsts)")
apply arith
apply (simp add: subst_height_concept_mono_closure) 
done

lemma subst_height_concept_positive [simp]:
  "0 < subst_height_concept (subst_closure_concept (SubstC c sb) sbsts)"
by (insert length_subst_height_concept [of sbsts c sb]) arith


lemma height_form_subst_closure_form [rule_format, simp]:
"\<forall> fm. height_form (subst_closure_form fm (sbsts)) =  length sbsts + height_form fm"
by (induct sbsts) simp+

lemma subst_height_form_subst_closure_form [rule_format, simp]:
"\<forall> fm. subst_height_form (subst_closure_form fm (sbsts)) sbsts'
      =  subst_height_form fm (sbsts @ sbsts')"
by (induct sbsts) simp+

lemma push_subst_fact_decr_rsubst: "extract_subst fct = None \<Longrightarrow> sb = (RSubst r rop v1v2) \<Longrightarrow> 
  (subst_height_form (push_subst_fact fct sb) sbsts < subst_height_fact fct (sb # sbsts))"
apply (case_tac fct)
prefer 3
  (* Eq *)
apply simp 
prefer 2
  (* AtomR *)
apply (clarsimp  simp add: split_def subst_AtomR_SDiff_def subst_AtomR_SAdd_def Let_def
  split : if_split_asm subst_op.split )


  (* Inst *)
apply (rename_tac x c)
apply (case_tac c)
apply (fastforce intro: subst_height_concept_mono_closure)+

  (* case c = NumRestrC *)
apply (case_tac v1v2)
apply simp
apply (intro conjI impI)
apply (case_tac rop)
apply (clarsimp simp add: nnf_IfThenElseFm_def IfThenElseFm_def subst_height_concept_mono_closure_nnc simp del: neg_norm_concept.simps)
apply clarsimp
apply (rename_tac x nro n c v1 v2)
apply (case_tac n)
apply (case_tac nro) apply clarsimp+
apply (clarsimp simp add: nnf_IfThenElseFm_def IfThenElseFm_def subst_height_concept_mono_closure_nnc simp del: neg_norm_concept.simps)
apply (simp add: IfThenElseFm_def subst_height_concept_mono_closure)

  (* case c = SubstC *)
apply simp

  (* case c = SomeC *)
apply (case_tac v1v2)
apply (case_tac rop)
apply (clarsimp simp add: nnf_IfThenElseFm_def IfThenElseFm_def subst_height_concept_mono_closure subst_height_concept_mono_closure_nnc simp del: neg_norm_concept.simps)
apply (clarsimp simp add: nnf_IfThenElseFm_def IfThenElseFm_def subst_height_concept_mono_closure subst_height_concept_mono_closure_nnc simp del: neg_norm_concept.simps)

  (* case c = AllC *)
apply (case_tac v1v2)
apply (case_tac rop)
defer
apply (clarsimp simp add: nnf_IfThenElseFm_def IfThenElseFm_def subst_height_concept_mono_closure subst_height_concept_mono_closure_nnc simp del: neg_norm_concept.simps)
apply (clarsimp simp add: nnf_IfThenElseFm_def IfThenElseFm_def subst_height_concept_mono_closure subst_height_concept_mono_closure_nnc)
apply (rename_tac x c v1 v2)
apply (subgoal_tac "height_concept (neg_norm_concept True c) \<le> height_concept c") prefer 2 apply (simp (no_asm_simp))
apply (subgoal_tac "subst_height_concept (neg_norm_concept True c) \<le> subst_height_concept c") prefer 2 apply (simp (no_asm_simp))
apply (subgoal_tac "height_concept (neg_norm_concept False c) \<le> height_concept c") prefer 2 apply (simp (no_asm_simp))
apply (subgoal_tac "subst_height_concept (neg_norm_concept False c) \<le> subst_height_concept c") prefer 2 apply (simp (no_asm_simp))
apply (intro conjI)
apply (rule subst_height_concept_mono_closure, (simp (no_asm_simp))+)+
done

lemma height_concept_rename_in_concept [rule_format, simp]:
  "\<forall> sbsts. height_concept (rename_in_concept c sbsts) \<le> height_concept c"
apply (induct c)
apply simp_all
apply clarsimp apply (drule_tac x=sbsts in spec)+ apply arith
done

lemma subst_height_concept_rename_in_concept [rule_format, simp]:
  "\<forall> sbsts. subst_height_concept (rename_in_concept c sbsts) \<le> subst_height_concept c"
apply (induct c)
apply simp_all
apply clarsimp apply (drule_tac x=sbsts in spec)+ apply arith
apply clarsimp

apply (rename_tac c sbsts)
apply (drule_tac x=sbsts in spec)
apply (subgoal_tac "height_concept (rename_in_concept c sbsts) \<le> height_concept c")
apply arith apply simp
done


lemma push_subst_fact_decr_csubst: "extract_subst fct = None \<Longrightarrow> sb = (CSubst c rop v) \<Longrightarrow> 
  (subst_height_form (push_subst_fact fct sb) sbsts < subst_height_fact fct (sb # sbsts))"
apply simp
apply (case_tac fct)
prefer 3
  (* Eq *)
apply simp 
prefer 2
  (* AtomR *)
apply (clarsimp)
  (* Inst *)
apply (rename_tac x cpt)
apply (case_tac cpt)
apply (simp split: if_split_asm subst_op.split )+
apply (fastforce intro: subst_height_concept_mono_closure)+
apply (simp split : if_split_asm subst_op.split)+
apply (fastforce intro: subst_height_concept_mono_closure)+
done

lemma push_subst_fact_decr: "extract_subst fct = None \<Longrightarrow>
  subst_height_form (push_subst_fact fct sb) sbsts' < subst_height_fact fct (sb # sbsts')"
apply (case_tac sb)
apply (rule push_subst_fact_decr_rsubst) apply assumption+
apply (rule push_subst_fact_decr_csubst) apply assumption+
done

lemma extract_subst_Some:
  "(extract_subst fct = Some (x, c, sb)) = (fct = (Inst x (SubstC c sb)))"
apply (case_tac fct)
apply (rename_tac ni concept)
apply (case_tac concept) 
apply simp_all
done

lemma push_subst_extract_some_SubstC: "extract_subst fct = Some(x, c, sb) \<Longrightarrow>
  subst_height_concept (subst_closure_concept (SubstC c sb) sbsts) = subst_height_fact fct sbsts"
by (clarsimp simp add: extract_subst_Some)


lemma height_fact_extract_some_decr: "extract_subst fct = Some(x, c, sb) \<Longrightarrow>
  height_concept c <  (height_fact fct)"
by (clarsimp simp add: extract_subst_Some)

lemma push_subst_extract_some_isubst: "extract_subst fct = Some(x, c, sb) \<Longrightarrow>
  subst_height_concept (subst_closure_concept (rename_in_concept c vsbsts) sbsts) < subst_height_fact fct sbsts"
apply (clarsimp simp add: extract_subst_Some)
apply (rule subst_height_concept_mono_closure)
apply simp_all
apply (insert subst_height_concept_rename_in_concept [of c vsbsts]) 
apply (subgoal_tac "0 < height_concept c") prefer 2 apply simp apply arith

apply (insert height_concept_rename_in_concept [of c vsbsts]) 
apply (subgoal_tac "0 < height_concept c") prefer 2 apply simp apply arith
done

lemma subst_height_concept_under_closure [rule_format]: "\<forall> c1 c2. 
  subst_height_concept c1 = subst_height_concept c2 \<longrightarrow> height_concept c1 = height_concept c2 \<longrightarrow> 
  subst_height_concept (subst_closure_concept c1 sbsts) = subst_height_concept (subst_closure_concept c2 sbsts)"
by (induct sbsts) simp_all

lemma subst_height_concept_same_length [rule_format]:
  "length sbsts1 = length sbsts2 \<Longrightarrow> 
  \<forall> c. (subst_height_concept (subst_closure_concept c sbsts1) = subst_height_concept (subst_closure_concept c sbsts2))"
apply(induct rule:list_induct2)
apply simp
apply (fastforce intro: subst_height_concept_under_closure)
done

lemma subst_height_fact_same_length:
  "length sbsts1 = length sbsts2 \<Longrightarrow> 
  subst_height_fact f sbsts1 = subst_height_fact f sbsts2"
apply (induct f)
apply simp_all
apply (erule subst_height_concept_same_length)
done


lemma subst_height_form_same_length [rule_format]:
  "\<forall> sbsts1 sbsts2. length sbsts1 = length sbsts2 \<longrightarrow> 
  subst_height_form f sbsts1 = subst_height_form f sbsts2"
apply (induct f)
apply clarsimp+
apply (erule subst_height_fact_same_length)
apply clarify apply (simp (no_asm)) apply fast
apply clarify apply (drule spec)+ apply (drule mp, assumption)+ apply simp
(* QuantifFm
apply clarify apply (drule spec)+ apply (drule mp, assumption)+ apply simp
*)
apply clarify 
apply (simp (no_asm))
apply (drule spec)+ apply (drule mp) prefer 2 apply assumption apply simp
done


termination push_subst_form

apply (relation "measures [(\<lambda>p. (subst_height_form (fst p) (snd p))), (\<lambda>p.(height_form (fst p)))]")
apply simp
apply simp_all

(* subcase None / # *)
apply (simp add: push_subst_fact_decr)

(* subcase Some *)
apply (clarsimp simp add: push_subst_extract_some_SubstC) 
apply (clarsimp simp only: height_fact_extract_some_decr)
apply arith+
done


  (* ----------------------------------------------------------------------  *)
subsection {* Structural correctness of pushing substitutions *}
  (* ----------------------------------------------------------------------  *)

fun subst_hidden_in_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> bool" where
    "subst_hidden_in_concept (SubstC c sb) = False"
  | "subst_hidden_in_concept _ = True"

fun subst_hidden_in_fact :: "('nr, 'nc, 'ni) fact \<Rightarrow> bool" where
    "subst_hidden_in_fact (Inst x c) = subst_hidden_in_concept c"
  | "subst_hidden_in_fact (AtomR sign r x y) = True"
  | "subst_hidden_in_fact (Eq sign x y) = True"

fun subst_hidden_in_form :: "('nr, 'nc, 'ni) form \<Rightarrow> bool" where
    "subst_hidden_in_form (ConstFm cn) = True"
  | "subst_hidden_in_form (FactFm fct) = subst_hidden_in_fact fct"
  | "subst_hidden_in_form (NegFm f) = subst_hidden_in_form f"
  | "subst_hidden_in_form (BinopFm bop f1 f2) = (subst_hidden_in_form f1 \<and> subst_hidden_in_form f2)"
  | "subst_hidden_in_form (SubstFm f sb) = False"

lemma extract_subst_subst_hidden_in_fact: 
  "extract_subst fct = None \<Longrightarrow> subst_hidden_in_fact fct"
apply (case_tac fct)
apply (rename_tac ni concept)
apply (case_tac concept)
apply clarsimp+
done


lemma extract_subst_none_subst_hidden_in_fact: 
  "(extract_subst fct = None) = subst_hidden_in_fact fct"
apply (rule iffI)
apply (metis extract_subst_subst_hidden_in_fact)
apply (case_tac fct)
apply (rename_tac ni concept)
apply (case_tac concept)
apply clarsimp+
done

lemma subst_hidden_in_form_push_subst_form [simp]:
  "subst_hidden_in_form (push_subst_form fm sbsts)"
apply (induct fm sbsts rule: push_subst_form.induct)
apply simp_all
apply (simp split: option.split list.split subst.split)
apply (intro conjI impI allI)
apply (clarsimp simp add: extract_subst_subst_hidden_in_fact)+
done

  (* ----------------------------------------------------------------------  *)
subsection {* Structural properties of pushing substitutions *}
  (* ----------------------------------------------------------------------  *)

lemma is_prenex_qform_rename_in_qform [rule_format,simp]:
"\<forall> sbsts. is_quantif_free f \<longrightarrow> is_quantif_free (rename_in_qform f sbsts)"
by (induct f) (auto split: subst.split rename.split)

  
  (* ----------------------------------------------------------------------  *)
subsection {* Semantics-preservation of pushing substitutions *}
  (* ----------------------------------------------------------------------  *)


lemma interp_form_SubstFm_FactFm_Rel_AtomR_SDiff:
  "interp_fact (AtomR sign r x y) (interp_subst (RSubst r SDiff (v1, v2)) i) = 
   interp_form (subst_AtomR_SDiff sign r x y v1 v2) i"
by (simp add: subst_AtomR_SDiff_def interp_r_modif_def) fast

lemma interp_form_SubstFm_FactFm_Rel_AtomR_SAdd:
  "interp_fact (AtomR sign r x y) (interp_subst (RSubst r SAdd (v1, v2)) i) = 
   interp_form (subst_AtomR_SAdd sign r x y v1 v2) i"
by (simp add: subst_AtomR_SAdd_def interp_r_modif_def)

lemma interp_form_push_rsubst_fact_AtomR: 
  "interp_form (push_rsubst_fact r rop (v1, v2) (AtomR sign r' x1 x2)) i =
       interp_fact (AtomR sign r' x1 x2) (interp_subst (RSubst r rop (v1, v2)) i)"
apply (case_tac "r = r'")
apply (case_tac rop)
apply (simp only: interp_form_SubstFm_FactFm_Rel_AtomR_SDiff) apply simp
apply (simp only: interp_form_SubstFm_FactFm_Rel_AtomR_SAdd) apply simp
apply simp
done


lemma interp_form_push_rsubst_concept_numrestrc_SAdd:
  "well_formed_interp i \<Longrightarrow>
     interp_fact (Inst x (NumRestrC nro (Suc n) r c)) (interp_subst (RSubst r SAdd (v1, v2)) i) =
     interp_form (push_rsubst_concept_numrestrc SAdd (v1, v2) x nro (Suc n) r c) i"
apply (simp only: push_rsubst_concept_numrestrc.simps interp_form_nnf_IfThenElseFm)
apply (simp only: interp_form.simps interp_form_IfThenElseFm lift_ite_def)
apply (split if_split)
apply (intro impI conjI)
apply (clarsimp simp add: interp_numres_ord_Eq_SAdd)

apply (simp only: interp_form.simps interp_binopFm.simps de_Morgan_conj)
apply (elim disjE)
apply (clarsimp simp add: rel_restrict_diff rel_restrict_insert interp_r_modif_def)

apply (clarsimp simp add: rel_restrict_diff rel_restrict_insert interp_r_modif_def)
apply (simp add: insert_absorb)
done

lemma interp_form_push_rsubst_concept_numrestrc_SDiff:
  "well_formed_interp i \<Longrightarrow>
    interp_fact (Inst x (NumRestrC nro n r c)) (interp_subst (RSubst r SDiff (v1, v2)) i) =
    interp_form (push_rsubst_concept_numrestrc SDiff (v1, v2) x nro n r c) i"
apply (simp only: push_rsubst_concept_numrestrc.simps interp_form_nnf_IfThenElseFm)
apply (simp only: interp_form.simps interp_form_IfThenElseFm lift_ite_def)
apply (split if_split)
apply (intro impI conjI)
apply (clarsimp simp add: interp_numres_ord_Eq_SDiff)
apply (simp only: interp_form.simps interp_binopFm.simps de_Morgan_conj)
apply (elim disjE)
apply (clarsimp simp add: rel_restrict_diff rel_restrict_insert interp_r_modif_def)+
done

lemma interp_form_push_rsubst_concept_numrestrc: 
  "well_formed_interp i \<Longrightarrow>
     interp_fact (Inst x (NumRestrC nro n r c)) (interp_subst (RSubst r rop (v1, v2)) i) =
     interp_form (push_rsubst_concept_numrestrc rop (v1, v2) x nro n r c) i"
apply (case_tac rop)
apply (simp only: interp_form_push_rsubst_concept_numrestrc_SDiff)
apply (case_tac n)
apply (case_tac nro)
apply simp
apply simp
apply (simp only: interp_form_push_rsubst_concept_numrestrc_SAdd)
done

lemma interp_form_push_rsubst_concept_somec: 
  "well_formed_interp i \<Longrightarrow>
    interp_fact (Inst x (SomeC r c)) (interp_subst (RSubst r rop (v1, v2)) i) =
    interp_form (push_rsubst_concept_somec rop (v1, v2) x r c) i"
apply (simp only: interp_fact_SomeC_NumRestrC interp_form_push_rsubst_concept_numrestrc)
apply (case_tac rop)
apply (simp add: lift_ite_def)+
done


lemma interp_form_push_rsubst_concept_allc: 
  "well_formed_interp i \<Longrightarrow>
     interp_fact (Inst x (AllC r c)) (interp_subst (RSubst r rop (v1, v2)) i) =
     interp_form (push_rsubst_concept_allc rop (v1, v2) x r c) i"
apply (simp only: interp_fact_AllC_NumRestrC 
  interp_form_push_rsubst_concept_numrestrc well_formed_interp_interp_subst)
apply (case_tac rop)
apply (simp add: lift_ite_def)+
done


lemma interp_form_push_rsubst_fact_Inst:
assumes wfi: "well_formed_interp i"
shows
  "interp_fact (Inst x c) (interp_subst (RSubst r rop (v1, v2)) i) = 
  interp_form (push_rsubst_concept r rop (v1, v2) x c) i"
proof (cases c)
  case (NumRestrC numres_ord nat nr concept) thus ?thesis
    apply (simp only: push_rsubst_concept.simps split: if_split)
    apply (intro conjI impI)
    apply (simp only: interp_form_push_rsubst_concept_numrestrc wfi)
    by simp
next
  case (SomeC nr concept) thus ?thesis
    apply (simp only: push_rsubst_concept.simps split:if_split)
    apply (intro conjI impI)
    apply (simp only: interp_form_push_rsubst_concept_somec wfi)
    by simp
next
  case (AllC nr concept) thus ?thesis
    apply (simp only: push_rsubst_concept.simps split: if_split)
    apply (intro conjI impI)
    apply (simp only: interp_form_push_rsubst_concept_allc wfi)
    by simp
next
  case (BinopC bop c1 c2) thus ?thesis
    apply (case_tac bop) 
    by simp_all
qed simp_all


lemma interp_form_push_rsubst_fact:
  "well_formed_interp i \<Longrightarrow>
  interp_form (push_rsubst_fact r rop v1v2 fct) i = interp_fact fct (interp_subst (RSubst r rop v1v2) i)"
apply (case_tac v1v2)
apply (case_tac fct)
apply (simp only: push_rsubst_fact.simps interp_form_push_rsubst_fact_Inst)
apply (simp only: interp_form_push_rsubst_fact_AtomR) 
apply simp
done


lemma interp_form_push_csubst_fact_Inst:
  "well_formed_interp i \<Longrightarrow>
  interp_fact (Inst x c) (interp_subst (CSubst cr rop v) i) = 
  interp_form (push_csubst_concept cr rop v x c) i"
by (case_tac c) (auto split: subst_op.splits)

lemma interp_form_push_csubst_fact:
  "well_formed_interp i \<Longrightarrow> 
  interp_form (push_csubst_fact c rop v fct) i = interp_fact fct (interp_subst (CSubst c rop v) i)"
apply (case_tac fct)
apply (simp only: interp_form_push_csubst_fact_Inst)
apply simp_all
done


lemma interp_subst_RSubst_ISubst:
  "interp_subst (RSubst nr subst_op (x1, x2)) (interp_rename sb i) =
   interp_rename sb (interp_subst (RSubst nr subst_op (replace_var sb x1, replace_var sb x2)) i)"
apply (case_tac sb)
apply (case_tac subst_op)
apply (simp add: interp_i_modif_def interp_r_modif_def)+
done

lemma interp_subst_CSubst_ISubst:
  "interp_subst (CSubst cr subst_op v) (interp_rename sb i) =
  interp_rename sb (interp_subst (CSubst cr subst_op (replace_var sb v)) i)"
apply (case_tac sb)
apply (case_tac subst_op)
apply (simp add: interp_i_modif_def interp_c_modif_def)+
done


lemma is_isubst_interp_c [simp]:
  "interp_c (interp_rename sb i) = interp_c i"
by (case_tac sb) auto

lemma forall_is_isubst_interp_c [rule_format, simp]: 
  "interp_c (interp_rename_closure sbsts i) = interp_c i"
by (induct sbsts) (auto)

lemma is_isubst_interp_r [simp]:
  "interp_r (interp_rename sb i) = interp_r i"
by (case_tac sb) auto

lemma forall_is_isubst_interp_r [rule_format, simp]: 
  "interp_r (interp_rename_closure sbsts i) = interp_r i"
by (induct sbsts) (auto)

lemma interp_d_interp_subst_closure [simp]: 
  "interp_d (interp_subst_closure sbsts i) = interp_d i"
by (induct sbsts) auto

lemma interp_d_interp_rename_closure [simp]: 
  "interp_d (interp_rename_closure sbsts i) = interp_d i"
by (induct sbsts) auto


lemma interp_c_interp_rename_closure_var_pair_to_substs [simp]:
  "interp_c (interp_rename_closure sbsts i) a = interp_c i a"
by (induct sbsts) auto

lemma interp_r_interp_rename_closure_var_pair_to_substs [simp]: 
"(interp_r (interp_rename_closure sbsts i) r) = interp_r i r"
by (induct sbsts) auto


lemma interp_i_interp_rename [simp]: 
   "interp_i (interp_rename sb i) v = interp_i i (replace_var sb v)"
by (case_tac sb) (simp)

lemma interp_i_interp_rename_closure_var_pair_to_substs [rule_format,simp]: 
"\<forall> v i. (interp_i (interp_rename_closure sbsts i) v) = interp_i i (rename_in_var v sbsts)"
apply (induct sbsts) 
apply clarsimp+
done

lemma interp_subst_RSubst [rule_format]:  "\<forall> v1 v2 i.  
 (interp_subst (RSubst nr subst_op (v1, v2)) (interp_rename_closure sbsts i)) = 
 (interp_rename_closure sbsts
             (interp_subst (RSubst nr subst_op (rename_in_var v1 sbsts, rename_in_var v2 sbsts)) i))"
apply (induct sbsts)
apply simp
apply (simp del: interp_subst.simps add: interp_subst_RSubst_ISubst)
done

lemma interp_subst_CSubst [rule_format]:  "\<forall> v i.  
 (interp_subst (CSubst cr subst_op v) (interp_rename_closure sbsts i)) = 
 (interp_rename_closure sbsts
             (interp_subst (CSubst cr subst_op (rename_in_var v sbsts)) i))"
apply (induct sbsts)
apply simp
apply (simp del: interp_subst.simps add: interp_subst_CSubst_ISubst)
done


lemma interp_concept_rename_in_concept: 
fixes c
shows  "well_formed_interp i \<longrightarrow>
        (interp_concept (rename_in_concept c sbsts) i = 
        interp_concept c (interp_rename_closure  sbsts i))"
proof (induct c arbitrary: sbsts i)
case (SubstC c subst) show ?case
proof
assume wfi: "well_formed_interp i" 
show "interp_concept (rename_in_concept (SubstC c subst) sbsts) i =
    interp_concept (SubstC c subst) (interp_rename_closure sbsts i)"
    proof (simp (no_asm_use), induct subst)
    next
    case (RSubst nr subst_op prod) show ?case
      apply (case_tac prod)
      apply (simp add: SubstC.hyps wfi del: interp_subst.simps)
      by (simp only: interp_subst_RSubst)
  next
    case (CSubst cr subst_op v) show ?case
      apply (simp add: SubstC.hyps wfi del: interp_subst.simps)
      by (simp only: interp_subst_CSubst)
  qed
  qed
qed (simp_all)

lemma interp_fact_rename_in_fact:
  "well_formed_interp i \<Longrightarrow>
  interp_fact (rename_in_fact fct sbsts) i = interp_fact fct (interp_rename_closure sbsts i)"
by (case_tac fct) (simp add: interp_concept_rename_in_concept)+


lemma interp_form_push_subst_fact:
  "well_formed_interp i \<Longrightarrow>
   interp_form (push_subst_fact fct sb) i = interp_fact fct (interp_subst sb i)"
apply (case_tac sb)
apply (simp del: interp_subst.simps add: interp_form_push_rsubst_fact)
apply (simp del: interp_subst.simps add: interp_form_push_csubst_fact)
done

lemma interp_form_push_subst_form_sbsts [rule_format]: shows 
   "well_formed_interp i \<longrightarrow>
   interp_form (push_subst_form fm sbsts) i = interp_form fm (interp_subst_closure sbsts i)"

   proof (induction fm sbsts arbitrary: i rule: push_subst_form.induct)

   case 1 (* ConstFm *) show ?case by simp
   next
   case 3 (* NegFm *) thus ?case by simp
   next
   case (4 bop f1 f2 sbsts i) (* BinOp *) thus ?case
   by simp
   next
   case (5 f sb sbsts i) (* SubstFm *) 
   thus ?case
   by simp
   next
   case (2 fct sbsts i) (* FactFm *) 
   show ?case
   proof (cases "extract_subst fct")
      case None 
      hence esn: "extract_subst fct = None" by simp
      thus ?thesis
          proof (cases sbsts) 
          case Nil thus ?thesis by (simp add: esn)
          next
          case (Cons sb sbsts')
          hence "sbsts = sb # sbsts'" by simp
          moreover hence "well_formed_interp i \<longrightarrow> 
          interp_form (push_subst_form (push_subst_fact fct sb) sbsts') i =
          interp_form (push_subst_fact fct sb) (interp_subst_closure sbsts' i)" 
          by (simp add: "2.IH" esn )
          ultimately show ?thesis
          by (clarsimp simp add: esn interp_form_push_subst_fact)
          qed
    next
      case (Some a)
      hence esn0: "extract_subst fct = Some a" by simp
      thus ?thesis
      proof (cases a) case (fields x c sb)
      hence esn: "extract_subst fct = Some(x, c, sb)" by (simp add: esn0)
      moreover from esn have fctInstSubstC:  "(fct = (Inst x (SubstC c sb)))" by (simp add: extract_subst_Some)
      thus ?thesis
        proof -
        have IH: 
           "well_formed_interp i \<longrightarrow> 
            interp_form (push_subst_form (FactFm (Inst x c)) (sb # sbsts)) i =
            interp_form (FactFm (Inst x c)) (interp_subst_closure (sb # sbsts) i)" 
            by (simp add: "2.IH" esn del: interp_form.simps push_subst_form.simps)
        show ?thesis
          apply (simp only: fctInstSubstC)
          apply (subst push_subst_form.simps)
          apply (simp add: esn IH del: interp_subst_closure.simps push_subst_form.simps interp_fact.simps)
          by (simp del: push_subst_form.simps)
        qed
      qed
   qed
qed

lemma interp_form_push_subst_form [simp]:
  "well_formed_interp i \<Longrightarrow> interp_form (push_subst_form fm []) i = interp_form fm i"
by (simp add: interp_form_push_subst_form_sbsts)

lemma interp_form_rename_in_form_interp_rename_closure [rule_format]:
  "\<forall> sbsts i. well_formed_interp i \<longrightarrow> 
  interp_form (rename_in_form fm sbsts) i = 
  interp_form fm (interp_rename_closure sbsts i)"
apply (induct fm)
apply (simp del: rename_in_subst.simps add: interp_fact_rename_in_fact)+
apply (intro conjI allI impI)
apply (rename_tac fm subst sbsts i)
apply (case_tac subst)
apply (clarsimp simp del: interp_subst.simps simp add: interp_subst_RSubst)
apply (clarsimp simp del: interp_subst.simps simp add: interp_subst_CSubst)
done


lemma interp_qform_rename_in_qform [rule_format]:
  "\<forall> sbsts i. well_formed_interp i \<longrightarrow> 
  is_quantif_free fm \<longrightarrow>
  interp_qform (rename_in_qform fm sbsts) i = 
  interp_qform fm (interp_rename_closure sbsts i)"
apply (induct fm)
apply (simp del: rename_in_subst.simps add: interp_fact_rename_in_fact)+
apply (intro conjI allI impI)
apply (rename_tac fm subst sbsts i)
apply (case_tac subst)

apply (clarsimp simp del: interp_subst.simps simp add: interp_subst_RSubst)

apply (clarsimp simp del: interp_subst.simps simp add: interp_subst_CSubst)

apply (clarsimp simp del: rename_in_subst.simps)
done


lemma interp_form_subst_closure_form [rule_format]:
  "\<forall> f. interp_form (subst_closure_form f sbsts) i = 
 interp_form f (interp_subst_closure sbsts i)"
by (induct sbsts) clarsimp+ 

lemma interp_qform_subst_closure_qform [rule_format]:
  "\<forall> f. interp_qform (subst_closure_qform f sbsts) i = 
 interp_qform f (interp_subst_closure sbsts i)"
by (induct sbsts) clarsimp+ 

lemma interp_qform_rename_closure_qform [rule_format]:
  "\<forall> f. interp_qform (rename_closure_qform f sbsts) i = 
 interp_qform f (interp_rename_closure sbsts i)"
by (induct sbsts) clarsimp+ 

  (* ----------------------------------------------------------------------  *)
subsection {* Negation normal form preservation of pushing substitutions *}
  (* ----------------------------------------------------------------------  *)

lemma push_rsubst_concept_numrestrc_pres_neg_norm_concept [rule_format, simp]:
  "is_neg_norm_form (push_rsubst_concept_numrestrc rop v1v2 x numres_ord n nr c)"
apply (case_tac v1v2)
apply (case_tac rop)
apply (case_tac n)
apply simp_all
apply (case_tac numres_ord)
apply (case_tac n, simp_all)+
done

lemma push_rsubst_concept_somec_pres_neg_norm_concept [rule_format, simp]:
   "is_neg_norm_form (push_rsubst_concept_somec rop v1v2 x nr c)"
apply (case_tac v1v2)
apply (case_tac rop)
apply simp_all
done

lemma push_rsubst_concept_allc_pres_neg_norm_concept [rule_format, simp]:
   "is_neg_norm_form (push_rsubst_concept_allc rop v1v2 x nr c)"
apply (case_tac v1v2)
apply (case_tac rop)
apply simp_all
done

lemma push_rsubst_concept_pres_neg_norm_concept [rule_format, simp]:
   "is_neg_norm_concept c \<longrightarrow> is_neg_norm_form (push_rsubst_concept r rop v1v2 x c)"
by (induct c) simp_all

lemma rename_in_concept_pres_neg_norm_concept [rule_format, simp]:
   "\<forall> sbsts. is_neg_norm_concept c \<longrightarrow> is_neg_norm_concept (rename_in_concept c sbsts)"
by (induct c) auto

lemma push_rsubst_fact_pres_neg_norm_fact [rule_format, simp]: 
   "is_neg_norm_fact f \<longrightarrow> is_neg_norm_form (push_rsubst_fact nr subst_op pair f)"
apply (case_tac pair)
apply (case_tac f)
apply simp_all
apply (clarsimp split : subst_op.split simp add: subst_AtomR_SDiff_def subst_AtomR_SAdd_def)
done

lemma push_csubst_concept_pres_neg_norm_concept [rule_format, simp]:
   "is_neg_norm_concept c \<longrightarrow> is_neg_norm_form (push_csubst_concept cr rop v x c)"
by (induct c) (auto split: subst_op.split)

lemma push_csubst_fact_pres_neg_norm_fact [rule_format, simp]: 
  "is_neg_norm_fact f \<longrightarrow> is_neg_norm_form (push_csubst_fact nc subst_op ni f)"
by (case_tac f) simp_all

lemma rename_in_fact_pres_neg_norm_fact [rule_format, simp]: 
   "is_neg_norm_fact f \<longrightarrow> is_neg_norm_fact (rename_in_fact f sbsts)"
by (case_tac f) simp_all

lemma push_subst_fact_pres_neg_norm_fact [rule_format, simp]: 
"is_neg_norm_fact f \<longrightarrow> is_neg_norm_form (push_subst_fact f sbst)"
by (case_tac sbst) simp_all

lemma push_subst_form_pres_neg_norm_form [rule_format, simp]: 
"is_neg_norm_form fm \<longrightarrow> is_neg_norm_form (push_subst_form fm sbsts)"
apply (induction fm sbsts rule: push_subst_form.induct)
prefer 2
apply (simp (no_asm_simp))
apply (simp (no_asm_simp) del: push_subst_form.simps split add: option.split)
apply (intro conjI impI)
apply (simp (no_asm_simp) split: option.split list.split)
apply (clarsimp simp add: extract_subst_Some)
apply simp_all
done

lemma is_isubst_free_push_qform [rule_format, simp]:
  "\<forall> sbsts. is_rename_free_qform (rename_in_qform f sbsts)"
by (induct f) auto

lemma interp_apply_var_interp_subst_inj_on: 
  "inj_on f A \<Longrightarrow> 
  interp_i_equivalent 
  (interp_apply_var f (interp_subst (apply_var_subst f subst) i)) 
  (interp_subst subst (interp_apply_var f i)) 
  A"
apply (simp add: interp_apply_var_def interp_i_update_vartype_def interp_i_equivalent_def)

apply (case_tac subst)
apply simp
apply (rename_tac nr subst_op prod)
apply (case_tac subst_op)
apply simp
apply (case_tac prod)
apply (simp add: interp_r_modif_def)
apply (case_tac prod)
apply (simp add: interp_r_modif_def)

apply simp
apply (simp add: interp_c_modif_def)
apply (rename_tac nc subst_op ni)
apply (case_tac subst_op)
apply simp+
done

lemma interp_apply_var_interp_subst: 
  "inj f \<Longrightarrow>
  (interp_apply_var f (interp_subst (apply_var_subst f subst) i)) = 
  (interp_subst subst (interp_apply_var f i))"
  apply (simp add: interp_apply_var_def interp_i_update_vartype_def)
  apply (case_tac subst)
  apply simp
  apply (rename_tac nr subst_op prod)
  apply (case_tac subst_op)
  apply simp
  apply (case_tac prod)
  apply (simp add: interp_r_modif_def)
  apply (case_tac prod)
  apply (simp add: interp_r_modif_def)

  apply simp
  apply (rename_tac nc subst_op ni)
  apply (simp add: interp_c_modif_def)
  apply (case_tac subst_op)
  apply simp+
done

lemma interp_i_update_vartype_interp_subst_Free [simp]: 
  "(interp_apply_var Free (interp_subst (apply_var_subst Free subst) i)) = 
  (interp_subst subst (interp_apply_var Free i))"
by (insert interp_apply_var_interp_subst [where f=Free])
   (auto simp add: inj_on_def comp_def)

lemma interp_concept_apply_var_concept_Free [rule_format, simp]:
  "\<forall> i. well_formed_interp i \<longrightarrow> interp_concept (apply_var_concept Free c) i = interp_concept c (interp_apply_var Free i)"
by (induct c) simp_all

lemma interp_fact_apply_var_fact_Free [simp]:
  "well_formed_interp i \<Longrightarrow> interp_fact (apply_var_fact Free fct) i = interp_fact fct (interp_apply_var Free i)"
by (case_tac fct) simp_all

lemma interp_form_apply_var_form_Free [rule_format, simp]:
"\<forall> i. well_formed_interp i \<longrightarrow> interp_form (apply_var_form Free frm)  i = interp_form frm (interp_apply_var Free i)"
by (induct frm) simp_all

lemma interp_qform_apply_var_form_Free [rule_format, simp]:
"\<forall> i. well_formed_interp i \<longrightarrow> interp_qform (qform_of_form frm)  i = interp_form frm (interp_apply_var Free i)"
by (induct frm) simp_all


  (* ----------------------------------------------------------------------  *)
subsection {*  Pushing substitutions and free variables*}
  (* ----------------------------------------------------------------------  *)


lemma rename_in_var_fv_var_isubsts [rule_format, simp]:
  "\<forall> x vs. x \<in> vs \<longrightarrow> rename_in_var x sbsts \<in> fv_var_isubsts vs sbsts"
apply (induct sbsts) 
apply clarsimp+
apply (rename_tac sb sbsts x vs)
apply (case_tac sb)
apply auto
done

(*--- Equality for renaming one variable ---*)

lemma fv_concept_rename_in_concept_one [simp]:  
   "fv_concept (rename_in_concept c [ISubst y2 y1]) = 
   (((fv_concept c) 
     - (if y1 = y2 then {} else if y2 \<in> fv_concept c then {y2} else {}))
     \<union> (if y1 = y2 then {} else if y2 \<in> fv_concept c then {y1} else {}))"
apply (induct c)
apply simp_all
apply fastforce
apply (rename_tac c sb)
apply (case_tac sb)
apply (rename_tac c sb r rop p)
apply (case_tac p)
apply auto
done


lemma fv_fact_rename_in_fact_one [simp]:  
   "fv_fact (rename_in_fact f [ISubst y2 y1]) = 
   (((fv_fact f) 
     - (if y1 = y2 then {} else if y2 \<in> fv_fact f then {y2} else {}))
     \<union> (if y1 = y2 then {} else if y2 \<in> fv_fact f then {y1} else {}))"
by (case_tac f) auto

lemma fv_form_rename_in_form_one [simp]:  
   "fv_form (rename_in_form f [ISubst y2 y1]) = 
   (((fv_form f) 
     - (if y1 = y2 then {} else if y2 \<in> fv_form f then {y2} else {}))
     \<union> (if y1 = y2 then {} else if y2 \<in> fv_form f then {y1} else {}))"
apply (induct f) 
apply simp_all
apply fastforce
apply (rename_tac f sb)
apply (case_tac sb)
apply (rename_tac f sb r rop p)
apply (case_tac p)
apply auto
done

(*--- Inclusion for renaming several variables ---*)

lemma fv_concept_rename_in_concept [rule_format]: 
"\<forall> sbsts. fv_concept (rename_in_concept c sbsts) \<subseteq> fv_var_isubsts (fv_concept c) sbsts"
apply (induct c)
prefer 7
(* SubstC *)
apply simp
apply (intro allI)
apply (rename_tac c sb sbsts)
apply (case_tac sb)
apply fastforce+
done

lemma fv_fact_rename_in_fact [rule_format]: 
"\<forall> sbsts. fv_fact (rename_in_fact f sbsts) \<subseteq> fv_var_isubsts (fv_fact f) sbsts"
apply (case_tac f)
apply simp_all
apply (rename_tac x c)
apply (intro allI)
apply (subgoal_tac "insert x (fv_concept c) = {x} \<union> fv_concept c")
apply (simp only: fv_var_isubsts_union)
apply (rule subset_trans)
apply (rule fv_concept_rename_in_concept)
apply blast+
done

lemma fv_form_rename_in_form [rule_format]:
 "\<forall> sbsts. fv_form (rename_in_form f sbsts) \<subseteq> fv_var_isubsts (fv_form f) sbsts"
apply (induct f)
apply clarsimp
apply (clarsimp simp add: fv_fact_rename_in_fact)
apply clarsimp
apply clarsimp apply fastforce
(* SubstFm *)
apply clarsimp apply (rule conjI) apply blast
apply (rename_tac f sb sbsts)
apply (case_tac sb)
apply fastforce
apply fastforce
done

lemma fv_qform_rename_in_qform [rule_format]:
 "\<forall> sbsts. is_quantif_free f \<longrightarrow>
   fv_qform (rename_in_qform f sbsts) \<subseteq> fv_var_isubsts (fv_qform f) sbsts"
apply (induct f)
apply clarsimp
apply (clarsimp simp add: fv_fact_rename_in_fact)
apply clarsimp
apply clarsimp apply fastforce
(* QuantifFm *)
apply clarsimp
(* QSubstFm *)
apply clarsimp apply (rule conjI) apply blast 
apply (rename_tac f sb sbsts)
apply (case_tac sb)
apply fastforce
apply fastforce
(* QRenameFm *)
apply (clarsimp split: rename.split)
apply fastforce
done

lemma fv_qform_rename_closure_qform_fv_var_isubsts [rule_format]:
  "\<forall> f. fv_qform (rename_closure_qform f sbsts) =
       fv_var_isubsts (fv_qform f) sbsts"
apply (induct sbsts)
apply simp_all
apply (rename_tac p sbsts)
apply (clarsimp split: rename.split)
done


lemma fv_qform_rename_in_qform_rename_closure_qform: 
  "is_quantif_free f \<Longrightarrow>
     fv_qform (rename_in_qform f sbsts) \<subseteq>
     fv_qform (rename_closure_qform f sbsts)"
by (simp add: fv_qform_rename_closure_qform_fv_var_isubsts)
   (erule fv_qform_rename_in_qform)

lemma is_closed_qform_rename_in_qform: "is_quantif_free f \<Longrightarrow> is_closed_qform f 
   \<Longrightarrow> is_closed_qform (rename_in_qform f [])"
by (insert fv_qform_rename_in_qform_rename_closure_qform [of f "[]"])
   (fastforce simp add: is_closed_qform_def)


lemma  extract_subst_Some_aux: "extract_subst fct = Some a \<Longrightarrow>
\<exists> x c sb. a = (x, c, sb) \<and> 
(push_subst_form (FactFm fct) sbsts = push_subst_form (FactFm (Inst x c)) (sb#sbsts))"
by (case_tac a) (simp split: subst.split)

lemma subst_height_form_push_subst_form_leq [rule_format]: 
 "\<forall> sbsts'. 
     subst_height_form (push_subst_form fm sbsts) sbsts'  
    \<le> subst_height_form fm (sbsts@sbsts')"
apply (induction fm sbsts  rule: push_subst_form.induct)
apply simp_all
prefer 2
(* BinopFm *)
apply (intro allI impI)
apply (rename_tac f1 f2 sbsts sbsts')
apply (drule_tac x=sbsts' in spec)
apply (drule_tac x=sbsts' in spec)
apply arith

(* FactFm *)
apply (rule allI)
apply (rename_tac fct sbsts sbsts')

apply (case_tac "extract_subst fct")
apply (case_tac sbsts)

(* subcase None / [] *)
apply (simp (no_asm_simp))

(* subcase None / # *)
apply (simp (no_asm_simp))
apply (rename_tac fct sbsts sbsts' sb sbsts'')
apply (subgoal_tac 
  "subst_height_form (push_subst_form (push_subst_fact fct sb) sbsts'') sbsts'
              \<le> subst_height_form (push_subst_fact fct sb) (sbsts'' @ sbsts') ")
  prefer 2 apply fast
apply (subgoal_tac "subst_height_form (push_subst_fact fct sb) (sbsts'' @ sbsts')
       < subst_height_fact fct (sb # sbsts'' @ sbsts')")
  prefer 2 apply (erule push_subst_fact_decr)
apply arith

(* subcase Some *)
apply (subgoal_tac "\<exists> x c sb. a = (x, c, sb) \<and> 
       (push_subst_form (FactFm fct) sbsts = push_subst_form (FactFm (Inst x c)) (sb#sbsts))")
  prefer 2 apply (erule extract_subst_Some_aux)
apply (elim exE conjE)
apply (simp only: extract_subst_Some split add: subst.split)
apply simp
done


lemma subst_height_form_push_subst_form_le_base: "extract_subst fct = None \<Longrightarrow>
       sbsts'' = [] \<Longrightarrow>
       subst_height_form
        (push_subst_form (push_subst_fact fct sb) []) sbsts'
       < subst_height_fact fct (sb # sbsts')"
apply (rule order.strict_trans1)
apply (subgoal_tac "subst_height_form (push_subst_form (push_subst_fact fct sb) []) sbsts'  
    \<le> subst_height_form (push_subst_fact fct sb) ([]@sbsts')")
  prefer 2 apply (rule subst_height_form_push_subst_form_leq)
apply simp
apply (erule push_subst_fact_decr)
done


lemma subst_height_form_push_subst_form_le [rule_format]: 
 "\<forall> sbsts'. sbsts \<noteq> [] \<longrightarrow>  
     subst_height_form (push_subst_form fm sbsts) sbsts'  
    < subst_height_form fm (sbsts@sbsts')"
apply (induction fm sbsts  rule: push_subst_form.induct)
apply simp_all
prefer 2
(* BinopFm *)
apply (intro allI impI)
apply (rename_tac f1 f2 sbsts sbsts')
apply simp
apply (drule_tac x=sbsts' in spec)
apply (drule_tac x=sbsts' in spec)
apply arith

(* SubstFm *)
apply (intro allI impI)
apply (rename_tac fct sbsts sbsts')

apply (case_tac "extract_subst fct")
apply (case_tac sbsts)

(* subcase None / [] *)
apply simp 

(* subcase None / # *)
apply (simp (no_asm_simp))
apply (rename_tac fct sbsts sbsts' sb sbsts'')

apply (case_tac "sbsts'' \<noteq> []")

(* case sbsts'' \<noteq> [] *)
apply (subgoal_tac 
  "subst_height_form (push_subst_form (push_subst_fact fct sb) sbsts'') sbsts'
              < subst_height_form (push_subst_fact fct sb) (sbsts'' @ sbsts') ")
  prefer 2 apply fast
apply (subgoal_tac "subst_height_form (push_subst_fact fct sb) (sbsts'' @ sbsts')
       < subst_height_fact fct (sb # sbsts'' @ sbsts')")
  prefer 2 apply (erule push_subst_fact_decr)
apply arith

(* case sbsts'' = [] *)
apply (simp add: subst_height_form_push_subst_form_le_base)

(* subcase Some *)
apply (subgoal_tac "\<exists> x c sb. a = (x, c, sb) \<and> 
       (push_subst_form (FactFm fct) sbsts = push_subst_form (FactFm (Inst x c)) (sb#sbsts))")
  prefer 2 apply (erule extract_subst_Some_aux)
apply (elim exE conjE)
apply (simp only: extract_subst_Some split add: subst.split)
apply simp
done


  (* ----------------------------------------------------------------------  *)
subsection {* Renaming and negation normal form *}
  (* ----------------------------------------------------------------------  *)

lemma rename_in_concept_neg_norm_concept [rule_format]:
"\<forall> b ren. (rename_in_concept (neg_norm_concept b c) ren) = (neg_norm_concept b (rename_in_concept c ren))"
by (induct c) auto

lemma rename_in_fact_neg_norm_fact [rule_format]:
"\<forall> b ren. (rename_in_fact (neg_norm_fact b f) ren) = (neg_norm_fact b (rename_in_fact f ren))"
by (case_tac f) (auto simp add: rename_in_concept_neg_norm_concept)

lemma rename_in_form_neg_norm_form [rule_format]:
"\<forall> b ren. (rename_in_form (neg_norm_form b f) ren) = (neg_norm_form b (rename_in_form f ren))"
by (induct f) (auto simp add: rename_in_fact_neg_norm_fact)
  
  (* ----------------------------------------------------------------------  *)
subsection {* Renaming and substitutions *}
  (* ----------------------------------------------------------------------  *)
(* TODO: this section has to be finished and tidied up *)


lemma rename_in_subst_id [simp]: "rename_in_subst sb [ISubst v1 v1] = sb"
by (induct sb) auto

lemma rename_in_concept_id [simp]: "rename_in_concept c [ISubst v1 v1] = c"
by (induct c) auto

lemma rename_in_fact_id [simp]: "rename_in_fact f [ISubst v1 v1] = f"
by (induct f) auto

lemma rename_in_form_id [simp]: "rename_in_form f [ISubst v1 v1] = f"
by (induct f) auto

lemma rename_in_var_id [simp]: "rename_in_var v [ISubst v1 v1] = v"
by (simp)

lemma rename_in_var_replace [simp]: "rename_in_var v1 [ISubst v1 v2] = v2"
by (simp)

lemma rename_in_form_push_rsubst_concept: "rename_in_form
        (push_rsubst_concept r rop (v1, v2) x c) ren =
       push_rsubst_concept r rop
        (rename_in_var v1 ren, rename_in_var v2 ren)
        (rename_in_var x ren) (rename_in_concept c ren)"
apply (induct c)
apply auto
apply (case_tac rop)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)
apply (rename_tac nro n c)
apply (case_tac nro)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)
apply (case_tac n)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)
apply (case_tac n)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)

apply (case_tac rop)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)
apply (case_tac rop)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)
done

lemma rename_in_form_push_csubst_concept:  "rename_in_form (push_csubst_concept cr rop v x c) ren =
       push_csubst_concept cr rop (rename_in_var v ren)
        (rename_in_var x ren) (rename_in_concept c ren)"
apply (induct c)
apply auto
apply (case_tac rop)
apply (auto simp add: nnf_IfThenElseFm_def IfThenElseFm_def 
      rename_in_form_neg_norm_form rename_in_concept_neg_norm_concept)
done

lemma rename_in_form_push_subst_fact [rule_format]:
  "\<forall> ren. (rename_in_form (push_subst_fact fct sb) ren) = 
          (push_subst_fact (rename_in_fact fct ren) (rename_in_subst sb ren))"
apply (case_tac fct)
apply (case_tac sb)
apply (auto simp add: rename_in_form_push_rsubst_concept rename_in_form_push_csubst_concept)
apply (case_tac sb)
apply (auto split : subst_op.split simp add: subst_AtomR_SDiff_def subst_AtomR_SAdd_def)
apply (case_tac sb)
apply auto
done


lemma extract_subst_rename_in_fact_None [simp]: 
  "extract_subst fct = None \<Longrightarrow> extract_subst (rename_in_fact fct ren) = None"
apply (case_tac fct)
apply auto
apply (rename_tac x c)
apply (case_tac c)
apply auto
done

  
lemma rename_in_form_push_subst_form [rule_format]:
 "\<forall> ren. rename_in_form (push_subst_form fm sbsts) ren =  
         push_subst_form (rename_in_form fm ren) (map (\<lambda> sb. rename_in_subst sb ren) sbsts)"
apply (induct fm sbsts rule: push_subst_form.induct)
apply simp_all

apply (rename_tac fct sbsts)
apply (case_tac "extract_subst fct")
apply (rule allI)
apply (subgoal_tac "extract_subst (rename_in_fact fct ren) = None")

(* extract_subst ... = None *)
apply simp
apply (case_tac "sbsts")
     apply simp
    
apply (simp add: rename_in_form_push_subst_fact)
apply simp

(* extract_subst ... = Some *)
apply (clarsimp simp add: extract_subst_Some)
done

(*<*)
end
(*>*)
