theory SemanticsProofs imports Semantics AuxilProofs CardProofs SyntaxProofs
begin

  (* ------------------------------------------------------------  *)
  (* Simp lemmas for basic interpretations *)
  (* ------------------------------------------------------------  *)
  
lemma interp_d_interp_r_modif [simp]:
  "interp_d (interp_r_modif r ri i) = interp_d i"
by (simp add: interp_r_modif_def)

lemma interp_d_interp_c_modif [simp]:
  "interp_d (interp_c_modif r ci i) = interp_d i"
by (simp add: interp_c_modif_def)

lemma interp_d_interp_i_modif [simp]:
  "interp_d (interp_i_modif r xi i) = interp_d i"
by (simp add: interp_i_modif_def)

lemma interp_d_interp_i_modif_list [rule_format, simp]:
  "\<forall> i. interp_d (interp_i_modif_list mds i) = interp_d i"
by (induct mds) simp+

lemma interp_d_interp_subst [simp]: "interp_d (interp_subst sb i)  = interp_d i"
by (case_tac sb) simp+

lemma interp_d_interp_rename [simp]: "interp_d (interp_rename sb i)  = interp_d i"
by (case_tac sb) simp+

lemma interp_c_interp_c_modif_eq [simp]: 
  "interp_c (interp_c_modif c ci i) c = ci"
by (simp add: interp_c_modif_def)

lemma interp_c_interp_c_modif_neq [simp]:
  "c' \<noteq> c \<Longrightarrow> (interp_c (interp_c_modif c ci i) c') = interp_c i c'"
by (simp add: interp_c_modif_def)

lemma interp_c_modif_interp_c [simp]: 
  "(interp_c_modif c (interp_c i c) i) = i"
by (simp add: interp_c_modif_def)

lemma interp_c_interp_i_modif [simp]:
  "interp_c (interp_i_modif r ri i) c = interp_c i c"
by (simp add: interp_i_modif_def)


lemma interp_c_interp_r_modif [simp]:
  "interp_c (interp_r_modif r ri i) c = interp_c i c"
by (simp add: interp_r_modif_def)

lemma interp_i_interp_c_modif [simp]: "interp_i (interp_c_modif c ci i) ni = interp_i i ni"
  by (simp add: interp_c_modif_def)

lemma interp_i_interp_r_modif [simp]:
  "interp_i (interp_r_modif r ri i) x = interp_i i x"
  by (simp add: interp_r_modif_def)

lemma interp_i_interp_i_modif_eq [simp]: 
  "interp_i (interp_i_modif v v' i) v = v'"
by (simp add: interp_i_modif_def)

lemma interp_i_interp_i_modif_neq [simp]: 
  "v \<noteq> v'' \<Longrightarrow> interp_i (interp_i_modif v v' i) v'' = (interp_i i v'')"
by (simp add: interp_i_modif_def)


lemma interp_r_interp_c_modif [simp]: "interp_r (interp_c_modif c ci i) r = interp_r i r"
by (simp add: interp_c_modif_def)

lemma interp_r_interp_i_modif [simp]:
  "interp_r (interp_i_modif v vi i) r = interp_r i r"
by (simp add: interp_i_modif_def)

lemma interp_r_interp_r_modif_eq [simp]:
  "interp_r (interp_r_modif r ri i) r = ri"
by (simp add: interp_r_modif_def)

lemma interp_r_interp_r_modif_neq [simp]:
  "r' \<noteq> r \<Longrightarrow> (interp_r (interp_r_modif r ri i) r') = interp_r i r'"
by (simp add: interp_r_modif_def)

lemma interp_r_modif_same [simp]: 
  "(interp_r_modif r (interp_r i r) i) = i"
by (simp add: interp_r_modif_def)

lemma interp_i_modif_same [simp]: 
  "interp_i i x = xi \<Longrightarrow> (interp_i_modif x xi i) = i"
  by (simp add: interp_i_modif_def fun_eq_iff)

lemma well_formed_interp_nonempty_d:
  "well_formed_interp i \<Longrightarrow> interp_d i \<noteq> {}"
by (simp add: well_formed_interp_def)

lemma well_formed_interp_interp_c:
  "well_formed_interp i \<Longrightarrow> x \<in> interp_c i r \<Longrightarrow> x \<in> interp_d i"
by (auto simp add: well_formed_interp_def)

lemma well_formed_interp_interp_r_right:
  "well_formed_interp i \<Longrightarrow> (x, y) \<in> interp_r i r \<Longrightarrow> x \<in> interp_d i"
by (auto simp add: well_formed_interp_def)

lemma well_formed_interp_interp_r_left:
  "well_formed_interp i \<Longrightarrow> (x, y) \<in> interp_r i r \<Longrightarrow> y \<in> interp_d i"
by (auto simp add: well_formed_interp_def)

lemma well_formed_interp_interp_i_interp_d [simp]:
 "well_formed_interp i \<Longrightarrow> interp_i i x \<in> interp_d i"
by (simp add: well_formed_interp_def)

(* -------------------------------------------------------------------------------*)
(* preservation of well_formed_interp *)
lemma well_formed_interp_interp_r_modif_interpRO_r [simp]:
  "well_formed_interp i \<Longrightarrow> well_formed_interp (interp_r_modif r (interpRO_r rop nr p i) i)"
apply (simp add: well_formed_interp_def interp_r_modif_def)
apply (case_tac p)
apply (case_tac rop)
apply fastforce+
done

lemma well_formed_interp_interp_c_modif_interpRO_c [simp]:
  "well_formed_interp i \<Longrightarrow> well_formed_interp (interp_c_modif c (interpRO_c rop c v i) i)"
apply (simp add: well_formed_interp_def interp_c_modif_def)
apply (case_tac rop)
apply fastforce+
done

lemma well_formed_interp_interp_i_modif_interp_i [simp]:
  "well_formed_interp i \<Longrightarrow> well_formed_interp (interp_i_modif x (interp_i i y) i)"
by (simp add: well_formed_interp_def interp_i_modif_def)

lemma well_formed_interp_interp_i_modif_interp_c [simp]:
  "well_formed_interp i \<Longrightarrow> xi \<in> interp_c i c \<Longrightarrow> 
   well_formed_interp (interp_i_modif x xi i)"
by (fastforce simp add: well_formed_interp_def interp_i_modif_def)

lemma well_formed_interp_interp_subst [simp]: 
  "well_formed_interp i \<Longrightarrow> well_formed_interp (interp_subst sb i)"
by (case_tac sb) simp_all

lemma well_formed_interp_interp_rename [simp]: 
  "well_formed_interp i \<Longrightarrow> well_formed_interp (interp_rename sb i)"
by (case_tac sb) simp_all

lemma well_formed_interp_interp_subst_closure [simp]: 
  "\<forall> i. well_formed_interp i \<longrightarrow> well_formed_interp (interp_subst_closure sbsts i)"
by (induct sbsts) auto

lemma well_formed_interp_interp_rename_closure [simp]: 
  "\<forall> i. well_formed_interp i \<longrightarrow> well_formed_interp (interp_rename_closure sbsts i)"
by (induct sbsts) auto

(* interpretation of special forms *)

lemma interp_form_IfThenElseFm [simp]: "interp_form (IfThenElseFm c a b) = 
  (lift_ite (interp_form c) (interp_form a) (interp_form b))"
by (simp add: IfThenElseFm_def lift_ite_def lift_impl_def fun_eq_iff)


  (* the traditional point-wise definition of number restrictions *)
lemma "(Range (rel_restrict R {x} (interp_concept c i))) = {y. ((x,y) \<in> R \<and> y \<in> (interp_concept c i))}"
by (simp add: rel_restrict_def) blast


  (* The lemmas Bottom_NumRestrC and Top_NumRestrC
  show that the only relevant concept constructors are AtomC, BinopC, NegC, NumRestrC, SubstC
 *)

  (* Bottom and Top are equivalent to a NumRestrC-expression, 
  but cannot be defined as abbreviations (unbound vars r and c).
  *)
lemma Bottom_NumRestrC: "interp_concept Bottom i = interp_concept (NumRestrC Lt 0 r c) i"
by simp

lemma Top_NumRestrC: "interp_concept Top i = interp_concept (NumRestrC Ge 0 r c) i"
by simp


lemma interp_concept_SomeC:
  "well_formed_interp i \<Longrightarrow>
  (x \<in> interp_concept (SomeC r c) i) = (\<exists>y. ((x,y) \<in>(interp_r i r) \<and> y \<in> (interp_concept c i)))"
apply (clarsimp simp add: card_ge_def well_formed_interp_def)
apply (subgoal_tac "\<forall> n. (Suc 0 \<le> n) = (0 < n)")
apply (auto simp add: rel_restrict_def card_gt_0_iff dest: non_finite_non_empty)
done

lemma interp_concept_AllC:
  "well_formed_interp i \<Longrightarrow>
  (x \<in> interp_concept (AllC r c) i) = (x \<in> interp_d i \<and> (\<forall> y. ((x,y) \<in>(interp_r i r) \<longrightarrow> y \<in> (interp_concept c i))))"
apply (clarsimp simp add: card_lt_def)
apply (clarsimp simp add: card_eq_0_iff)
apply (auto simp add: rel_restrict_def card_gt_0_iff dest: non_finite_non_empty)
apply (subgoal_tac "(Range (interp_r i r \<inter> {x} \<times> - interp_concept c i)) = {}")
apply auto
done

lemma interp_concept_SomeC_NumRestrC: 
  "interp_concept (SomeC r c) i =
   interp_concept ([\<ge>] 1 r c) i"
by simp

lemma well_formed_interp_rel_restrinct_interp_r: 
"well_formed_interp i \<Longrightarrow>  
rel_restrict (interp_r i r) A B = 
rel_restrict (interp_r i r) (A \<inter> (interp_d i)) (B \<inter> (interp_d i))"
by (auto simp add: well_formed_interp_def rel_restrict_def)

lemma well_formed_interp_rel_restrinct_interp_r_minus [simp]: 
"well_formed_interp i \<Longrightarrow>  
rel_restrict (interp_r i r) A (interp_d i - B) = 
rel_restrict (interp_r i r) A (- B)"
by (auto simp add: well_formed_interp_def rel_restrict_def)

lemma well_formed_interp_rel_restrinct_interp_r_minus_union [simp]: 
"well_formed_interp i \<Longrightarrow>  
rel_restrict (interp_r i r) A (- interp_d i \<union> B) = 
rel_restrict (interp_r i r) A (B)"
by (auto simp add: well_formed_interp_def rel_restrict_def)

lemma interp_concept_AllC_NumRestrC: 
  "well_formed_interp i \<Longrightarrow>
  interp_concept (AllC r c) i =
   interp_concept ([<] 1 r (NegC c)) i"
by simp


lemma interp_concept_NumRestrC_AllC: 
  "well_formed_interp i \<Longrightarrow>
  interp_concept ([<] 1 r c) i =
  interp_concept (AllC r (NegC c)) i"
  by simp

lemma interp_fact_SomeC_NumRestrC: 
  "interp_fact (Inst x (SomeC r c)) i =
   interp_fact (Inst x ([\<ge>] 1 r c)) i"
by simp

lemma interp_fact_AllC_NumRestrC: 
  "well_formed_interp i \<Longrightarrow>
  interp_fact (Inst x (AllC r c)) i =
   interp_fact (Inst x ([<] 1 r (NegC c))) i"
by simp


  (* ------------------------------------------------------------  *)
  (* Explicit substitutions *)
  (* ------------------------------------------------------------  *)

  (* Concepts: Pushing explicit substitution into constructors *)

lemma interp_concept_SubstC_BinopC:
  "interp_concept (SubstC (BinopC bop c1 c2) sb) i = 
  interp_concept (BinopC bop (SubstC c1 sb) (SubstC c2 sb)) i"
by (case_tac bop) simp_all

lemma interp_concept_SubstC_NegC:
  "interp_concept (SubstC (NegC c) sb) i = 
  interp_concept (NegC (SubstC c sb)) i"
by simp

lemma interp_concept_SubstC_NumRestrC_other_role:
  "r \<noteq> r' \<Longrightarrow> 
  interp_concept (SubstC (NumRestrC nro n r' c) (RSubst r rop p)) i = 
  interp_concept (NumRestrC nro n r' (SubstC c (RSubst r rop p))) i"
by simp

  (* Forms: Pushing explicit substitution into constructors *)
  (* case FactFm is dealt with in lemma interp_form_SubstFm_FactFm_Inst ff.  *)

lemma interp_form_SubstFm_NegFm:
  "interp_form (SubstFm (NegFm f) sb) i = 
  interp_form (NegFm (SubstFm f sb)) i"
by simp

lemma interp_form_SubstFm_ConjFm:
  "interp_form (SubstFm (BinopFm bop f1 f2) sb) i = 
  interp_form (BinopFm bop (SubstFm f1 sb) (SubstFm f2 sb)) i"
by (case_tac sb) ((case_tac bop), simp_all)+



  (* Pushing explicit substitution into NumRestrC
  *)
lemma interp_fact_NumRestrC_Neq_SAdd_expl_subst:
  "interp_form (NegFm (ConjFm (ConjFm
  (FactFm (Eq True x v1)) 
  (FactFm (Inst v2 (SubstC c (RSubst r SAdd (v1, v2))))))
  (FactFm (AtomR False r v1 v2)))) i
  \<Longrightarrow> interp_fact (Inst x (SubstC (NumRestrC nro n r c) (RSubst r SAdd (v1, v2)))) i =
     interp_fact (Inst x (NumRestrC nro n r (SubstC c (RSubst r SAdd (v1, v2))))) i"
apply (simp only: interp_form.simps interp_binopFm.simps de_Morgan_conj)
apply (elim disjE)
apply (clarsimp simp add: rel_restrict_diff rel_restrict_insert interp_r_modif_def insert_absorb)+
done

lemma interp_numres_ord_Eq_SAdd:
  "\<lbrakk>interp_i i v2 \<in> ci; (interp_i i v1, interp_i i v2) \<notin> interp_r i r \<rbrakk>
  \<Longrightarrow> interp_numres_ord nro
        (Range (rel_restrict (insert (interp_i i v1, interp_i i v2) (interp_r i r)) {interp_i i v1} ci))
        (Suc n) =
       interp_numres_ord nro (Range (rel_restrict (interp_r i r) {interp_i i v1} ci)) n"
apply (simp add: rel_restrict_diff rel_restrict_insert)
apply (subgoal_tac "interp_i i v2 \<notin> Range (rel_restrict (interp_r i r) {interp_i i v1} ci)")
  prefer 2 apply (simp add: rel_restrict_def) apply fastforce
apply (case_tac nro)
apply (simp add: card_lt_Suc_insert)
apply (simp add: card_ge_Suc_insert)
done

lemma interp_numres_ord_Eq_SDiff:
  "\<lbrakk>interp_i i v2 \<in> ci; (interp_i i v1, interp_i i v2) \<in> interp_r i r\<rbrakk>
    \<Longrightarrow> interp_numres_ord nro
        (Range (rel_restrict (interp_r i r - {(interp_i i v1, interp_i i v2)}) {interp_i i v1} ci)) n =
       interp_numres_ord nro (Range (rel_restrict (interp_r i r) {interp_i i v1} ci)) (Suc n)"
apply (simp add: rel_restrict_diff rel_restrict_insert )
apply (clarsimp simp add: rel_restrict_remove)
apply (subgoal_tac "interp_i i v2 \<in> Range (rel_restrict (interp_r i r) {interp_i i v1} ci)")
  prefer 2 apply (fastforce simp add: rel_restrict_def)
apply (case_tac nro)
apply (simp add: card_lt_Suc_diff)
apply (simp add: card_ge_Suc_diff)
done


end

