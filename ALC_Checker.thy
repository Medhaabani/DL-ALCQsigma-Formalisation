theory ALC_Checker imports ALC_Tableau New_Var (*ALC_Implementation *) VariablesProofs

begin

definition nnms_to_substs:: "'ni list \<Rightarrow>  'ni var rename list" where 
  "nnms_to_substs nnms = List.map (\<lambda> (n, vn). (ISubst (Bound n) (Free vn))) (List.zip [0 ..< length nnms] nnms)"

definition nnms_to_substs_inv:: "'ni list \<Rightarrow> 'ni var rename list" where 
  "nnms_to_substs_inv nnms = List.map (\<lambda> (n, vn). (ISubst (Free vn) (Bound n))) (List.zip [0 ..< length nnms] nnms)"

definition nnms_to_substs_bounded:: "nat \<Rightarrow> nat \<Rightarrow> 'ni list \<Rightarrow> 'ni var rename list" where 
  "nnms_to_substs_bounded l u nnms = List.map (\<lambda> (n, vn). (ISubst (Bound n) (Free vn))) (List.zip [l ..< u] nnms)"

definition nnms_to_substs_inv_bounded:: "nat \<Rightarrow> nat \<Rightarrow> 'ni list \<Rightarrow> 'ni var rename list" where 
  "nnms_to_substs_inv_bounded l u nnms = List.map (\<lambda> (n, vn). (ISubst (Free vn) (Bound n))) (List.zip [l ..< u] nnms)"

lemma nnms_to_substs_sbst_bounded: 
  "nnms_to_substs nnms = nnms_to_substs_bounded 0 (0 + length nnms) nnms"
by (simp add: nnms_to_substs_def nnms_to_substs_bounded_def)

lemma nnms_to_substs_sbst_inv_bounded: 
  "nnms_to_substs_inv nnms = nnms_to_substs_inv_bounded 0 (0 + length nnms) nnms"
by (simp add: nnms_to_substs_inv_def nnms_to_substs_inv_bounded_def)

(*  nnms: new names; fvs: original free variables of f *)
fun free_univ_bound_list :: 
  "('nr, 'nc, ('ni::new_var_list_class)) qform \<Rightarrow> 'ni list \<Rightarrow> 'ni list \<Rightarrow>  ('nr, 'nc, 'ni) qform" where

    "free_univ_bound_list (QuantifFm QAll v f) nnms fvs = 
     (let nv_name = new_var_list (nnms @ fvs) v in
      free_univ_bound_list f (nv_name#nnms) fvs)"

  | "free_univ_bound_list f nnms fvs = rename_closure_qform f (nnms_to_substs nnms)"


definition free_prenex_form_list :: "('nr, 'nc, ('ni::new_var_list_class)) qform \<Rightarrow> ('nr, 'nc, 'ni) form" where
  "free_prenex_form_list f = 
     form_of_qform 
     (rename_in_qform
       (free_univ_bound_list (lift_bound f) [] (List.map name_of_free (fv_qform_list f)))
       [])"
 
definition free_prenex_form_list_string :: 
    "('nr, 'nc, String.literal) qform \<Rightarrow> ('nr, 'nc, String.literal) form" where
  "free_prenex_form_list_string = free_prenex_form_list" 


  (* ------------------------------------------------------------  *)
  (* Properties of free_univ_bound_list *)
  (* ------------------------------------------------------------  *)

lemma is_quantif_free_subst_closure_qform [rule_format, simp]:
 "\<forall> f. is_quantif_free (subst_closure_qform f sbsts) = is_quantif_free f"
by (induct sbsts) auto

lemma is_quantif_free_rename_closure_qform [rule_format, simp]:
 "\<forall> f. is_quantif_free (rename_closure_qform f sbsts) = is_quantif_free f"
by (induct sbsts) auto

lemma is_quantif_free_free_univ_bound_list [rule_format,simp]:
  "\<forall>  nnms fvs. is_univ_quantif True f \<longrightarrow> is_prenex_form f 
  \<longrightarrow> is_quantif_free (free_univ_bound_list f nnms fvs)"
apply (induct f)
prefer 5
(* QuantifFm *)
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply (clarsimp simp del: rename_in_qform.simps simp add: Let_def)
apply (simp_all del: rename_in_qform.simps)
done


definition "bound_closing f (nnms::('i::new_var_list_class) list) fvs =
  (distinct (nnms @ fvs) \<and> (Set.filter is_free (fv_qform f) = Free ` (set fvs)))"


lemma filter_is_free_close_quantif:
  "Set.filter is_free (close_quantif ` (A - {Bound 0})) = Set.filter is_free A"
by (simp add: Set.filter_def image_def)
   (fastforce simp add: close_quantif_case split: var.split)+ 

lemma close_quantif_image_Bound [simp]: "close_quantif ` Bound ` {Suc 0 ..< (Suc n)} = Bound ` {0 ..< n}"
by (fastforce simp add:  atMost_def image_def)
 

lemma bound_closing_AllFm:
  "bound_closing f (new_var_list (nnms @ fvs) n # nnms) fvs = 
  bound_closing (AllFm n f) nnms fvs"
apply (simp add: bound_closing_def)
apply (insert new_var_list_class_class.new_var_gen_list  [of "nnms @ fvs" n])
apply simp
apply (simp add: filter_is_free_close_quantif)
done

lemma bound_closing_AllFm_new_var_list:
  "bound_closing (AllFm n f) nnms fvs \<Longrightarrow>  
   bound_closing f (new_var_list (nnms @ fvs) n # nnms)  fvs"
by (simp add: bound_closing_AllFm)

lemma interp_bound_interp_i_update_vartype: 
  "interp_bound (interp_i i (Bound 0)) (interp_i_update_vartype (\<lambda> i y. i (lift_var 0 y)) i) = i"
apply (simp add: interp_bound_def)
apply (case_tac i)
apply (simp add: interp_i_update_vartype_def comp_def fun_eq_iff)
apply (clarsimp simp add: lift_var_drop_var)
done

lemma well_formed_interp_interp_i_update_vartype: 
  "well_formed_interp i \<Longrightarrow>
       well_formed_interp (interp_i_update_vartype (\<lambda>i y. i (f y)) i)"
by (simp add: well_formed_interp_def interp_i_update_vartype_def)

lemma valid_qform_AllFm: "valid_qform TYPE('d) (AllFm n f) = valid_qform TYPE('d) f"
apply (rule iffI)
apply (clarsimp simp add: valid_qform_def)
apply (drule_tac x="(interp_i_update_vartype (\<lambda> i y. i (lift_var 0 y)) i)" in spec)
apply (drule mp) apply (erule well_formed_interp_interp_i_update_vartype)
apply (drule_tac x="interp_i i (Bound 0)" in bspec) 
apply (simp add: well_formed_interp_def interp_i_update_vartype_def)
apply (simp add: interp_bound_interp_i_update_vartype)
apply (clarsimp simp add: valid_qform_def)
done


lemma nnms_to_substs_inv_bounded_Cons:
  "(nnms_to_substs_inv_bounded l (Suc (l + length nnms)) (vn # nnms)) = 
   (ISubst (Free vn) (Bound l)) # (nnms_to_substs_inv_bounded (Suc l) (Suc (l + length nnms)) nnms)"
apply (simp add: nnms_to_substs_inv_bounded_def del: upt_Suc)
apply (subgoal_tac "[l..<Suc (l + length nnms)] = l # [Suc l..<Suc (l + length nnms)]")
   prefer 2 apply (simp add: upt_rec)
apply (simp del: upt_Suc)
done

lemma nnms_to_substs_bounded_Nil [simp]:
  "(nnms_to_substs_bounded l l []) = []"
by (simp add: nnms_to_substs_bounded_def)
 
lemma nnms_to_substs_bounded_Cons:
  "(nnms_to_substs_bounded l (Suc (l + length nnms)) (vn # nnms)) = 
   (ISubst (Bound l) (Free vn)) # (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms)"
apply (simp add: nnms_to_substs_bounded_def del: upt_Suc)
apply (subgoal_tac "[l..<Suc (l + length nnms)] = l # [Suc l..<Suc (l + length nnms)]")
   prefer 2 apply (simp add: upt_rec)
apply (simp del: upt_Suc)
done

lemma replace_var_invert: "w \<noteq> v1 \<Longrightarrow> 
 replace_var (ISubst v1 v2) (replace_var (ISubst v2 v1) w) = w"
by clarsimp

lemma rename_in_var_replace_var [rule_format]: "\<forall> v sb. 
   (isubst_dom sb) \<inter> (\<Union> (isubst_dom ` set sbsts)) = {} \<longrightarrow>
   (isubst_dom sb) \<inter> (\<Union> (isubst_ran ` set sbsts)) = {} \<longrightarrow>
   (isubst_ran sb) \<inter> (\<Union> (isubst_dom ` set sbsts)) = {} \<longrightarrow>
   rename_in_var (replace_var sb v) sbsts = replace_var sb (rename_in_var v sbsts)"
apply (induct sbsts)
apply clarsimp+
apply (case_tac a)
apply (case_tac sb)
apply clarify
apply (rename_tac a sbsts v sb x1 x2 y1 y2)
apply (subgoal_tac "(replace_var (ISubst x1 x2) (replace_var (ISubst y1 y2) v)) =
  (replace_var (ISubst y1 y2) (replace_var (ISubst x1 x2) v))")
   prefer 2 apply clarsimp 
apply (simp only:)
apply (drule_tac x="replace_var (ISubst x1 x2) v" in spec)
apply (drule_tac x="ISubst y1 y2" in spec)
apply fastforce
done

lemma subst_var_contained [rule_format]: 
  "\<forall> v. rename_in_var v sbsts \<in> insert v  (\<Union> (isubst_ran ` set sbsts))"
apply (induct sbsts)
apply simp
apply (rename_tac sb sbsts)
apply (case_tac sb)
apply fastforce
done

lemma isubst_dom_set_nnms_to_substs_bounded [rule_format]:
 "\<forall> l. \<Union> (isubst_dom ` set (nnms_to_substs_bounded l (l + length nnms) nnms)) =
  Bound ` set [l ..< (l + length nnms)]"
apply (induct nnms)
apply simp
apply (simp add: nnms_to_substs_bounded_Cons)
apply clarify
apply (drule_tac x="Suc l" in spec)
apply clarsimp
apply fastforce
done

lemma isubst_ran_set_nnms_to_substs_bounded [rule_format]:
 "\<forall> l. \<Union> (isubst_ran ` set (nnms_to_substs_bounded l (l + length nnms) nnms)) =
  Free ` set nnms"
apply (induct nnms)
apply simp
apply (simp add: nnms_to_substs_bounded_Cons)
apply clarify
apply (drule_tac x="Suc l" in spec)
apply clarsimp
done

lemma  Bound_disjoint_inter: "{Bound l} \<inter> Bound ` set [Suc l ..< n] = {}"
by (simp add: image_def)

lemma  Bound_Free_inter: "{Bound l} \<inter> Free ` A = {}"
by (fastforce simp add: image_def)

lemma  Free_Bound_inter: "{Free l} \<inter> Bound ` A = {}"
by (fastforce simp add: image_def)

lemma interp_subst_closure_nnms_to_substs_bounded [rule_format]:
"distinct nnms \<longrightarrow>
      (\<forall> v. (v \<notin>  Free ` (set nnms) \<longrightarrow>  
       (\<forall> l. (interp_i i (rename_in_var (rename_in_var v (nnms_to_substs_bounded l (l + length nnms) nnms))
                            (nnms_to_substs_inv_bounded l (l + length nnms) nnms))
            = interp_i i v))))"
apply (induct nnms)
apply (clarsimp simp add: nnms_to_substs_bounded_def nnms_to_substs_inv_bounded_def)
apply clarsimp
apply (rename_tac n nnms v l)
apply (drule_tac x="v" in spec)
apply simp

apply (drule_tac x="Suc l" in spec)
apply simp
apply (simp only: nnms_to_substs_bounded_Cons nnms_to_substs_inv_bounded_Cons)
apply (simp (no_asm_use) only: rename_in_var.simps)
apply (subgoal_tac "(rename_in_var (replace_var (ISubst (Bound l) (Free n)) v) 
                       (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms)) = 
              (replace_var (ISubst (Bound l) (Free n))
               (rename_in_var v (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms)))")
  prefer 2 
  apply (subgoal_tac "(Suc (l + length nnms)) = (Suc l + length nnms)") prefer 2 apply simp
  apply (rule rename_in_var_replace_var) 
  apply (simp only:  isubst_dom_set_nnms_to_substs_bounded isubst_dom.simps Bound_disjoint_inter) 
  apply (simp only:  isubst_ran_set_nnms_to_substs_bounded isubst_dom.simps Bound_Free_inter) 
  apply (simp only:  isubst_dom_set_nnms_to_substs_bounded isubst_ran.simps Free_Bound_inter)
apply (simp only:)

apply (subgoal_tac "(replace_var (ISubst (Free n) (Bound l))
            (replace_var (ISubst (Bound l) (Free n))
              (rename_in_var v (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms)))) 
              = (rename_in_var v (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms))")
apply simp

apply (rule replace_var_invert)
apply (subgoal_tac "rename_in_var v
        (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms) 
          \<in> insert v (\<Union> (isubst_ran ` set  
               (nnms_to_substs_bounded (Suc l) (Suc (l + length nnms)) nnms)))")
   prefer 2 apply (rule subst_var_contained)
apply (subgoal_tac "(Suc (l + length nnms)) = (Suc l + length nnms)") prefer 2 apply simp
apply (simp only:  isubst_ran_set_nnms_to_substs_bounded isubst_dom.simps) 
by (metis image_iff insert_iff var.inject(1))

lemma valid_qform_subst_closure_qform:
"is_quantif_free f\<Longrightarrow>
bound_closing f nnms fvs \<Longrightarrow> 
valid_qform TYPE('d) (rename_closure_qform f (nnms_to_substs nnms)) = 
valid_qform TYPE('d) f"
apply (clarsimp simp add: bound_closing_def)
apply (simp add: valid_qform_def)
apply (simp add: interp_qform_rename_closure_qform)
apply (rule iffI)
defer
apply clarsimp

apply clarsimp
apply (drule_tac x="interp_rename_closure (nnms_to_substs_inv nnms) i" in spec)
apply simp
apply (subgoal_tac "interp_i_equivalent (interp_rename_closure
                     (nnms_to_substs nnms) (interp_rename_closure (nnms_to_substs_inv nnms) i))
                     i (fv_qform f)")
apply (simp add: interp_i_equivalent_interp_qform)
apply (clarsimp simp add: interp_i_equivalent_def)
apply (simp only: nnms_to_substs_sbst_bounded nnms_to_substs_sbst_inv_bounded)
apply (erule interp_subst_closure_nnms_to_substs_bounded)
apply fastforce
done

lemma valid_qform_impl_valid_qform_free_univ_bound_list [rule_format]:
"\<forall> nnms. is_univ_quantif True f \<longrightarrow> is_prenex_form f \<longrightarrow> bound_closing f nnms fvs 
  \<longrightarrow> valid_qform TYPE('d) f 
   \<longrightarrow> valid_qform TYPE('d) (free_univ_bound_list f nnms fvs)"
apply (induct f)
prefer 5
(* AllFm *)
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply clarsimp
apply (drule_tac x="(new_var_list (nnms @ fvs) ni # nnms)" in spec)
apply (frule bound_closing_AllFm_new_var_list)
apply (simp add: valid_qform_AllFm)

(* ExFm *)
apply simp

(* others *)
apply (clarsimp simp del: rename_in_qform.simps simp add: valid_qform_subst_closure_qform)+
done


lemma valid_qform_free_univ_bound_list_impl_valid_qform [rule_format]:
"\<forall> nnms. is_univ_quantif True f \<longrightarrow> is_prenex_form f \<longrightarrow> bound_closing f nnms fvs 
   \<longrightarrow> valid_qform TYPE('d) (free_univ_bound_list f nnms fvs) 
   \<longrightarrow> valid_qform TYPE('d) f"
  
apply (induct f)
prefer 5
(* AllFm *) 
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply clarsimp
apply (drule_tac  x=" (new_var_list (nnms @ fvs) ni # nnms)" in spec) 
apply (simp add: bound_closing_AllFm)
apply (simp add: valid_qform_AllFm)

(* others *)
apply (clarsimp simp del: rename_in_qform.simps simp add: valid_qform_subst_closure_qform)+
done

lemma valid_qform_free_univ_bound_list_eq_valid_qform [rule_format]:
  "is_univ_quantif True f \<Longrightarrow> is_prenex_form f \<Longrightarrow> bound_closing f nnms fvs 
   \<Longrightarrow> valid_qform TYPE('d) (free_univ_bound_list f nnms fvs) = 
   valid_qform TYPE('d) f"
by (fast intro: valid_qform_impl_valid_qform_free_univ_bound_list
  valid_qform_free_univ_bound_list_impl_valid_qform)

   
  (* ------------------------------------------------------------  *)
  (* Properties of form_of_qform *)
  (* ------------------------------------------------------------  *)

lemma interp_apply_var_Free_name_of_free [simp]:
  "interp_apply_var Free (interp_apply_var name_of_free i) = i"
by (simp add: interp_apply_var_def interp_i_update_vartype_def comp_def)

lemma interp_apply_var_name_of_free_Free [simp]: 
  "(\<forall> v \<in> A. is_free v) 
  \<Longrightarrow> interp_i_equivalent (interp_apply_var name_of_free (interp_apply_var Free i)) i A"
apply (clarsimp simp add: interp_apply_var_def interp_i_update_vartype_def comp_def interp_i_equivalent_def)
apply (rename_tac v)
apply (case_tac v)
apply auto
done

lemma interp_concept_apply_var_concept_free [rule_format]:
"\<forall> i. 
       (\<forall> v \<in> fv_concept c. is_free v) \<longrightarrow> 
       interp_concept (apply_var_concept name_of_free c) i =
            interp_concept c (interp_apply_var name_of_free i)"
apply (induct c)
apply simp_all
apply clarsimp
apply (rename_tac c sb i)

apply (rule interp_i_equivalent_interp_concept) 
apply (rule interp_apply_var_interp_subst_inj_on)
apply (fast intro: inj_on_name_of_free)
done

lemma interp_fact_apply_var_fact_free:
  "(\<forall> v \<in> fv_fact fact. is_free v) \<Longrightarrow>
       interp_fact (apply_var_fact name_of_free fact) i =
            interp_fact fact (interp_apply_var name_of_free i)"
apply (case_tac fact)
apply simp_all
apply (rename_tac n c)
apply (subgoal_tac "interp_concept (apply_var_concept name_of_free c) i = interp_concept c (interp_apply_var name_of_free i)")
apply clarsimp+
apply (rule interp_concept_apply_var_concept_free)
apply fast
done


lemma interp_form_apply_var_form_free [rule_format]:
 "\<forall> i. is_quantif_free f \<longrightarrow>  is_rename_free_qform f
 \<longrightarrow> is_closed_qform f
 \<longrightarrow> interp_form (form_of_qform f) i = interp_qform f (interp_apply_var name_of_free i)" 
apply (induct f)
apply (simp_all add: is_closed_qform_def)
apply (clarsimp simp add: interp_fact_apply_var_fact_free)

apply (rename_tac f sb)
apply clarsimp
apply (rule interp_i_equivalent_interp_qform) prefer 2 apply assumption
apply (rule interp_apply_var_interp_subst_inj_on)
apply (fast intro: inj_on_name_of_free)
done

lemma interp_form_form_of_qform_apply_var_form_free:
  "is_quantif_free f \<Longrightarrow> is_rename_free_qform f 
  \<Longrightarrow> is_closed_qform f
  \<Longrightarrow> interp_form (form_of_qform f) (interp_apply_var Free i) = interp_qform f i"
apply (insert interp_form_apply_var_form_free [of f  "(interp_apply_var Free i)"])
apply simp
apply (rule interp_i_equivalent_interp_qform) prefer 2 apply assumption
apply (simp add: is_closed_qform_def)
done

lemma valid_form_form_of_qform:
  "is_quantif_free f \<Longrightarrow> is_rename_free_qform f 
  \<Longrightarrow> is_closed_qform f
  \<Longrightarrow> valid_form TYPE('d) (form_of_qform f) = valid_qform TYPE('d) f"
apply (simp add: valid_form_def valid_qform_def)
apply (rule iffI)
apply clarsimp
apply (drule_tac x="(interp_apply_var Free i)" in spec)
apply (simp add: interp_form_form_of_qform_apply_var_form_free)

apply clarsimp
apply (subgoal_tac "interp_form (form_of_qform f) (interp_apply_var Free (interp_apply_var name_of_free i))")
apply simp
apply (subgoal_tac "well_formed_interp (interp_apply_var name_of_free i)") prefer 2 apply simp
apply (simp del: interp_apply_var_Free_name_of_free add: interp_form_form_of_qform_apply_var_form_free)
done


lemma valid_qform_lift_bound [simp]: "valid_qform TYPE('d) (lift_bound f) = valid_qform TYPE('d) f"
by (simp add: valid_qform_def)

lemma is_closed_qform_QConstFm [simp]: "is_closed_qform (QConstFm cn)"
by (simp add: is_closed_qform_def)

lemma is_closed_qform_QNegFm [simp]: "is_closed_qform (QNegFm f) = is_closed_qform f"
by (simp add: is_closed_qform_def)

lemma is_closed_qform_QBinopFm [simp]: 
"is_closed_qform (QBinopFm bop f1 f2) = (is_closed_qform f1 \<and> is_closed_qform f2)"
by (fastforce simp add: is_closed_qform_def)


lemma fv_subst_lift_subst [rule_format, simp]:
  "\<forall> n. fv_subst (lift_subst n sb) = lift_var n ` fv_subst sb"
apply (case_tac sb)
apply (rename_tac r rop v1v2)
apply (case_tac v1v2)
apply simp_all
done

lemma fv_rename_lift_rename [rule_format, simp]:
  "\<forall> n. fv_rename (lift_rename n sb) = lift_var n ` fv_rename sb"
by (case_tac sb) simp

lemma isubst_dom_lift_rename [rule_format, simp]:
  "isubst_dom (lift_rename n sb) = lift_var n ` (isubst_dom  sb)"
  apply (case_tac sb)
  apply simp
done

lemma fv_concept_lift_concept [rule_format, simp]:
   "\<forall> n. fv_concept (lift_concept n c) = lift_var n ` fv_concept c"
apply (induct c)
apply simp_all
apply (clarsimp simp add: image_Un)
apply (clarsimp simp add: image_Un image_set_diff)
done

lemma fv_fact_lift_fact [rule_format, simp]:
  "\<forall> n. fv_fact (lift_fact n f) = lift_var n ` fv_fact f"
by (induct f) simp_all

lemma lift_var_0_image [simp]: 
  "(lift_var 0 ` F - {Bound 0}) = lift_var 0 ` F"
by (auto simp add: image_def)

lemma lift_var_Suc_image: 
  "(lift_var (Suc n) ` F - {Bound 0}) = lift_var (Suc n) ` (F - {Bound 0})"
by (simp add: image_set_diff)

lemma close_quantif_comp_lift_var_0 [simp]:
  "(close_quantif \<circ> lift_var 0) = id"
  apply (simp add: fun_eq_iff comp_def close_quantif_case split: var.split)
  apply (intro conjI impI allI)
  apply (rename_tac x x1) apply (case_tac x) apply simp_all
  apply (rename_tac x x1) apply (case_tac x) apply simp_all
done

lemma lift_var_0_comp_close_quantif: 
  "x \<notin> {Bound 0} \<Longrightarrow> (lift_var 0) (close_quantif x) = x"
by (simp add: close_quantif_case) (auto split : var.split)

lemma close_quantif_comp_lift_var_Suc:
  "x \<notin> {Bound 0} \<Longrightarrow> (close_quantif \<circ> lift_var (Suc n)) x = (lift_var n \<circ> close_quantif) x"
  by (clarsimp simp add: fun_eq_iff comp_def close_quantif_case split: var.split)
     arith

lemma fv_qform_lift_form [rule_format, simp]:
  "\<forall> n. fv_qform (lift_form n f) = lift_var n ` fv_qform f"
apply (induct f)
apply simp_all
apply (clarsimp simp add: image_Un)

apply (clarsimp simp add: image_Un lift_var_Suc_image image_comp)
apply (insert close_quantif_comp_lift_var_Suc) apply (fastforce simp add: image_def)

apply (clarsimp simp add: image_Un image_set_diff split : rename.split)+
done

lemma fv_qform_shuffle_right [rule_format, simp]:
  "\<forall> f1. fv_qform (shuffle_right bop f1 f2) = (fv_qform f1 \<union> fv_qform f2)"
apply (induct f2)
apply simp_all
apply (clarsimp simp add: image_Un image_set_diff)
apply (clarsimp simp add: Un_Diff image_Un image_comp)
done

lemma fv_qform_shuffle_left [rule_format, simp]:
  "\<forall> f2. fv_qform (shuffle_left bop f1 f2) = (fv_qform f1 \<union> fv_qform f2)"
apply (induct f1)
apply simp_all
apply (clarsimp simp add: image_Un image_set_diff)
apply (clarsimp simp add: Un_Diff image_Un image_comp)
done

lemma fv_qform_lift_bound_above_negfm [rule_format, simp]:
  "fv_qform (lift_bound_above_negfm f) = fv_qform f"
by (induct f) simp_all

lemma rewr_renamefm: "B0 \<notin> LVI \<Longrightarrow> B0 \<notin> LVF \<Longrightarrow> 
      (((FQF - LVI) \<union> LVF) - {B0}) = (((FQF - {B0}) - LVI)  \<union> LVF)"
by blast

lemma rewr_substfm: "B0 \<notin> LVF \<Longrightarrow> 
      (((FQF ) \<union> LVF) - {B0}) = (((FQF - {B0}))  \<union> LVF)"
by blast

lemma close_quantif_set_diff: "Bound 0 \<notin> A \<Longrightarrow> Bound 0 \<notin> B 
\<Longrightarrow> close_quantif ` (A - B) = (close_quantif ` A) - (close_quantif ` B)"
by (rule inj_on_image_set_diff [where C="A \<union> B"]) fastforce+

lemma bound_not_in_lift_var [simp]: "Bound 0 \<notin> ((lift_var 0) ` A)"
apply clarsimp
apply (drule sym)
apply simp
done

 (* declare [[show_brackets]]*) 
lemma fv_qform_lift_bound_above_renamefm [rule_format, simp]:
 "\<forall> sb. fv_qform (lift_bound_above_renamefm f sb) = 
        fv_qform f - isubst_dom sb \<union> fv_rename sb"
apply (induct f)
apply (simp_all split: rename.split)
apply clarsimp
apply (simp add: rewr_renamefm image_Un)
apply (simp add: close_quantif_set_diff)
apply (simp add: image_comp)
done

lemma fv_qform_lift_bound_above_substfm [rule_format, simp]:
 "\<forall> sb. fv_qform (lift_bound_above_substfm f sb) = 
        fv_qform f \<union> fv_subst sb"
apply (induct f)
apply simp_all
apply clarsimp
apply (simp add: rewr_substfm image_Un)

apply (simp add: image_comp)
done

lemma is_rename_free_qform_lift_form [simp]:
   "\<forall> n. is_rename_free_qform (lift_form n f) = is_rename_free_qform f"
by (induct f) simp_all

lemma is_rename_free_qform_shuffle_right [simp]:
  "\<forall> f1. is_rename_free_qform (shuffle_right bop f1 f2) = 
  (is_rename_free_qform f1 \<and> is_rename_free_qform f2)"
  by (induct f2) simp_all
  
lemma is_rename_free_qform_shuffle_left [simp]:
  "\<forall> f2. is_rename_free_qform (shuffle_left bop f1 f2) = 
  (is_rename_free_qform f1 \<and> is_rename_free_qform f2)"
  by (induct f1) simp_all
  
lemma is_rename_free_qform_lift_bound_above_substfm [simp]:
"\<forall> sb. is_rename_free_qform (lift_bound_above_substfm f sb) = 
       (is_rename_free_qform f)"
by (induct f)  simp_all

lemma fv_qform_lift_bound [simp]:
  "fv_qform (lift_bound f) = fv_qform f"
apply (induct f) 
apply simp_all
apply (case_tac x2a)
apply (clarsimp split : rename.split)
done

lemma is_closed_qform_lift_bound [simp]: 
  "is_closed_qform (lift_bound f) = is_closed_qform f"
by (simp add: is_closed_qform_def)

lemma lift_var_0_close_quantif_set [simp]:
  "lift_var 0 ` close_quantif ` (F - {Bound 0}) = (F - {Bound 0})"
by (simp add: image_comp) (fastforce simp add: lift_var_0_comp_close_quantif image_def)

lemma lift_var_comp_Free [simp]: "(lift_var n) \<circ> Free = Free" 
by (simp add: comp_def)

lemma lift_var_0_comp_Bound [simp]: "(lift_var 0) \<circ> Bound = Bound \<circ> Suc"
by (simp add: fun_eq_iff)


(*.....................................*)

definition "open_bound_vars fm = {v \<in> (fv_qform fm). \<not> is_free v}"


lemma nnms_to_substs_bounded_Cons_for_0:
  "(nnms_to_substs_bounded 0 (Suc (length nnms)) (vn # nnms)) = 
   (ISubst (Bound 0) (Free vn)) # (nnms_to_substs_bounded (Suc 0) (Suc (length nnms)) nnms)"
by (insert nnms_to_substs_bounded_Cons [of 0 nnms vn]) simp

lemma open_bound_vars_QRenameFm [simp]:
  "open_bound_vars (QRenameFm f (ISubst (Bound l) (Free a))) = open_bound_vars f - {Bound l}"
by (fastforce simp add: open_bound_vars_def)


lemma open_bound_vars_subst_closure_qform_nnms_to_substs_bounded [rule_format]: 
  "\<forall> l f. open_bound_vars (rename_closure_qform f (nnms_to_substs_bounded l (l + length nnms) nnms)) =
       open_bound_vars f - Bound ` {l ..< l + length nnms}"
apply (induct nnms)
apply (simp add: nnms_to_substs_bounded_def)
apply (clarsimp simp add: nnms_to_substs_bounded_Cons)
apply (drule_tac x="Suc l" in spec)
apply simp
apply fastforce
done


lemma open_bound_vars_subst_closure_qform_nnms_to_substs_sbst: 
  "open_bound_vars (rename_closure_qform f (nnms_to_substs nnms)) =
   open_bound_vars f - Bound ` {0 ..< length nnms}"
apply ( simp only: nnms_to_substs_sbst_bounded)
apply (insert open_bound_vars_subst_closure_qform_nnms_to_substs_bounded [of f 0 nnms])
apply simp
done

lemma is_closed_qform_subst_closure_qform_nnms_to_substs_bounded [rule_format]: 
"\<forall> l f. is_closed_qform (rename_closure_qform f (nnms_to_substs_bounded l (l + length nnms) nnms)) =
       (open_bound_vars f \<subseteq> Bound ` {l ..< l + length nnms})"
apply (induct nnms)
apply (simp add: nnms_to_substs_bounded_def)
apply (fastforce simp add: is_closed_qform_def open_bound_vars_def)
apply (clarsimp simp add: nnms_to_substs_bounded_Cons)
apply (drule_tac x="Suc l" in spec)
apply simp
apply fastforce
done

lemma open_bound_vars_in_Bound: "(open_bound_vars f - {Bound 0}
        \<subseteq> Bound ` {Suc 0..<Suc (length nnms)}) =
       (open_bound_vars (AllFm v f) \<subseteq> Bound ` {0..<length nnms})"
apply (rule iffI)
apply (clarsimp simp add: open_bound_vars_def)
apply (simp add: close_quantif_case split: var.split_asm)
apply fastforce
apply (clarsimp simp add: open_bound_vars_def)
apply (rename_tac x)
apply (case_tac x)
apply simp+
apply fastforce
done

lemma is_closed_qform_free_univ_bound_list [rule_format]: "\<forall> nnms fvs. 
  is_univ_quantif True f \<longrightarrow> is_prenex_form f \<longrightarrow>
     is_closed_qform (free_univ_bound_list f nnms fvs) = 
     is_closed_qform (rename_closure_qform f (nnms_to_substs nnms))"
apply (induct f)
apply simp_all
apply clarsimp
apply (simp add: nnms_to_substs_sbst_bounded nnms_to_substs_bounded_Cons_for_0)
apply (rename_tac v f nnms fvs)
apply (subgoal_tac "is_closed_qform (rename_closure_qform (AllFm v f) (nnms_to_substs_bounded 0 (0 + length nnms) nnms)) =
       (open_bound_vars (AllFm v f) \<subseteq> Bound ` {0 ..< 0 + length nnms})")
  prefer 2 apply (rule is_closed_qform_subst_closure_qform_nnms_to_substs_bounded)
apply simp

apply (subgoal_tac "is_closed_qform (rename_closure_qform ((QRenameFm f
            (ISubst (Bound 0)
              (Free
                (new_var_list (nnms @ fvs)
                  v))))) (nnms_to_substs_bounded (Suc 0) ((Suc 0) + length nnms) nnms)) =
       (open_bound_vars ((QRenameFm f
            (ISubst (Bound 0)
              (Free
                (new_var_list (nnms @ fvs)
                  v))))) \<subseteq> Bound ` {Suc 0 ..< Suc 0 + length nnms})")
  prefer 2 apply (rule is_closed_qform_subst_closure_qform_nnms_to_substs_bounded)
apply simp

apply (rule open_bound_vars_in_Bound)
done


lemma valid_qform_rename_in_qform:
  "is_quantif_free f \<Longrightarrow>
   valid_qform TYPE('d) (rename_in_qform f sbsts) =
   valid_qform TYPE('d) (rename_closure_qform f sbsts)"
by (simp add: valid_qform_def interp_qform_rename_in_qform 
   interp_qform_rename_closure_qform)

lemma bound_closing_lift_bound:
   "is_closed_qform f \<Longrightarrow>
   bound_closing (lift_bound f) [] (map name_of_free (fv_qform_list f))"
apply (simp add: bound_closing_def is_closed_qform_def) 
apply (intro conjI)
  apply (simp add: distinct_map)
  apply (simp add: Free_name_of_free_image) apply (fastforce simp add: Set.filter_def)
done

lemma valid_form_free_prenex_form_list:
  "is_univ_quantif True f 
  \<Longrightarrow> is_closed_qform f
  \<Longrightarrow> valid_form TYPE('d) (free_prenex_form_list f) = valid_qform TYPE('d) f"
apply (simp add: free_prenex_form_list_def)
apply (rule trans) 
  apply (rule valid_form_form_of_qform) apply simp apply simp
     apply (rule  is_closed_qform_rename_in_qform) apply simp 
     apply (simp add: is_closed_qform_free_univ_bound_list)
     apply (simp add: nnms_to_substs_def)
  apply (simp add: valid_qform_rename_in_qform)
apply (rule trans)
  apply (rule valid_qform_free_univ_bound_list_eq_valid_qform)
    apply simp apply simp apply (simp add: bound_closing_lift_bound)
  apply simp
done

end
