(*<*)
theory VariablesProofs imports SemanticsProofs
begin
(*>*)

section {* Treatment of variables (Proofs) *}

(*-------------------------------------------------------------------*)
subsection {* Syntactic properties *}
(*-------------------------------------------------------------------*)



lemma finite_fv_subst [simp]: "finite (fv_subst sb)"
by (induct sb) auto

lemma finite_fv_concept [simp]: "finite (fv_concept c)"
by (induct c) auto

lemma finite_fv_fact [simp]: "finite (fv_fact f)"
by (induct f) auto

lemma finite_fv_form [simp]: "finite (fv_form f)"
by (induct f) auto


lemma close_quantif_case: 
   "close_quantif x = (case x of (Free v) \<Rightarrow> Free v | (Bound n) \<Rightarrow> Bound (n - 1))"
by (auto simp add: var.split)

lemma lift_var_not_bound [simp]: "\<not> (lift_var 0 v = Bound 0)"
by (case_tac v) simp_all

lemma drop_var_lift_var [simp]:
  "drop_var n (lift_var n v) = v"
by (case_tac v) simp+

lemma lift_var_drop_var: 
  "x \<noteq> Bound n \<Longrightarrow> lift_var n (drop_var n x) = x"
apply (case_tac x)
apply clarsimp+
apply arith
done

lemma inj_on_Free [simp]: "inj_on name_of_free (Free ` A)"
by (simp add: inj_on_def)

lemma inj_on_name_of_free [simp]: "\<forall>v \<in> F. is_free v \<Longrightarrow> inj_on name_of_free F"
apply (clarsimp simp add: inj_on_def)
apply (rename_tac x y)
apply (case_tac x) apply simp
apply (case_tac y) apply fastforce+
done


lemma inj_lift_var [simp]: "inj (lift_var n)"
apply (clarsimp simp add: inj_on_def)
apply (rename_tac x y)
apply (case_tac x)
   apply (case_tac y) apply simp apply clarsimp
  by (metis drop_var_lift_var)
    
  

lemma inj_on_close_quantif [simp]: "Bound 0 \<notin> F \<Longrightarrow> inj_on close_quantif F"
  
apply (clarsimp simp add: inj_on_def close_quantif_case   var.split_asm)
apply (rename_tac x y)
apply (case_tac x)
apply simp_all
apply (case_tac y)
apply simp_all
  by (metis Suc_pred neq0_conv var.exhaust)
    

lemma Free_name_of_free_image: "\<forall> x \<in> F. is_free x \<Longrightarrow> Free ` name_of_free ` F =  F"
apply (rule subset_antisym)
apply clarsimp
apply (rename_tac x')
apply (case_tac x') apply simp apply fastforce
apply clarsimp
apply (rename_tac x')
apply (case_tac x') apply (simp add: image_def) apply (erule rev_bexI)
apply auto
done

lemma close_quantif_comp_Free [simp]: "(close_quantif \<circ> Free) = Free"
by (simp add: fun_eq_iff)

lemma close_quantif_Free_image [simp]: "close_quantif ` Free ` F = Free ` F"
by (simp add: image_comp)

lemma fv_var_isubsts_union [rule_format, simp]:
  "\<forall> A B. fv_var_isubsts (A \<union> B) sbsts = (fv_var_isubsts A sbsts \<union> fv_var_isubsts B sbsts)"
apply (induct sbsts)
apply simp
apply clarsimp
apply (rename_tac sb sbsts A B)
apply (case_tac sb)
apply (rename_tac sb sbsts A B a b)
apply (drule_tac x="insert b (A - {a})" in spec)
apply (drule_tac x="insert b (B - {a})" in spec)
apply (subgoal_tac "(insert b (A - {a}) \<union> insert b (B - {a})) = (insert b(A \<union> B - {a}))")
prefer 2 apply blast
apply simp
done

lemma fv_var_isubsts_mono [rule_format]:
  "\<forall> A B. A \<subseteq> B \<longrightarrow> fv_var_isubsts A sbsts \<subseteq> fv_var_isubsts B sbsts"
apply (induct sbsts)
apply simp
apply (intro allI impI)
apply (rename_tac sb sbsts A B)
apply (case_tac sb)
apply simp
apply (rename_tac sb sbsts A B x y)
apply (drule_tac x="(insert y (A - {x}))" in spec)
apply (drule_tac x="(insert y (B - {x}))" in spec)
apply fastforce
done


lemma distinct_fv_subst_list [simp]: "distinct (fv_subst_list sb)"
apply (case_tac sb)
apply simp_all
apply (rename_tac r rop p)
apply (case_tac p)
apply simp_all
done

lemma distinct_fv_concept_list [simp]: "distinct (fv_concept_list c)"
by (induct c) simp_all

lemma distinct_fv_fact_list [simp]: "distinct (fv_fact_list f)"
by (induct f) simp_all

lemma distinct_fv_form_list [simp]: "distinct (fv_form_list f)"
by (induct f) simp_all

lemma distinct_fv_qform_list [simp]: "distinct (fv_qform_list f)"
apply (induct f)
apply simp_all
apply (simp add: distinct_map)
apply (auto simp add: rename.split)
done


lemma fv_concept_sub_concepts [simp]:
   "(\<Union>i\<in>sub_concepts c. fv_concept i) =  fv_concept c"
by (induct c) auto

lemma fv_concept_sub_concepts_pn [simp]: 
   "(\<Union> (fv_concept ` (sub_concepts_pn c)) = fv_concept c)"
by (induct c)  (auto simp add: Let_def  if_split_asm )

lemma sub_concepts_pn_incl_fv_concept : "C \<subseteq> sub_concepts_pn c \<Longrightarrow>
       \<forall> c' \<in> C. fv_concept c' \<subseteq> fv_concept c"
apply (subgoal_tac "fv_concept ` C \<subseteq> fv_concept ` (sub_concepts_pn c)")
   prefer 2 apply (simp add: image_mono)
apply (insert fv_concept_sub_concepts_pn [of c])
apply blast
done


(*-------------------------------------------------------------------*)
subsection {* Interpretations *}
(*-------------------------------------------------------------------*)

lemma interp_c_interp_bound [simp]: 
  "interp_c (interp_bound xi i) nc = interp_c i nc"
by (simp add: interp_bound_def)

lemma interp_r_interp_bound [simp]:
  "(interp_r (interp_bound xi i) r) = interp_r i r"
by (simp add: interp_bound_def)

lemma interp_i_interp_bound_i_Bound0 [simp]:
  "interp_i (interp_bound xi i) (Bound 0) = xi"
by (simp add: interp_bound_def)

lemma interp_i_interp_bound_i_BoundSuc [simp]:
  "interp_i (interp_bound xi i) (Bound (Suc k)) = interp_i i (Bound k)"
by (simp add: interp_bound_def)

lemma interp_i_interp_bound_i_Free [simp]:
  "(interp_i (interp_bound xi i)) (Free v) = interp_i i (Free v)"
by (simp add: interp_bound_def)

lemma interp_i_interp_bound_lift_var [simp]:
  "interp_i (interp_bound xi i) (lift_var 0 v) = interp_i i v"
by (case_tac v) simp+

lemma interpRO_r_interp_bound [simp]: 
  "(interpRO_r rop nr (lift_var 0 v1, lift_var 0 v2) (interp_bound xi i)) = 
  (interpRO_r rop nr (v1, v2) i)"
by (case_tac rop) simp_all

lemma interpRO_c_interp_bound [simp]: 
  "(interpRO_c rop c (lift_var 0 v) (interp_bound xi i)) = 
  (interpRO_c rop c v i)"
by (case_tac rop) simp_all


definition "fun_replace_at n xi i = (\<lambda> v.
  (case v of
    (Free w) \<Rightarrow> (interp_i i) (Free w)
  | (Bound k) \<Rightarrow> (if n = k then xi else (if n < k then (interp_i i) (Bound (k - 1)) else  (interp_i i) (Bound k)))))"

definition "interp_replace_at n xi i = i\<lparr>interp_i := fun_replace_at n xi i\<rparr>"

lemma interp_d_interp_replace_at [simp]: "interp_d (interp_replace_at n xi i) = interp_d i"
by (simp add: interp_replace_at_def)

lemma interp_replace_at_0_interp_bound:
  "interp_bound xi i = interp_replace_at 0 xi i"
apply (simp add: interp_replace_at_def fun_replace_at_def interp_bound_def)
apply (cases i)
  apply (clarsimp simp add: var.split fun_eq_iff)
   
done


lemma fun_replace_at_lift_var [simp]:
  "fun_replace_at n xi i (lift_var n v) = interp_i i v"
by (case_tac v) (simp add: fun_replace_at_def)+

lemma interp_replace_at_lift_var [simp]:
  "(interp_i (interp_replace_at n xi i) (lift_var n v)) = interp_i i v"
by (simp add: interp_replace_at_def)


lemma interp_c_interp_replace_at [simp]: 
  "interp_c (interp_replace_at n xi i) nc = interp_c i nc"
by (simp add: interp_replace_at_def)

lemma interp_r_interp_replace_at [simp]:
  "(interp_r (interp_replace_at n xi i) r) = interp_r i r"
by (simp add: interp_replace_at_def)

lemma interpRO_r_interp_replace_at [simp]: 
  "(interpRO_r rop nr (lift_var n v1, lift_var n v2) (interp_replace_at n xi i)) = 
  (interpRO_r rop nr (v1, v2) i)"
by (case_tac rop) simp_all

lemma interpRO_c_interp_replace_at [simp]: 
  "(interpRO_c rop c (lift_var n v) (interp_replace_at n xi i)) = 
  (interpRO_c rop c v i)"
by (case_tac rop) simp_all

lemma interp_replace_at_interp_c_modif: 
  "interp_replace_at n xi (interp_c_modif c ci i) = interp_c_modif c ci (interp_replace_at n xi i)"
apply (simp add: interp_c_modif_def fun_replace_at_def interp_replace_at_def)
apply (cases i)
apply (clarsimp simp add: fun_eq_iff   var.split)
done

lemma interp_replace_at_interp_r_modif: 
  "interp_replace_at n xi (interp_r_modif r ri i) = interp_r_modif r ri (interp_replace_at n xi i)"
apply (simp add: interp_r_modif_def fun_replace_at_def interp_replace_at_def)
apply (cases i)
apply (clarsimp simp add: fun_eq_iff  var.split)
done

lemma fun_replace_at_interp_i:
  "(fun_replace_at n xi (i\<lparr>interp_i := (interp_i i)(y := yi)\<rparr>)) = ((fun_replace_at n xi i)(lift_var n y := yi))"
apply (simp add: fun_eq_iff)
apply (simp add: fun_replace_at_def var.split)
apply (auto  simp add: if_split_asm)
done

lemma interp_replace_at_interp_i_modif:
  "interp_replace_at n xi (interp_i_modif y yi i) =
              interp_i_modif (lift_var n y) yi (interp_replace_at n xi i)"
apply (simp add: interp_i_modif_def interp_replace_at_def)
apply (simp add: fun_replace_at_interp_i)
done


lemma interp_subst_interp_replace_at [simp]: 
  "interp_subst (lift_subst n sb) (interp_replace_at n xi i) = interp_replace_at n xi (interp_subst sb i)"
apply (case_tac sb)
apply (rename_tac nr subst_op prod)
apply (case_tac prod)
apply simp
apply (simp add: interp_replace_at_interp_r_modif)
apply (simp add: interp_replace_at_interp_c_modif)
done

lemma interp_rename_interp_replace_at [simp]: 
  "interp_rename (lift_rename n sb) (interp_replace_at n xi i) = interp_replace_at n xi (interp_rename sb i)"
by (case_tac sb) (simp add: interp_replace_at_interp_i_modif)

lemma interp_subst_lift_subst_interp_bound [simp]:
  "(interp_subst (lift_subst 0 sb) (interp_bound xi i)) = (interp_bound xi (interp_subst sb i))"
by (simp add: interp_replace_at_0_interp_bound)

lemma interp_rename_lift_rename_interp_bound [simp]:
  "(interp_rename (lift_rename 0 sb) (interp_bound xi i)) = (interp_bound xi (interp_rename sb i))"
by (simp add: interp_replace_at_0_interp_bound)

lemma interp_subst_closure_lift_subst [rule_format]:
  "\<forall> xi i. (interp_subst_closure (map (lift_subst 0) sbsts) (interp_bound xi i)) = 
(interp_bound xi (interp_subst_closure sbsts i))"
apply (induct sbsts)
apply simp
apply clarsimp
done


lemma fun_replace_at_drop_var: 
  "(fun_replace_at n a i \<circ> drop_var 0)(Bound 0 := xi) = fun_replace_at (Suc n) a (i\<lparr>interp_i := (interp_i i \<circ> drop_var 0)(Bound 0 := xi)\<rparr>)"
apply (rule ext)
apply (case_tac x)
apply (simp add: fun_replace_at_def)
apply (simp add: fun_replace_at_def)
apply auto
done

lemma interp_bound_fun_replace_at:
  "(interp_bound xi (i\<lparr>interp_i := fun_replace_at n a i\<rparr>)) = (interp_replace_at (Suc n) a (interp_bound xi i))"
apply (simp add: interp_bound_def)
apply (simp add: interp_replace_at_def interp_bound_def)
apply (simp add: fun_replace_at_drop_var)
done

lemma interp_concept_interp_replace_at [rule_format, simp]:
  "\<forall> i. interp_concept (lift_concept n c) (interp_replace_at n xi i) = interp_concept c i"
by (induct c) simp_all

lemma interp_fact_interp_replace_at [simp]:
  "interp_fact (lift_fact n fact1) (interp_replace_at n xi i) = interp_fact fact1 i"
by (induct fact1) simp_all


lemma interp_form_interp_replace_at [rule_format, simp]: 
  "\<forall> n i xi. interp_qform (lift_form n frm) (interp_replace_at n xi i) = interp_qform frm i"
apply (induct frm)
apply simp_all
apply (rename_tac quantif ni frm)
apply (case_tac quantif)
apply (clarsimp simp add: interp_replace_at_def interp_bound_fun_replace_at)
apply (clarsimp simp add: interp_replace_at_def interp_bound_fun_replace_at)
done

lemma interp_form_interp_bound [simp]: 
  "interp_qform (lift_form 0 f) (interp_bound xi i) = interp_qform f i"
by (simp add: interp_replace_at_0_interp_bound)


(* Lemmas about well_formed_interp *)

lemma well_formed_interp_interp_bound [simp]:
  "well_formed_interp i \<Longrightarrow> xi \<in> interp_d i \<Longrightarrow> well_formed_interp (interp_bound xi i)"
by (simp add: interp_bound_def well_formed_interp_def)


lemma interp_form_shuffle_right [rule_format]:
  "\<forall> f1 i. well_formed_interp i \<longrightarrow> interp_qform (shuffle_right bop f1 f2) i = interp_qform (QBinopFm bop f1 f2) i"
apply (induct f2)
prefer 5
apply clarify
apply (rename_tac quantif ni f1 f2 i)
apply (frule well_formed_interp_nonempty_d)
apply (case_tac bop)
apply (case_tac quantif, simp_all)
apply blast
apply (case_tac quantif, simp_all)
apply blast
done

lemma interp_form_shuffle_left [rule_format]:
  "\<forall> f2 i. well_formed_interp i \<longrightarrow> interp_qform (shuffle_left bop f1 f2) i = interp_qform (QBinopFm bop f1 f2) i"
apply (induct f1)
prefer 5
apply clarify
apply (rename_tac quantif ni f1 f2 i)
apply (frule well_formed_interp_nonempty_d)
apply (case_tac bop)
apply (case_tac quantif)
apply simp_all
apply blast
apply (case_tac quantif)
apply simp_all
apply blast
apply (simp add: interp_form_shuffle_right)+
done

lemma interp_qform_lift_bound_above_negfm [rule_format, simp]:
  "\<forall> i. interp_qform (lift_bound_above_negfm f) i = (\<not> interp_qform f i)"
apply (induct f)
prefer 5
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply auto
done


lemma interp_qform_lift_bound_above_substfm [rule_format, simp]:
  "\<forall> i sb. interp_qform (lift_bound_above_substfm f sb) i = (interp_qform (QSubstFm f sb) i)"
apply (induct f)
apply simp_all
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply simp_all
done

lemma interp_qform_lift_bound_above_renamefm [rule_format, simp]:
  "\<forall> i sb. interp_qform (lift_bound_above_renamefm f sb) i = (interp_qform (QRenameFm f sb) i)"
apply (induct f)
apply simp_all
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply simp_all
done


lemma interp_form_lift_bound [rule_format, simp]:
  "\<forall> i. well_formed_interp i \<longrightarrow> interp_qform (lift_bound f) i = interp_qform f i"
apply (induct f)
apply simp_all
apply (rename_tac binop f1 f2)
apply (case_tac binop)
apply (simp add: interp_form_shuffle_left)+
apply (rename_tac quantif ni f)
apply (case_tac quantif)
apply simp_all
done


lemma interp_i_modif_interp_bound: 
  "interp_i_modif (Free x) xi (interp_bound xi i) = interp_replace_at 0 xi (interp_i_modif (Free x) xi i)"
apply (simp add: interp_replace_at_0_interp_bound)
apply (simp add: interp_replace_at_interp_i_modif)
done

lemma interp_form_bind:
  "(interp_qform (bind QAll v frm) i) = (\<forall> vi \<in> interp_d i. interp_qform frm (interp_i_modif (Free v) vi i))"
apply (simp add: bind_def)
  apply (simp add: interp_i_modif_interp_bound)
  done
 
  
 

subsection {* Structural properties of lifting bound variables *}

lemma is_prenex_form_lift_bound_above_negfm [rule_format, simp]:
  "is_prenex_form f \<longrightarrow> is_prenex_form (lift_bound_above_negfm f)"
by (induct f) auto

lemma is_quantif_free_is_prenex_form [rule_format]:
  "is_quantif_free f \<longrightarrow> is_prenex_form f"
by (induct f) auto

lemma is_quantif_free_lift_form [rule_format,simp]:
  "is_quantif_free f \<longrightarrow> is_quantif_free (lift_form n f)"
by (induct f) auto

lemma is_prenex_form_lift_form [rule_format,simp]:
  "\<forall> n. is_prenex_form f \<longrightarrow> is_prenex_form (lift_form n f)"
by (induct f) auto

lemma is_prenex_form_shuffle_right [rule_format,simp]: 
 "\<forall> f1. is_quantif_free f1 \<longrightarrow>  is_prenex_form f2 \<longrightarrow>
       is_prenex_form (shuffle_right bop f1 f2)"
by (induct f2) auto

lemma is_prenex_form_shuffle_left [rule_format,simp]: 
 "\<forall> f2. is_prenex_form f1 \<longrightarrow>  is_prenex_form f2 \<longrightarrow>
       is_prenex_form (shuffle_left bop f1 f2)"
by (induct f1) auto

lemma is_prenex_form_lift_bound_above_substfm [rule_format,simp]: 
  "\<forall> subst. is_prenex_form f \<longrightarrow> is_prenex_form (lift_bound_above_substfm f subst)"
by (induct f) auto

lemma is_prenex_form_lift_bound_above_renamefm [rule_format,simp]: 
  "\<forall> subst. is_prenex_form f \<longrightarrow> is_prenex_form (lift_bound_above_renamefm f subst)"
by (induct f) auto

lemma is_prenex_form_lift_bound [simp]: "is_prenex_form (lift_bound f)"
by (induct f) simp_all 

lemma quantif_free_quantif_depth [rule_format, simp]:
  "is_quantif_free f \<longrightarrow> quantif_depth f = 0"
by (induct f) auto

subsection {* Proofs about Free Variable functions *}


  (* Isabelle apparently does not allow record update with a differently typed component. 
    Otherwise, one would prefer to write
    (i\<lparr>interp_i := (interp_i i) \<circ> Free \<rparr>)
    instead of 
    (interp_i_update_vartype (\<lambda> ii. ii \<circ> Free) i)
 *)

definition interp_i_update_vartype :: 
  "(('ni1 \<Rightarrow> 'd) \<Rightarrow> 'ni2 \<Rightarrow> 'd) \<Rightarrow> ('d, 'nr, 'nc, 'ni1, 'r) Interp_scheme \<Rightarrow> ('d, 'nr, 'nc, 'ni2, 'r) Interp_scheme" where
  "interp_i_update_vartype f i = 
  \<lparr> interp_d = interp_d i,interp_c = interp_c i, interp_r = interp_r i, interp_i = f (interp_i i), \<dots> = (more i) \<rparr>"


lemma interp_d_interp_i_update_vartype [simp]:
  "interp_d (interp_i_update_vartype f i) = interp_d i"
by (case_tac i) (simp add: fun_eq_iff interp_i_update_vartype_def)

lemma interp_r_interp_i_update_vartype [simp]:
  "interp_r (interp_i_update_vartype f i) = interp_r i"
by (case_tac i) (simp add: fun_eq_iff interp_i_update_vartype_def)

lemma interp_c_interp_i_update_vartype [simp]:
  "interp_c (interp_i_update_vartype f i) = interp_c i"
by (case_tac i) (simp add: fun_eq_iff interp_i_update_vartype_def)

lemma interp_i_interp_i_update_vartype [simp]: 
  "interp_i (interp_i_update_vartype f i) = f (interp_i i)"
by (simp add: interp_i_update_vartype_def)

lemma interp_i_update_vartype_interp_i_update [simp]:
  "interp_i_update_vartype f (i\<lparr>interp_i := x\<rparr>) = (i\<lparr>interp_i := f x\<rparr>)"
by (simp add: interp_i_update_vartype_def)

lemma interp_i_update_vartype_interp_c_update [simp]:
  "interp_i_update_vartype f (i\<lparr>interp_c := x\<rparr>) = (interp_i_update_vartype f i)\<lparr>interp_c := x\<rparr>"
by (simp add: interp_i_update_vartype_def)
  
lemma interp_i_update_vartype_interp_r_update [simp]:
  "interp_i_update_vartype f (i\<lparr>interp_r := x\<rparr>) = (interp_i_update_vartype f i)\<lparr>interp_r := x\<rparr>"
by (simp add: interp_i_update_vartype_def)

definition interp_apply_var :: "('i1 \<Rightarrow> 'i2) \<Rightarrow> ('d, 'r, 'c, 'i2) Interp \<Rightarrow> ('d, 'r, 'c, 'i1) Interp" where
  "interp_apply_var f = interp_i_update_vartype (\<lambda>ii. ii \<circ> f)" 
  
lemma interp_i_interp_apply_var [simp]: "interp_i (interp_apply_var f i)  = (interp_i i) \<circ> f "
by (clarsimp simp add: interp_apply_var_def fun_eq_iff) 
lemma interp_r_interp_apply_var [simp]: "interp_r (interp_apply_var f i) = interp_r i"
by (clarsimp simp add: interp_apply_var_def) 
lemma interp_c_interp_apply_var [simp]: "interp_c (interp_apply_var f i) = interp_c i"
by (clarsimp simp add: interp_apply_var_def) 
lemma interp_d_interp_apply_var [simp]: "interp_d (interp_apply_var f i) = interp_d i"
by (clarsimp simp add: interp_apply_var_def) 

lemma well_formed_interp_interp_apply_var [simp]: 
  "well_formed_interp i \<Longrightarrow> well_formed_interp (interp_apply_var f i)"
by (simp add: well_formed_interp_def interp_apply_var_def interp_i_update_vartype_def)

definition interp_i_var_equivalent 
    :: "('d, 'nr, 'nc, 'ni var) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni var) Interp \<Rightarrow> 'ni set \<Rightarrow> bool" where
  "interp_i_var_equivalent i1 i2 A = 
  ((interp_c i1 = interp_c i2) \<and> (interp_r i1 = interp_r i2) 
  \<and> (\<forall> n. interp_i i1 (Bound n) = interp_i i2 (Bound n)) 
  \<and> (\<forall> v \<in> A. interp_i i1 (Free v) = interp_i i2 (Free v)))"

definition interp_i_equivalent
    :: "('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> 'ni set \<Rightarrow> bool" where
"interp_i_equivalent i1 i2 A = 
  ( (interp_d i1 = interp_d i2)  \<and>(interp_c i1 = interp_c i2) \<and> (interp_r i1 = interp_r i2) 
  \<and> (\<forall> v \<in> A. interp_i i1 v = interp_i i2 v))"

lemma interp_i_equivalent_UNIV [simp]: 
  "(interp_i_equivalent i1 i2 UNIV) = (i1 = i2)"
apply (case_tac i1)
apply (case_tac i2)
apply (simp add: interp_i_equivalent_def fun_eq_iff)
done

lemma interp_i_equivalent_subset:
  "B \<subseteq> A \<Longrightarrow> interp_i_equivalent i1 i2 A \<Longrightarrow> interp_i_equivalent i1 i2 B"
by (fastforce simp add: interp_i_equivalent_def)

lemma interp_i_equivalent_insert [simp]:
  "interp_i_equivalent i1 i2 (insert a A) = 
  ((interp_i i1 a = interp_i i2 a) \<and> interp_i_equivalent i1 i2 A)"
by (fastforce simp add: interp_i_equivalent_def)

lemma interp_i_equivalent_union [simp]:
  "interp_i_equivalent i1 i2 (A \<union> B) = (interp_i_equivalent i1 i2 A \<and> interp_i_equivalent i1 i2 B)"
by (fastforce simp add: interp_i_equivalent_def)

lemma interp_i_equivalent_interp_i: 
  "interp_i_equivalent i1 i2 {v} \<Longrightarrow> interp_i i1 v = interp_i i2 v"
by (simp add: interp_i_equivalent_def)


lemma interp_d_interp_subst:
  "\<lbrakk>interp_d i1 = interp_d i2;
  \<forall>v\<in>fv_subst subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  interp_d (interp_subst subst i1) = interp_d (interp_subst subst i2)"
by (case_tac subst)
   (simp add: interp_r_modif_def interp_c_modif_def interp_i_modif_def)+

lemma interp_d_interp_rename:
  "\<lbrakk>interp_d i1 = interp_d i2;
  \<forall>v\<in>fv_rename subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  interp_d (interp_rename subst i1) = interp_d (interp_rename subst i2)"
by (case_tac subst)
   (simp add: interp_r_modif_def interp_c_modif_def interp_i_modif_def)+


lemma interp_c_interp_subst:
  "\<lbrakk>interp_c i1 = interp_c i2;
  \<forall>v\<in>fv_subst subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  interp_c (interp_subst subst i1) = interp_c (interp_subst subst i2)"
apply (case_tac subst)
apply (simp add: interp_r_modif_def interp_c_modif_def interp_i_modif_def)+
apply (rename_tac nc subst_op ni)
apply (case_tac subst_op)
apply simp+
done

lemma interp_c_interp_rename:
  "\<lbrakk>interp_c i1 = interp_c i2;
  \<forall>v\<in>fv_rename subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  interp_c (interp_rename subst i1) = interp_c (interp_rename subst i2)"
by (case_tac subst)
   (simp add: interp_r_modif_def interp_c_modif_def interp_i_modif_def)+


lemma interp_r_interp_subst:
  "\<lbrakk>interp_r i1 = interp_r i2;
     \<forall>v\<in>fv_subst subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  interp_r (interp_subst subst i1) = interp_r (interp_subst subst i2)"
apply (case_tac subst)
apply (auto simp add: interp_r_modif_def interp_c_modif_def interp_i_modif_def)
apply (rename_tac nr subst_op a b)
apply (case_tac subst_op)
apply simp+
done

lemma interp_r_interp_rename:
  "\<lbrakk>interp_r i1 = interp_r i2;
     \<forall>v\<in>fv_rename subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  interp_r (interp_rename subst i1) = interp_r (interp_rename subst i2)"
by (case_tac subst)
   (auto simp add: interp_r_modif_def interp_c_modif_def interp_i_modif_def)

lemma interp_i_interp_subst [simp]: 
"interp_i (interp_subst sb i) v = interp_i i v"
by (case_tac sb) auto

lemma interp_i_interp_rename [simp]: 
"v \<noteq> v1 \<Longrightarrow> interp_i (interp_rename (ISubst v1 v2) i) v = interp_i i v"
by simp

lemma interp_i_interp_subst_closure [rule_format]: 
"(interp_i (interp_subst_closure sbst i) x) = interp_i i x"
by (induct sbst) auto

lemma interp_i_interp_rename_closure [rule_format]: 
"\<forall> i. x \<notin> \<Union> (isubst_dom ` set sbst) \<Longrightarrow> 
 (interp_i (interp_rename_closure sbst i) x) = interp_i i x"
apply (induct sbst)
apply auto
apply (rename_tac sb sbsts)
apply (case_tac sb)
apply auto
done

lemma interp_i_interp_subst_Free:
  "\<lbrakk> \<forall>v \<in> V. interp_i i1 v = interp_i i2 v;
     \<forall>v\<in>fv_subst subst. interp_i i1 v = interp_i i2 v \<rbrakk> \<Longrightarrow>
  \<forall>v \<in> V. interp_i (interp_subst subst i1) v = interp_i (interp_subst subst i2) v"
apply clarify
apply (case_tac subst)
apply simp_all
done


lemma interp_i_equivalent_interp_subst: 
  "\<lbrakk>interp_i_equivalent i1 i2 V;
  interp_i_equivalent i1 i2 (fv_subst subst) \<rbrakk> \<Longrightarrow>
  interp_i_equivalent (interp_subst subst i1) (interp_subst subst i2) V"
apply (unfold interp_i_equivalent_def)
apply clarify
apply (intro conjI)
apply (erule interp_d_interp_subst) apply assumption+
apply (erule interp_c_interp_subst) apply assumption+
apply (erule interp_r_interp_subst) apply assumption+
apply (erule interp_i_interp_subst_Free) apply assumption+
done

lemma interp_i_equivalent_interp_rename: 
  "\<lbrakk>interp_i_equivalent i1 i2 (V - {v1});
  interp_i i1 v2 = interp_i i2 v2 \<rbrakk> \<Longrightarrow>
  interp_i_equivalent (interp_rename (ISubst v1 v2) i1) (interp_rename (ISubst v1 v2) i2) V"
apply (unfold interp_i_equivalent_def)
apply (clarsimp simp del: interp_rename.simps)
apply (intro conjI)
apply (erule interp_c_interp_rename) apply simp
apply (erule interp_r_interp_rename) apply simp
apply (simp add: interp_i_modif_def)
done

lemma interp_i_equivalent_interp_concept [rule_format]:
   "\<forall>i1 i2. interp_i_equivalent i1 i2 (fv_concept c) 
  \<longrightarrow> interp_concept c i1 = interp_concept c i2"
   apply (induct c)
   apply (simp only: interp_i_equivalent_def,
         (clarsimp simp add: interp_i_equivalent_interp_subst)+)+
   apply (simp only: interp_i_equivalent_def)
done

lemma interp_i_equivalent_interp_fact: 
  "interp_i_equivalent i1 i2 (fv_fact f) \<Longrightarrow> interp_fact f i1 = interp_fact f i2" 
apply (case_tac f)
apply (clarsimp simp add: interp_i_equivalent_interp_concept)+
apply (clarsimp simp add: interp_i_equivalent_def)+
done

lemma interp_i_equivalent_interp_form [rule_format]: 
  "\<forall>i1 i2. interp_i_equivalent i1 i2 (fv_form f) 
  \<longrightarrow> interp_form f i1 = interp_form f i2" 
apply (induct f) 
apply (simp_all add:  interp_i_equivalent_interp_subst)
apply (clarsimp simp add: interp_i_equivalent_interp_fact)+
done

lemma interp_i_equivalent_interp_qform [rule_format]: 
  "\<forall>i1 i2. interp_i_equivalent i1 i2 (fv_qform f) 
  \<longrightarrow> is_quantif_free f
  \<longrightarrow> interp_qform f i1 = interp_qform f i2" 
apply (induct f) 
apply (simp_all add:  interp_i_equivalent_interp_subst)
apply (clarsimp simp add: interp_i_equivalent_interp_fact)+
  apply (case_tac x2a ) 
  apply (clarsimp simp add: interp_i_equivalent_interp_rename  simp del: interp_rename.simps split ) 
done

(* Lemmas about is_univ_quantif *)

lemma is_univ_quantif_lift_bound_above_negfm [simp]: 
  "is_univ_quantif b (lift_bound_above_negfm f) = is_univ_quantif (\<not> b) f"
by (induct f arbitrary: b) simp_all

lemma is_univ_quantif_lift_bound_above_substfm [simp]: 
  "is_univ_quantif b (lift_bound_above_substfm f sb) = is_univ_quantif b f"
by (induct f arbitrary: b sb) simp_all

lemma is_univ_quantif_lift_bound_above_renamefm [simp]: 
  "is_univ_quantif b (lift_bound_above_renamefm f sb) = is_univ_quantif b f"
by (induct f arbitrary: b sb) simp_all

lemma is_univ_quantif_lift_form [simp]:
  "is_univ_quantif b (lift_form n f) = is_univ_quantif b f"
by (induct f arbitrary: b n) simp_all

lemma is_univ_quantif_shuffle_right [rule_format, simp]:
  "\<forall> f1. is_univ_quantif b (shuffle_right bop f1 f2) = (is_univ_quantif b f1 \<and> is_univ_quantif b f2) "
by (induct f2) auto

lemma is_univ_quantif_shuffle_left [rule_format, simp]:
  "\<forall> f2. is_univ_quantif b (shuffle_left bop f1 f2) = (is_univ_quantif b f1 \<and> is_univ_quantif b f2)"
by (induct f1) auto

lemma is_univ_quantif_lift_bound [rule_format, simp]: 
  "\<forall> b. is_univ_quantif b (lift_bound f) = is_univ_quantif b f"
by (induct f) simp_all

lemma is_quantif_free_is_univ_quantif [simp]:
  "is_quantif_free frm \<longrightarrow> is_univ_quantif b frm"
by (induct frm arbitrary: b) auto

lemma is_univ_quantif_bind [simp]:
  "is_univ_quantif b (bind q v f) = (dual_quantif b q = QAll \<and> is_univ_quantif b f)"
by (simp add: bind_def)

lemma is_univ_quantif_bind_list [rule_format, simp]:
  "\<forall> f. is_univ_quantif b (bind_list q vs f) = ((vs = [] \<or> dual_quantif b q = QAll) \<and> is_univ_quantif b f)"
by (induct vs) (auto simp add: bind_list_def)

lemma quantif_free_qform_of_form [simp]: "is_quantif_free (qform_of_form fm)"
by (induct fm) auto

(*<*)
end
(*>*)
