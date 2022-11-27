(*<*)
theory HoareProofs imports Hoare ProglangProofs
begin
(*>*)

section {* Hoare logic (Proofs) *}

lemma strengthen_pre:
  "(valid_qform TYPE('d) (QImplFm P' P)) \<Longrightarrow> \<turnstile>  TYPE('d) {P} c {Q} \<Longrightarrow> \<turnstile> TYPE('d) {P'} c {Q}"
apply (erule conseq)
apply assumption
apply (simp add: valid_qform_def lift_impl_def)
done

lemma weaken_post:
  "\<turnstile> TYPE('d) {P} c {Q} \<Longrightarrow> valid_qform TYPE('d) (QImplFm Q Q') \<Longrightarrow>  \<turnstile> TYPE('d) {P} c {Q'}"
apply (rule conseq)
prefer 2 apply assumption
prefer 2 apply assumption
apply (simp add: valid_qform_def lift_impl_def)
done

lemma While':
assumes "\<turnstile> TYPE('d) {QConjFm P (qform_of_form b)} c {P}" 
and "valid_qform TYPE('d) (QImplFm (QConjFm P (QNegFm (qform_of_form b))) Q)"
shows "\<turnstile> TYPE('d) {P} WHILE {iv} b DO c {Q}"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])


  (* ----------------------------------------------------------------------  *)
  (* Semantic notion of validity of a Hoare triple *)
  (* ----------------------------------------------------------------------  *)

definition hoare_valid :: "'d itself \<Rightarrow> ('r, 'c, 'i) qform \<Rightarrow> ('r, 'c, 'i) stmt \<Rightarrow> ('r, 'c, 'i) qform \<Rightarrow> bool" 
 ("\<Turnstile> _ {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile> tp {P}c{Q} = (\<forall> (s:: ('d, 'r, 'c, 'i var) Interp) t. 
     (apply_var_stmt Free c,s) \<Rightarrow> t  \<longrightarrow>  well_formed_interp s \<longrightarrow> interp_qform P s \<longrightarrow> interp_qform Q t)"

lemma interp_form_SubstFm_CSubst_add:
  "interp_qform (QSubstFm Q (CSubst c SAdd v))
  = (interp_qform Q) \<circ> (add_node v c)"
by (rule ext) (simp add: interp_c_modif_def add_node_def)

lemma interp_form_SubstFm_CSubst_delete:
  "interp_qform (QSubstFm Q (CSubst c SDiff v))
  = (interp_qform Q) \<circ> (delete_node v c)"
by (rule ext) (simp add: interp_c_modif_def delete_node_def)

lemma interp_form_SubstFm_RSubst_add:
  "interp_qform (QSubstFm Q (RSubst r SAdd (v1, v2)))
  = (interp_qform Q) \<circ> (add_edge v1 r v2)"
by (rule ext) (simp add: interp_r_modif_def add_edge_def)

lemma interp_form_SubstFm_RSubst_delete:
  "interp_qform (QSubstFm Q (RSubst r SDiff (v1, v2)))
  = (interp_qform Q) \<circ> (delete_edge v1 r v2)"
by (rule ext) (simp add: interp_r_modif_def delete_edge_def)

lemma hoare_sound_while [rule_format]: "
  ((WHILE {apply_var_form Free iv}  (apply_var_form Free b) DO (apply_var_stmt Free c), s) \<Rightarrow> t) \<Longrightarrow> 
   \<Turnstile> TYPE('d) {QConjFm P (qform_of_form b)} c {P} \<Longrightarrow> 
    well_formed_interp s \<longrightarrow> interp_qform P (s:: ('d, 'r, 'c, 'i var) Interp) \<longrightarrow> interp_qform P t \<and> \<not> interp_form b (interp_apply_var Free t)"
apply (induction "WHILE {apply_var_form Free iv}  (apply_var_form Free b) DO (apply_var_stmt Free c)" s t 
  rule: big_step_induct)
apply clarsimp
apply clarsimp
apply (subgoal_tac "well_formed_interp s\<^sub>2") prefer 2 apply (erule well_formed_interp_big_step, assumption)
apply (simp add:  hoare_valid_def)
done

lemma interp_form_bind_list [rule_format]:
  "length vs = length vis \<Longrightarrow>
  \<forall> frm i. (set vis \<subseteq> interp_d i  \<longrightarrow> 
   (interp_qform (bind_list QAll vs frm) i) 
    \<longrightarrow>  interp_qform frm (interp_i_modif_list (zip (map Free vs) vis) i))"
apply (induct vs vis rule: list_induct2)
apply (simp add: bind_list_def)

apply (simp (no_asm_use) add: bind_list_def interp_form_bind)
apply (intro allI impI)
apply clarsimp
done


text {* Soundness of Hoare logic: *}

lemma hoare_sound: "\<turnstile> TYPE('d) {P}c{Q}  \<Longrightarrow>  \<Turnstile> TYPE('d) {P}c{Q}"
proof(induction rule: hoare.induct)
  case (Skip P) thus ?case 
    by (auto simp: hoare_valid_def)
next
  case (NAdd Q c v) thus ?case 
    by (clarsimp simp only: hoare_valid_def interp_form_SubstFm_CSubst_add, clarsimp)
next
  case (NDel Q c v) thus ?case 
    by (clarsimp simp only: hoare_valid_def interp_form_SubstFm_CSubst_delete, clarsimp)
next
  case (EAdd Q r v1 v2) thus ?case 
    by (clarsimp simp only: hoare_valid_def interp_form_SubstFm_RSubst_add, clarsimp)
next
  case (EDel Q r v1 v2) thus ?case 
    by (clarsimp simp only: hoare_valid_def interp_form_SubstFm_RSubst_delete, clarsimp)
next
  case (SelAss vs b Q) thus ?case
    by (clarsimp simp add: hoare_valid_def, frule (2) interp_form_bind_list, simp)

next
  case (If P b c1 Q c2) thus ?case
    by (auto simp add: hoare_valid_def) 
next
  case (Seq P c1 Q c2 R) thus ?case
    by (auto simp add: hoare_valid_def well_formed_interp_big_step)
next
  case (While P b c iv) thus ?case
    by (clarsimp simp add: hoare_valid_def hoare_sound_while well_formed_interp_big_step)
next
  case (conseq P' P c Q Q') thus ?case
    by (simp add: hoare_valid_def valid_qform_def lift_impl_def well_formed_interp_big_step)
qed


  (* Syntactic checks *)

lemma is_univ_quantif_wp_dl [rule_format, simp]:
  "is_univ_quantif True q \<longrightarrow> is_univ_quantif True (wp_dl c q)"
by (induct c arbitrary: q) (simp_all add: QIfThenElseFm_def)

lemma is_univ_quantif_vc [rule_format, simp]:
  "is_univ_quantif True q \<longrightarrow> is_univ_quantif True (vc c q)"
by (induct c arbitrary: q) (auto simp add: Let_def QIfThenElseFm_def)


text {* Soundness of verification conditions: *}

(* declare [[show_types]] *)
lemma vc_sound: "valid_qform TYPE('d) (vc c Q) \<Longrightarrow> \<turnstile> TYPE('d) {wp_dl c Q} c {Q}"
proof(induction c arbitrary: Q)
  case (While iv b c)
  show ?case
  thm While'
  proof(simp, rule While')
    from `valid_qform TYPE('d) (vc (While iv b c) Q)`
    have vc: "valid_qform TYPE('d) (vc c (qform_of_form iv))" 
      and IQ: "valid_qform TYPE('d) (QImplFm (QConjFm (qform_of_form iv) (QNegFm (qform_of_form b))) Q)" 
      and pre: "valid_qform TYPE('d) (QImplFm (QConjFm (qform_of_form iv) (qform_of_form b)) (wp_dl c (qform_of_form iv)))" 
      by (simp_all add: valid_qform_def Let_def)
    have "\<turnstile> TYPE('d) {wp_dl c (qform_of_form iv)} c {(qform_of_form iv)}" by (rule While.IH [OF vc])
    with pre show "\<turnstile> TYPE('d) {QConjFm (qform_of_form iv) (qform_of_form b)} c {(qform_of_form iv)}"
      by(rule strengthen_pre)
    show "valid_qform TYPE('d)(QImplFm (QConjFm (qform_of_form iv) (QNegFm (qform_of_form b))) Q)" by(rule IQ)
  qed
next
case (Seq c1 c2) thus ?case by (auto simp add: valid_qform_def) 
next
case (If b c1 c2) thus ?case apply (auto intro: hoare.conseq simp add: valid_qform_def  lift_impl_def lift_ite_def)
apply (rule hoare.conseq) prefer 2 apply blast apply (clarsimp simp add: valid_qform_def QIfThenElseFm_def)+
apply (rule hoare.conseq) prefer 2 apply blast by (clarsimp simp add: valid_qform_def QIfThenElseFm_def)+
qed simp_all


lemma valid_form_ConjFm: 
   "valid_form TYPE('d) (ConjFm a b) = (valid_form TYPE('d) a \<and> valid_form TYPE('d) b)"
by (fastforce simp add: valid_form_def)

lemma valid_qform_QConjFm: 
   "valid_qform TYPE('d) (QConjFm a b) = (valid_qform TYPE('d) a \<and> valid_qform TYPE('d) b)"
by (fastforce simp add: valid_qform_def)

lemma valid_form_mp: "valid_form TYPE('d) (ImplFm P Q) \<Longrightarrow> valid_form TYPE('d) P \<Longrightarrow> valid_form TYPE('d) Q"
by (simp add: valid_form_def lift_impl_def)

(* TODO: 
Does the following still hold, after redef of hoare_valid with precond well_formed_interp s \<longrightarrow> ... ?
Is it needed ?

lemma wp_dl_mono:
  "valid_qform TYPE('d) (QImplFm P P') \<Longrightarrow> valid_qform TYPE('d) (QImplFm (wp_dl c P) (wp_dl c P'))"
apply (induction c arbitrary: P P')
apply ((simp_all add: valid_qform_def QIfThenElseFm_def interp_form_bind ), blast+)+
done

lemma vc_mono:
  "valid_qform TYPE('d) (QImplFm P P') \<Longrightarrow> valid_qform TYPE('d) (QImplFm (vc c P) (vc c P'))"
apply (induction c arbitrary: P P')
apply (simp_all add: valid_qform_def QIfThenElseFm_def lift_impl_def interp_form_bind lift_ite_def)+
apply (insert wp_dl_mono)
apply (clarsimp simp add: valid_qform_def QIfThenElseFm_def Let_def lift_impl_def interp_form_bind lift_ite_def, blast)
apply (clarsimp simp add: valid_qform_def QIfThenElseFm_def lift_impl_def interp_form_bind lift_ite_def Let_def)
done
*)

corollary vc_sound':
  "valid_qform TYPE('d) (extract_vcs P c Q) \<Longrightarrow> \<turnstile> TYPE('d) {P} c {Q}"
by (simp only: valid_qform_QConjFm extract_vcs_def) (metis strengthen_pre vc_sound)


(*<*)
end
(*>*)
