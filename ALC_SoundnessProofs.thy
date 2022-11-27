(*<*)
theory ALC_SoundnessProofs imports ALC_TableauProofs
begin
(*>*)

section {* Soundness of Tableau Calculus *}

lemma satisfiable_satisfiable_neg_abox [simp]: 
  "satisfiable TYPE('d) (neg_norm_abox ab) = satisfiable TYPE('d) ab"
  by ( fastforce simp add: satisfiable_def image_iff neg_norm_abox_def)

  (* sound means: no creation of models *)
definition  sound :: "('nr, 'nc, 'ni) rule \<Rightarrow> bool" where 
  "sound rl \<equiv> \<forall> A1 A2. rl A1 A2 \<longrightarrow> satisfiable TYPE('d) A2 \<longrightarrow> satisfiable TYPE('d) A1"


definition soundness_pres_weakening :: "('nr,'nc,'ni) rule \<Rightarrow> ('nr,'nc,'ni) rule \<Rightarrow> bool" where
"soundness_pres_weakening r r_weak = 
  (\<forall> ab. (Collect (r ab) \<subseteq> Collect (r_weak ab)))"

lemma sound_weaken: "sound TYPE('d) r_weak
\<Longrightarrow> soundness_pres_weakening r r_weak 
\<Longrightarrow> sound TYPE('d) r"
by (fastforce simp add: sound_def soundness_pres_weakening_def)

lemma sound_ex_rule_closure [rule_format, simp]: 
"(\<forall> f. sound TYPE('d) (ir f)) \<Longrightarrow> sound TYPE('d) (ex_rule_closure ir)"
by (fastforce simp add: sound_def ex_rule_closure_def)

lemma sound_rule_weaken:
   "sound TYPE('d) rl1 \<Longrightarrow> 
   \<forall> A1 A2. rl2 A1 A2 \<longrightarrow> rl1 A1 A2 \<Longrightarrow> 
   sound TYPE('d) rl2"
by (fastforce simp add: sound_def)


  (* ----------------------------------------------------------------------  *)
  (* Rule combinators *)

lemma empty_rule_sound [simp]: 
  "sound TYPE('d) empty_rule"
  by (fastforce simp add: sound_def empty_rule_def)

lemma alternative_rule_sound [simp]:
  "sound TYPE('d) (alternative_rule r1 r2) = (sound TYPE('d) r1 \<and> sound TYPE('d) r2)"
  by (fastforce simp add: sound_def alternative_rule_def)

lemma alternative_rule_of_set_sound [simp]: 
  "(sound TYPE('d) (alternative_rule_of_set rs)) = (Ball rs (sound TYPE('d)))"
by (fastforce simp add: sound_def alternative_rule_of_set_def)

lemma relcompp_rule_sound [simp]: 
"sound TYPE('d) r1 \<Longrightarrow> sound TYPE('d) r2 \<Longrightarrow> sound TYPE('d) (r1 OO r2)"
by (fastforce simp add: sound_def relcompp.simps)

lemma rtranclp_rule_sound_for_induct: 
  "r\<^sup>*\<^sup>* A1 A2 \<Longrightarrow>
    satisfiable TYPE('d) A2 \<longrightarrow>
    (\<forall>A1 A2. r A1 A2 \<longrightarrow> satisfiable TYPE('d) A2 \<longrightarrow> satisfiable TYPE('d) A1) \<longrightarrow> satisfiable TYPE('d) A1"
  by (induct rule: rtranclp.induct) auto

lemma rtranclp_rule_sound [simp]: "sound TYPE('d) r \<Longrightarrow> sound TYPE('d) r\<^sup>*\<^sup>*"
  by (clarsimp simp add: sound_def rtranclp_rule_sound_for_induct)

lemma tranclp_rule_sound_for_induct:
  "r\<^sup>+\<^sup>+ A1 A2 \<Longrightarrow>
    satisfiable TYPE('d) A2 \<longrightarrow>
    (\<forall>A1 A2. r A1 A2 \<longrightarrow> satisfiable TYPE('d) A2 \<longrightarrow> satisfiable TYPE('d) A1) \<longrightarrow> satisfiable TYPE('d) A1"
  by (induct rule: tranclp.induct) auto

lemma tranclp_rule_sound [simp]: "sound TYPE('d) r \<Longrightarrow> sound TYPE('d) r\<^sup>+\<^sup>+"
  by (clarsimp simp add: sound_def tranclp_rule_sound_for_induct)


  (*----------------------------------------------------------------------------------------*)
  (* Properties of specific rules *)
  
lemma conjc_rule_indiv_sound [simp, intro]: "sound TYPE('d) (conjc_rule_indiv f)"
  by (fastforce elim: conjc_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma disjc_rule_indiv_sound [simp]: "sound TYPE('d) (disjc_rule_indiv f)"
  by (fastforce elim: disjc_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma allc_rule_indiv_sound [simp]: "sound TYPE('d) (allc_rule_indiv f)"
  by (fastforce elim: allc_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma somec_rule_indiv_sound [simp]: "sound TYPE('d) (somec_rule_indiv (z, f))"
  by (fastforce elim: somec_rule_indiv_cases  simp add: sound_def satisfiable_def)

lemma substc_rule_indiv_sound [simp]: "sound TYPE('d) (substc_rule_indiv f)"
  by (fastforce elim: substc_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma eq_rule_indiv_sound [simp]: "sound TYPE('d) (eq_rule_indiv f)"
apply (clarsimp simp add: sound_def satisfiable_def)
apply (erule eq_rule_indiv_cases)
apply (rename_tac a1 a2 i x y)
apply (rule_tac x="(interp_rename_closure (if x < y then [ISubst y x] else [ISubst x y]) i)" in exI)
apply (fastforce simp add: interp_form_rename_in_form_interp_rename_closure rename_in_abox_def)
done

lemma eq_compl_rule_sound [simp]: "sound TYPE('d) eq_compl_rule"
apply (clarsimp simp add: sound_def satisfiable_def)
apply (erule eq_compl_rule_cases)
apply (rename_tac a1 a2 i x y)
apply (elim disjE)
apply fastforce
apply (rule_tac x="(interp_rename_closure [ISubst y x] i)" in exI)
apply (fastforce simp add: interp_form_rename_in_form_interp_rename_closure rename_in_abox_def)
done

lemma conjfm_rule_indiv_sound [simp]: "sound TYPE('d) (conjfm_rule_indiv f)"
  by (fastforce elim: conjfm_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma disjfm_rule_indiv_sound [simp]: "sound TYPE('d) (disjfm_rule_indiv f)"
  by (fastforce elim: disjfm_rule_indiv_cases  simp add: sound_def satisfiable_def)

lemma substfm_rule_indiv_sound [simp]: "sound TYPE('d) (substfm_rule_indiv f)"
  by (fastforce elim: substfm_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma choose_rule_indiv_sound [simp]: "sound TYPE('d) (choose_rule_indiv f)"
  by (fastforce elim: choose_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma choose_stable_rule_indiv_sound [simp]: "sound TYPE('d) (choose_stable_rule_indiv f)"
  by (fastforce elim: choose_stable_rule_indiv_cases simp add: sound_def satisfiable_def)

lemma numrestrc_ge_rule_indiv_sound [simp]: "sound TYPE('d) (numrestrc_ge_rule_indiv f)"
  by (fastforce elim:  numrestrc_ge_rule_indiv_cases  simp add: sound_def satisfiable_def)

lemma numrestrc_lt_rule_orig_indiv_sound [simp]: "sound TYPE('d) (numrestrc_lt_rule_orig_indiv (S, f))"
apply (clarsimp simp add: sound_def satisfiable_def)
apply (erule numrestrc_lt_rule_orig_indiv_cases)
apply (rename_tac a1 a2 i x n r c y1 y2)
apply (rule_tac x="(interp_rename_closure [ISubst y2 y1] i)" in exI)
apply (fastforce simp add: interp_form_rename_in_form_interp_rename_closure rename_in_abox_def)
done

lemma numrestrc_lt_rule_indiv_sound [simp]: "sound TYPE('d) (numrestrc_lt_rule_indiv f)"
apply (clarsimp simp add: sound_def satisfiable_def)
apply (erule numrestrc_lt_rule_indiv_cases)
apply (rename_tac a1 a2 i x n r c S y1 y2)
apply (rule_tac x="(interp_rename_closure [ISubst y2 y1] i)" in exI)
apply (fastforce simp add: interp_form_rename_in_form_interp_rename_closure rename_in_abox_def)
done

lemma somec_rule_sound [simp]: "sound TYPE('d) somec_rule"
apply (simp add: somec_rule_def)
apply (rule sound_ex_rule_closure)
apply (case_tac f)
apply simp
done

lemma numrestrc_lt_rule_orig_sound [simp]: "sound TYPE('d) numrestrc_lt_rule_orig"
apply (simp add: numrestrc_lt_rule_orig_def)
apply (rule sound_ex_rule_closure)
apply (case_tac f)
apply simp
done

lemma alc_rule_sound [simp]: "sound TYPE('d) alc_rule"
  by (simp add: alc_rule_def set_alc_rules_def)
     (simp add: conjc_rule_def disjc_rule_def allc_rule_def substc_rule_def 
     eq_rule_def
     conjfm_rule_def disjfm_rule_def choose_rule_def substfm_rule_def 
     numrestrc_ge_rule_def numrestrc_lt_rule_def)

(*<*)
end
(*>*)
