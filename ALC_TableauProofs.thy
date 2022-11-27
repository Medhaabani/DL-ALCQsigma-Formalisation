(*<*)
theory ALC_TableauProofs imports ALC_Tableau NormalFormProofs
begin
(*>*)

section {* Tableau Calculus for $\cal ALCQ$ (Proofs) *}

inductive_cases conjc_applicable_cases [elim!]: "conjc_applicable f ab"
inductive_cases disjc_applicable_cases [elim!]: "disjc_applicable f ab"
inductive_cases allc_applicable_cases [elim!]: "allc_applicable f ab"
inductive_cases somec_applicable_cases [elim!]: "somec_applicable z f ab"
inductive_cases substc_applicable_cases [elim!]: "substc_applicable f ab"
inductive_cases eq_applicable_cases [elim!]: "eq_applicable f ab"
inductive_cases conjfm_applicable_cases [elim!]: "conjfm_applicable f ab"
inductive_cases disjfm_applicable_cases [elim!]: "disjfm_applicable f ab"
inductive_cases substfm_applicable_cases [elim!]: "substfm_applicable f ab"
inductive_cases numrestrc_ge_applicable_cases [elim!]: "numrestrc_ge_applicable f ab"
inductive_cases numrestrc_lt_applicable_cases [elim!]: "numrestrc_lt_applicable (S, f) ab"

inductive_cases conjc_rule_indiv_cases: "conjc_rule_indiv f ab1 ab2"
inductive_cases disjc_rule_indiv_cases: "disjc_rule_indiv f ab1 ab2"
inductive_cases allc_rule_indiv_cases: "allc_rule_indiv f ab1 ab2"
inductive_cases somec_rule_indiv_cases: "somec_rule_indiv (z, f) ab1 ab2"
inductive_cases substc_rule_indiv_cases: "substc_rule_indiv f ab1 ab2"
inductive_cases choose_rule_indiv_cases: "choose_rule_indiv f ab1 ab2"
inductive_cases choose_stable_rule_indiv_cases: "choose_stable_rule_indiv f ab1 ab2"
inductive_cases numrestrc_ge_rule_indiv_cases: "numrestrc_ge_rule_indiv f ab1 ab2"
inductive_cases numrestrc_lt_rule_orig_indiv_cases: "numrestrc_lt_rule_orig_indiv (S, f) ab1 ab2"
inductive_cases numrestrc_lt_rule_indiv_cases: "numrestrc_lt_rule_indiv f ab1 ab2"
inductive_cases eq_rule_indiv_cases: "eq_rule_indiv f ab1 ab2"
inductive_cases conjfm_rule_indiv_cases: "conjfm_rule_indiv f ab1 ab2"
inductive_cases disjfm_rule_indiv_cases: "disjfm_rule_indiv f ab1 ab2"
inductive_cases substfm_rule_indiv_cases: "substfm_rule_indiv f ab1 ab2"

inductive_cases eq_compl_rule_cases: "eq_compl_rule ab1 ab2"

(*---------------------------------------------------------------------------------*)
(* Auxiliary facts about aboxes *)
(*---------------------------------------------------------------------------------*)


lemma rename_in_abox_id [simp]: " rename_in_abox ab [ISubst v1 v1] = ab"
by (simp add: rename_in_abox_def)

definition is_neg_norm_abox :: "('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
  "is_neg_norm_abox ab = (\<forall> f \<in> ab. (is_neg_norm_form f))"

definition neg_norm_abox ::"('nr, 'nc, 'ni) abox \<Rightarrow>('nr, 'nc, 'ni) abox " where
"neg_norm_abox ab =  (neg_norm_form True)` ab"

lemma is_neg_norm_neg_norm:"is_neg_norm_abox(neg_norm_abox ab)"
 by (simp add: image_iff is_neg_norm_abox_def  neg_norm_abox_def)

lemma is_neg_norm_abox_empty [simp]: "is_neg_norm_abox {}"
by (simp add: is_neg_norm_abox_def)

lemma is_neg_norm_abox_insert [simp]: 
  "is_neg_norm_abox (insert x xs) = (is_neg_norm_form x \<and> is_neg_norm_abox xs)"
by (simp add: is_neg_norm_abox_def)

lemma neg_norm_is_neg_norm :" is_neg_norm_abox ab \<Longrightarrow> neg_norm_abox ab = ab  "
  apply (simp add: image_iff is_neg_norm_abox_def  neg_norm_abox_def)
  apply (fastforce simp add:image_def neg_norm_form_is_neg_norm_form )
done

lemma fv_abox_insert [simp]: "fv_abox (insert f ab) = fv_form f \<union> fv_abox ab"
by (simp add: fv_abox_def)

lemma fv_abox_union [simp]: "fv_abox (A \<union> B) = fv_abox A \<union> fv_abox B"
by (simp add: fv_abox_def)

lemma fv_abox_image_FactFm:
  "fv_abox ((\<lambda>c. FactFm (Inst x c)) ` C) = (if C = {} then {} else {x}) \<union> (\<Union> (fv_concept ` C))"
by (auto simp add: fv_abox_def)

lemma finite_fv_abox [simp]: "finite ab \<Longrightarrow> finite (fv_abox ab)"
by (simp add: fv_abox_def)

lemma fv_form_fv_abox: "f \<in> ab \<Longrightarrow>  fv_form f \<subseteq> fv_abox ab"
by (fastforce simp add: fv_abox_def)


lemma in_fresh_set_notin_abox: "y \<in> Y \<Longrightarrow> fresh_set Y ab \<Longrightarrow> y \<in> fv_form f \<Longrightarrow> f \<notin> ab"
by (fastforce simp add: fresh_set_def fv_abox_def)

lemma fresh_set_fv_form: "fresh_set Y ab \<Longrightarrow> f \<in> ab \<Longrightarrow> fv_form f \<inter> Y = {}"
by (fastforce simp add: fresh_set_def fv_abox_def)

lemma fresh_set_incr_fresh_set: "fresh_set_incr Y ab \<Longrightarrow> fresh_set Y ab"
by (fastforce simp add: fresh_set_incr_def fresh_set_def)

lemma in_fresh_set_incr_notin_abox: "y \<in> Y \<Longrightarrow> fresh_set_incr Y ab \<Longrightarrow> y \<in> fv_form f \<Longrightarrow> f \<notin> ab"
by (fast dest: fresh_set_incr_fresh_set in_fresh_set_notin_abox)

lemma fresh_set_incr_fv_form: "fresh_set_incr Y ab \<Longrightarrow> f \<in> ab \<Longrightarrow> fv_form f \<inter> Y = {}"
by (fast dest: fresh_set_incr_fresh_set in_fresh_set_notin_abox)

(* --------------------------------------------------------- *)
(* Preservation of nnf by rules *)

definition neg_norm_pres_rule :: "('nr, 'nc, 'ni) rule \<Rightarrow> bool" where
  "neg_norm_pres_rule rl = (\<forall> ab1 ab2. rl ab1 ab2 \<longrightarrow> is_neg_norm_abox ab1 \<longrightarrow> is_neg_norm_abox ab2)"

lemma conjc_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (conjc_rule_indiv f)"
  by (fastforce elim: conjc_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma disjc_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (disjc_rule_indiv f)"
   by (fastforce elim: disjc_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma allc_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (allc_rule_indiv f)"
   by (fastforce elim: allc_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma somec_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (somec_rule_indiv (z, f))"
  apply (clarsimp simp add: neg_norm_pres_rule_def)
  apply (erule somec_rule_indiv_cases)
  apply (erule somec_applicable_cases)
  apply (fastforce  simp add: is_neg_norm_abox_def)
  done

lemma choose_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (choose_rule_indiv f)"
   by (fastforce elim: choose_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)
   
lemma choose_stable_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (choose_stable_rule_indiv f)"
   by (fastforce elim: choose_stable_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)
  
lemma numrestrc_ge_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (numrestrc_ge_rule_indiv f)"
 apply (clarsimp simp add: neg_norm_pres_rule_def)
 apply (erule numrestrc_ge_rule_indiv_cases)
 apply (erule numrestrc_ge_applicable_cases)
 apply (clarsimp simp add:image_def numrestrc_ge_rule_facts_def)
 apply (clarsimp simp add: is_neg_norm_abox_def  fresh_set_def)
 apply (auto simp add: image_def is_neg_norm_abox_def) 
 done


lemma is_neg_norm_concept_rename_in_concept [rule_format, simp]:
  "\<forall> sb. is_neg_norm_concept c \<longrightarrow> is_neg_norm_concept (rename_in_concept c sb)"
  by (induct c, simp_all)
 
lemma is_neg_norm_fact_rename_in_fact [rule_format, simp]:
  "is_neg_norm_fact fct \<longrightarrow> is_neg_norm_fact (rename_in_fact fct sbsts)"
by (case_tac fct) simp_all

lemma is_neg_norm_form_rename_in_form [rule_format, simp]:
  "\<forall> sbsts. is_neg_norm_form fm \<longrightarrow> is_neg_norm_form (rename_in_form fm sbsts)"
  by (induct fm) simp_all

lemma eq_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (eq_rule_indiv f)"
  by (fastforce elim: eq_rule_indiv_cases 
    simp add: rename_in_abox_def neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma eq_compl_rule_preserve_nnf [simp]: "neg_norm_pres_rule eq_compl_rule"
  by (fastforce elim: eq_compl_rule_cases 
    simp add: rename_in_abox_def neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma numrestrc_lt_rule_orig_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (numrestrc_lt_rule_orig_indiv (S, f))"
by (fastforce elim: numrestrc_lt_rule_orig_indiv_cases 
  simp add: neg_norm_pres_rule_def is_neg_norm_abox_def rename_in_abox_def)

lemma numrestrc_lt_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (numrestrc_lt_rule_indiv f)"
by (fastforce elim: numrestrc_lt_rule_indiv_cases 
  simp add: neg_norm_pres_rule_def is_neg_norm_abox_def rename_in_abox_def)

lemma conjfm_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (conjfm_rule_indiv f)"
  by (fastforce elim: conjfm_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma disjfm_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (disjfm_rule_indiv f)"
   by (fastforce elim: disjfm_rule_indiv_cases simp add: neg_norm_pres_rule_def is_neg_norm_abox_def)

lemma substc_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (substc_rule_indiv f)"
  by (fastforce  simp only: neg_norm_pres_rule_def  substc_rule_indiv.simps is_neg_norm_abox_def push_subst_form_pres_neg_norm_form)
    
lemma substfm_rule_indiv_preserve_nnf [simp]: "neg_norm_pres_rule (substfm_rule_indiv f)"
   by (fastforce simp only: neg_norm_pres_rule_def substfm_rule_indiv.simps  is_neg_norm_abox_def  push_subst_form_pres_neg_norm_form)

  (* ----------------------------------------------------------------------  *)
  (* Rule combinators *)

lemma empty_rule_preserve_nnf [simp]: 
  "neg_norm_pres_rule empty_rule"
  by (simp add: neg_norm_pres_rule_def empty_rule_def)

lemma alternative_rule_preserve_nnf [simp]: 
 "neg_norm_pres_rule (alternative_rule r1 r2) = 
 (neg_norm_pres_rule r1 \<and> neg_norm_pres_rule r2) "
by (fastforce simp add: neg_norm_pres_rule_def alternative_rule_def)

lemma alternative_rule_of_set_preserve_nnf [simp]: 
  "(neg_norm_pres_rule (alternative_rule_of_set rs)) = (Ball rs neg_norm_pres_rule)"
by (fastforce simp add: neg_norm_pres_rule_def alternative_rule_of_set_def)  

lemma ex_rule_closure_preserve_nnf [rule_format, simp]: 
 "(\<forall> f.  neg_norm_pres_rule (ir f)) \<Longrightarrow>  neg_norm_pres_rule (ex_rule_closure ir)"
by (fastforce simp add: neg_norm_pres_rule_def ex_rule_closure_def)


lemma somec_rule_preserve_nnf [simp]: "neg_norm_pres_rule somec_rule"
apply (simp add: somec_rule_def)
apply (rule ex_rule_closure_preserve_nnf)
apply (case_tac f)
apply simp
done

lemma numrestrc_lt_rule_orig_preserve_nnf [simp]: "neg_norm_pres_rule numrestrc_lt_rule_orig"
apply (simp add: numrestrc_lt_rule_orig_def)
apply (rule ex_rule_closure_preserve_nnf)
apply (case_tac f)
apply simp
done

lemma alc_rule_preserve_nnf [simp]: "neg_norm_pres_rule alc_rule"
   by (simp add: alc_rule_def set_alc_rules_def)
      (simp add: conjc_rule_def disjc_rule_def allc_rule_def substc_rule_def eq_rule_def
      conjfm_rule_def disjfm_rule_def choose_rule_def substfm_rule_def 
      numrestrc_ge_rule_def numrestrc_lt_rule_def)

      
  (* ---------------------------------------------------------------- *)
  (* Proofs about tableau rules *)
  (* ---------------------------------------------------------------- *)
  
definition node_active :: "('nr, 'nc, 'ni) tableau \<Rightarrow> 'ni \<Rightarrow> bool" where
  "node_active tab x = (x \<in> fv_abox (abox tab))"

(* TODO: decide which of the two definitions to keep *)
definition node_concepts_abox :: "('nr, 'nc, 'ni) abox \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) concept set" where
  "node_concepts_abox ab x = (concept_of_Inst_fact ` {f \<in> ab. is_Inst_fact {x} f})"
definition node_concepts :: "('nr, 'nc, 'ni) tableau \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) concept set" where
  "node_concepts tab x = node_concepts_abox (abox tab) x"

definition all_subconcepts_abox:: "('nr, 'nc, 'ni) abox \<Rightarrow> ('nr, 'nc, 'ni) concept set" where
"all_subconcepts_abox ab = (\<Union>x \<in> (fv_abox ab).  \<Union>c \<in> node_concepts_abox ab x. (sub_concepts_pn c))"

(*----------------- Definition of diverse closure properties -------------------------*) 

definition finite_varbounds :: "('nr, 'nc, 'ni) tableau \<Rightarrow> bool" where
  "finite_varbounds tab = (\<forall> x \<in> fv_abox (abox tab). finite (varbounds tab x))"

definition deco_respecting_bounds :: "('nr, 'nc, 'ni) tableau \<Rightarrow> bool" where
"deco_respecting_bounds tab = (\<forall> x \<in> fv_abox (abox tab). (node_concepts tab x) \<subseteq> (varbounds tab x))"


 (* TODO: bounds_subset_closed has been used in the proofs of bounds_sable_conjc_rule,
   whereas the very similar bounds_subset_closed_pn is used in other proofs. 
   Combine these two.
 
definition bounds_subset_closed :: "('nr, 'nc, 'ni) varbounds \<Rightarrow> bool" where
"bounds_subset_closed bds = (\<forall> x c. c \<in> bds x \<longrightarrow>  (sub_concepts_pn c) \<subseteq> bds x)"
*)
definition bounds_subset_closed_pn :: "('nr, 'nc, 'ni) varbounds \<Rightarrow> bool" where
"bounds_subset_closed_pn bds = (\<forall> x c. c \<in> bds x \<longrightarrow>  (sub_concepts_pn c) \<subseteq> bds x)"

definition bounds_renaming_closed :: "('nr, 'nc, 'ni :: linorder) tableau \<Rightarrow> bool" where
"bounds_renaming_closed tab = (\<forall> x y. x \<in> fv_tableau tab \<longrightarrow> y \<in> fv_tableau tab \<longrightarrow>
                    x < y \<longrightarrow>  varbounds tab y \<subseteq> varbounds tab x)"

definition successor_varbounds_closed :: "('nr, 'nc, 'ni:: linorder) tableau \<Rightarrow> bool" where
  "successor_varbounds_closed tab = 
     (\<forall> x n r c y. 
         ([<] n r c) \<in> varbounds tab x \<longrightarrow>
         FactFm (AtomR True r x y) \<in> abox tab \<longrightarrow>
         c \<in> varbounds tab y)"

definition contraction_stable :: "('nr, 'nc, 'ni:: linorder) tableau \<Rightarrow> bool" where
  "contraction_stable tab = 
     (\<forall> r y y'.  
        FactFm (AtomR True r y y') \<in> abox tab \<longrightarrow>
        (neq_complete y (abox tab) 
         \<or> (\<forall> x < y. x \<in> fv_abox (abox tab) \<longrightarrow> varbounds tab x \<subseteq> varbounds tab y)))"  

definition expansion_stable :: "('nr, 'nc, 'ni:: linorder) tableau \<Rightarrow> bool" where
  "expansion_stable tab = 
     (\<forall> x \<in> fv_abox (abox tab).  
        (numrestrc_ge_complete x (abox tab) 
         \<or> (\<forall> x' \<in> fv_abox (abox tab). x < x' \<longrightarrow> varbounds tab x \<subseteq> varbounds tab x')))"  

definition initial_tableau :: "('nr, 'nc, 'ni) abox \<Rightarrow> ('nr, 'nc, 'ni) tableau" where
  "initial_tableau ab = \<lparr> abox = ab, 
                         varbounds = (\<lambda> x. if x \<in> fv_abox ab then (all_subconcepts_abox ab) else {}) \<rparr>"



lemma node_concepts_all_subconcepts: "x \<in> fv_abox ab \<Longrightarrow> node_concepts_abox ab x \<subseteq> (all_subconcepts_abox ab)"
by (fastforce simp add: all_subconcepts_abox_def)

lemma is_Inst_fact_mono: "A \<subseteq> B \<Longrightarrow> is_Inst_fact A f \<Longrightarrow> is_Inst_fact B f"
by (auto  split : form.split_asm fact.split)


lemma node_concept_abox_empty [simp]: "node_concepts_abox {} x = {}"
by (simp add: node_concepts_abox_def)

lemma node_concepts_abox_union [simp]: 
   "node_concepts_abox (A \<union> B) x = node_concepts_abox A x \<union> node_concepts_abox B x"
by (unfold node_concepts_abox_def) (auto simp add:  image_def)

lemma node_concepts_abox_inter [simp]: 
   "node_concepts_abox (A \<inter> B) x = node_concepts_abox A x \<inter> node_concepts_abox B x"
by (auto simp add:  image_def node_concepts_abox_def  split: form.split_asm fact.split_asm)

lemma node_concepts_abox_image_FactFm [simp]: 
   "node_concepts_abox ((\<lambda>c. FactFm (Inst x c)) ` C) y = (if x = y then C else {})"
by (auto simp add: node_concepts_abox_def image_def)

lemma node_concepts_abox_insert [simp]: 
   "node_concepts_abox (insert f A) x = 
   (if is_Inst_fact {x} f then {concept_of_Inst_fact f} else {})  \<union> node_concepts_abox A x"
by (unfold node_concepts_abox_def) (auto simp add:  image_def)

lemma fv_abox_empty [simp]: "fv_abox {} = {}"
by (simp add: fv_abox_def)

(* proofs about neq_complete *)

lemma neq_complete_mono: "(x :: 'a :: linorder) < y \<Longrightarrow> neq_complete y ab \<Longrightarrow> neq_complete x ab"
by (simp add: neq_complete_def)

lemma neq_complete_insert_Inst: 
   "fv_concept c \<subseteq> fv_abox ab \<Longrightarrow>
   x' \<in> fv_abox ab \<Longrightarrow>
   neq_complete x (insert (FactFm (Inst x' c)) ab) = neq_complete x ab"
by (auto simp add: neq_complete_def)

lemma neq_complete_insert_InstD: "neq_complete x (insert (FactFm (Inst x' c)) ab) \<Longrightarrow> neq_complete x ab"
by (auto simp add: neq_complete_def)

lemma neq_complete_subset: "ab \<subseteq> ab' \<Longrightarrow> fv_abox ab' \<subseteq> fv_abox ab \<Longrightarrow> 
      neq_complete x ab \<Longrightarrow> neq_complete x ab'"
by (fastforce simp add: neq_complete_def)

lemma neq_complete_not_eq_fact:
     "ab \<subseteq> ab' \<Longrightarrow> fv_abox ab = fv_abox ab' \<Longrightarrow> \<forall> f \<in> ab' - ab. \<not> is_Eq_fact f \<Longrightarrow> 
       neq_complete x ab = neq_complete x ab'"
apply (rule)
apply (erule neq_complete_subset) apply (simp+)
apply (clarsimp simp add: neq_complete_def)
apply (rename_tac z1 z2)
apply (drule_tac x=z1 in spec, simp)
apply (drule_tac x=z2 in spec, simp)
apply (elim disjE)
apply (case_tac "FactFm (Eq False z1 z2) \<in> ab")
apply simp
apply (drule_tac x="FactFm (Eq False z1 z2)" in  bspec) apply fast apply simp
apply (drule_tac x="FactFm (Eq False z2 z1)" in  bspec) apply fast apply simp
done

lemma numrestrc_ge_rule_facts_empty [simp]: "numrestrc_ge_rule_facts c r x {} = {}"
by (simp add: numrestrc_ge_rule_facts_def)


lemma FactFm_Eq_numrestrc_ge_rule_facts:
  "(FactFm (Eq False z1 z2) \<in> numrestrc_ge_rule_facts c r x Y) = 
  (z1 \<in> Y \<and> z2 \<in> Y \<and> z1 < z2)"
by (simp add: numrestrc_ge_rule_facts_def)

(*<*)
end
(*>*)
