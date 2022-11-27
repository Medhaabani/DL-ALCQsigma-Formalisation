theory ALC_Termination imports (*  Decide_satisfiability *) ALC_CompletenessProofs ALC_PrInfrastruc 
Strategies Select "~~/src/HOL/Library/Multiset"
begin


(*---------------------------------------------------------------------------------*)
(* Auxiliary facts *)
(*---------------------------------------------------------------------------------*)

(* TODO: move to ALC_TableauProofs *)
lemma numrestrc_ge_blocked_numrestrc_ge_rule_facts [simp]: 
  "finite (Y :: ('ni :: linorder) set) \<Longrightarrow>
   numrestrc_ge_blocked (numrestrc_ge_rule_facts c r x Y \<union> A) x (card Y) r c"
apply (simp add: numrestrc_ge_blocked_def)
apply (intro exI conjI)
apply assumption
apply (rule refl)
apply (auto simp add: numrestrc_ge_rule_facts_def)+
done


(* TODO: move elsewhere *)
definition subst_free_abox :: "('nr, 'nc, 'ni) abox \<Rightarrow> bool"  where
  "subst_free_abox ab = (\<forall> f\<in> ab. subst_free_form f)"

lemma subst_free_concept_rename_in_concept [rule_format]:
   "subst_free_concept c \<longrightarrow> rename_in_concept c ren = c"
by (induct c) auto

lemma FactFm_AtomR_rename_in_abox_inversion: "x \<noteq> y \<Longrightarrow> 
   (FactFm (AtomR s r x' y') \<in> rename_in_abox ab [ISubst y x]) =
  ((FactFm (AtomR s r x' y') \<in> ab) \<and> x' \<noteq> y \<and> y' \<noteq> y \<or>
  (FactFm (AtomR s r y y') \<in> ab) \<and> x' = x \<and> y' \<noteq> y \<or>
  (FactFm (AtomR s r x' y) \<in> ab) \<and> x' \<noteq> y \<and> y' = x \<or>
  (FactFm (AtomR s r y y) \<in> ab) \<and> x' = x \<and> y' = x)" 
apply (simp add: rename_in_abox_def)
apply (auto simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_AtomR split : if_split_asm)
apply (frule imageI [where f="(\<lambda>f. rename_in_form f [ISubst y x])"], simp)+
done

lemma FactFm_Eq_rename_in_abox_inversion: "x \<noteq> y \<Longrightarrow> 
   (FactFm (Eq s x' y') \<in> rename_in_abox ab [ISubst y x]) =
  ((FactFm (Eq s x' y') \<in> ab) \<and> x' \<noteq> y \<and> y' \<noteq> y \<or>
  (FactFm (Eq s y y') \<in> ab) \<and> x' = x \<and> y' \<noteq> y \<or>
  (FactFm (Eq s x' y) \<in> ab) \<and> x' \<noteq> y \<and> y' = x \<or>
  (FactFm (Eq s y y) \<in> ab) \<and> x' = x \<and> y' = x)" 
apply (simp add: rename_in_abox_def)
apply (auto simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Eq split: if_split_asm)
apply (frule imageI [where f="(\<lambda>f. rename_in_form f [ISubst y x])"], simp)+
done

(* TODO: move elsewhere *)
lemma fv_abox_rename_in_abox_one [simp]:  
   "fv_abox (rename_in_abox ab [ISubst y2 y1]) = 
   (((fv_abox ab) 
     - (if y1 = y2 then {} else if y2 \<in> fv_abox ab then {y2} else {}))
     \<union> (if y1 = y2 then {} else if y2 \<in> fv_abox ab then {y1} else {}))"
apply (clarsimp simp add: subst_free_abox_def fv_abox_def rename_in_abox_def)
apply (rule subset_antisym)
apply (rule subsetI)
apply clarsimp
apply (elim disjE)
apply (clarsimp split: if_split_asm)+
apply (intro conjI)
apply fastforce
apply (rule subsetI)
apply clarsimp
apply fastforce
done

(*---------------------------------------------------------------------------------*)
(* Multisets *)
(*---------------------------------------------------------------------------------*)


definition multstar :: "('a \<times> 'a) set \<Rightarrow> ('a multiset \<times> 'a multiset) set" where
  "multstar r = (mult1 r)\<^sup>*"
  
lemma multstar_Id_mult: "multstar r = Id \<union> mult r"
by (simp add: multstar_def mult_def rtrancl_id_trancl)

lemma multstar_refl [simp]: "(x, x) \<in> multstar r"
by (simp add: multstar_def)

definition "strongly_decreasing K J r =  
   (J \<noteq> {#} \<and> (\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> r))"

lemma mult_union: "(B, D) \<in> mult r \<Longrightarrow> (C + B, C + D) \<in> mult r"
apply (simp add: mult_def)
apply (erule trancl.induct)

apply (fast intro: mult1_union) 
apply (fast intro: trancl_into_trancl mult1_union) 
done


lemma one_step_implies_mult_ws_decreasing2:
  "trans r \<Longrightarrow> 
   strongly_decreasing K J r \<Longrightarrow>
   (I', I) \<in> multstar r \<Longrightarrow>
     (I' + K, I + J) \<in> mult r"
apply (simp add: mult_def)
apply (rule rtrancl_trancl_trancl [where y = "I + K"])

(* case rtrancl *)
apply (simp add: multstar_def rtrancl_eq_or_trancl)
apply (elim disjE) apply clarsimp+

apply (fold mult_def)
apply (subgoal_tac "I' + K = K + I'") 
apply (subgoal_tac "I + K = K + I") 
apply (simp add: mult_union)
  apply (metis mult_union union_commute)
apply (rule union_commute)+

(* case trancl *)

  apply (simp add: strongly_decreasing_def)+
apply (clarsimp simp add: one_step_implies_mult) 
done


(*---------------------------------------------------------------------------------*)
(* Termination of transition system *)
(*---------------------------------------------------------------------------------*)

(* ------------------------------------------------ *)
(* Tableau potential *)
(* ------------------------------------------------ *)

(*
Important: 
- change rule system so that no nodes are deleted, but only stored in a list of equivalence classes
  \<longrightarrow> useful for later when reconstructing interpretations
  \<longrightarrow> also necessary for transformations that contract two nodes with identical decoration
- consequence: during a transf, the node set increases monotonically
- it remains to be shown that for each transf, 
  all old nodes only have \<le> potential, one old node has < potential (potential difference diff)
  for each new node, the potential is less than diff
*)

(* potential of a node in an abox:
  (act, bound, deco) where: 
  - act indicates whether node is active
  - bound is the decoration bound as set of concepts; deco \<subset> bound 
  - deco is the actual decoration
*)
type_synonym 'a potential = "(bool \<times>  (nat \<times> (('a set) \<times> ('a set)) \<times>(nat \<times> nat)))"
(* abstract abox *)
type_synonym 'a tableau_potential = "'a potential multiset"

definition "bool_ord = {(b1 :: bool, b2). b1 < b2}"
definition "nat_ord = {(n1 :: nat, n2). n1 < n2}"

definition "superset_ord = {(a1, a2). a2 \<subset> a1}"

definition bounded_measure_ord :: "((('a set) \<times> ('a set)) \<times> (('a set) \<times> ('a set))) set" where
  "bounded_measure_ord = {((b1, d1),  (b2, d2)). finite b2 \<and> b1 \<subseteq> b2 \<and> b2 \<supseteq> d1 \<and> d1 \<supset> d2}"

lemma wf_bounded_measure_ord [simp]: "wf bounded_measure_ord"
by (rule wf_bounded_set [of bounded_measure_ord fst snd])
 (simp add: bounded_measure_ord_def split_def)
 
definition potential_ord :: "'a potential rel" where
   "potential_ord  = bool_ord <*lex*> nat_ord <*lex*>bounded_measure_ord <*lex*> nat_ord <*lex*> nat_ord"

(*   lemma "(False < True)" by simp *)
lemma trans_bool_ord [simp]: "trans bool_ord"
by (simp add: trans_def bool_ord_def)

lemma wf_bool_ord [simp]: "wf bool_ord"
by (simp add: wf_def  bool_ord_def)

lemma trans_nat_ord [simp]: "trans nat_ord"
by (simp add: trans_def nat_ord_def)

lemma wf_nat_ord [simp]: "wf nat_ord"
by (simp add:  nat_ord_def wf_less)

lemma trans_bounded_measure_ord [simp]: "trans bounded_measure_ord"
by (auto simp add: trans_def bounded_measure_ord_def)

lemma trans_potential_ord [simp]: "trans potential_ord"
by (simp add: potential_ord_def trans_lex_prod)

lemma wf_potential_ord [simp]: "wf potential_ord"
by (simp add: potential_ord_def wf_lex_prod)

lemma nat_ord_or_eq: "((a, b) \<in> nat_ord \<or> a = b) = (a \<le> b)"
by (auto simp add: nat_ord_def)

definition card_having_image :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> nat" where
  "card_having_image =  (\<lambda> A f b. if finite (f ` A) then card {a \<in> A. f a = b} else 0)"
    
lemma finite_card_having_image [simp]: "finite {x. 0 < card_having_image A f x}"
  apply (simp add: card_having_image_def)
  apply (case_tac "finite (f ` A)")
  apply (erule rev_finite_subset)
  apply clarsimp
  apply (case_tac "{a \<in> A. f a = x} = {}")
  apply auto
done

lemma card_having_image_empty [simp]: 
  "card_having_image {} f = (\<lambda> b. 0)"                            
by (simp add: card_having_image_def)

lemma card_having_image_singleton: 
  "card_having_image {x} f = (\<lambda> b. if (f x) = b then 1 else 0)" 
apply (simp add: card_having_image_def fun_eq_iff)
apply (subgoal_tac "{a. a = x \<and> f a = f x} = {x}")
apply simp+
apply blast
done

lemma card_having_image_union: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow>
   card_having_image (A \<union> B) f = (\<lambda> x. card_having_image A f x + card_having_image B f x)"
apply (clarsimp simp add: card_having_image_def fun_eq_iff)
apply (subgoal_tac "{a. (a \<in> A \<or> a \<in> B) \<and> f a = x} = ({a \<in> A. f a = x} \<union> {a \<in> B. f a = x})")
apply (simp only:)
apply (rule card_Un_disjoint)
apply auto
done

lemma card_having_image_insert [simp]: "finite B \<Longrightarrow>  a \<notin> B \<Longrightarrow>
    card_having_image (insert a B) f =
    (\<lambda>x. (if f a = x then 1 else 0) + card_having_image B f x)"
apply (subgoal_tac "card_having_image ({a} \<union> B) f = 
       (\<lambda> x. card_having_image {a} f x + card_having_image B f x)")
  prefer 2 apply (rule card_having_image_union) 
apply simp_all
apply (simp add: card_having_image_singleton)
done

lemma card_having_image_in_multiset [simp]: "card_having_image A f \<in> multiset"
by (simp add: multiset_def)

lemma card_having_image_for_finite: 
   "finite A \<Longrightarrow> card_having_image A f = (\<lambda> b. card {a \<in> A. f a = b})"
by (simp add: card_having_image_def fun_eq_iff)

lift_definition set_image_multiset :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b multiset" is "card_having_image"
by simp 

lemma set_image_multiset_empty [simp]: 
  "set_image_multiset {} f = {#}"
by (simp add: set_image_multiset_def zero_multiset_def)

lemma set_image_multiset_singleton [simp]: 
  "set_image_multiset {x} f = {# f x #}"
apply (simp add: set_image_multiset_def add_mset_def)
apply (rule arg_cong [where f=Abs_multiset])
apply (simp add: fun_eq_iff)
done

lemma set_image_multiset_union: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> C = (A \<union> B)
   \<Longrightarrow> set_image_multiset C f = set_image_multiset A f + set_image_multiset B f"
by (simp add: set_image_multiset_def plus_multiset_def card_having_image_union)

lemma set_image_multiset_insert: "finite B \<Longrightarrow> a \<notin> B
   \<Longrightarrow> set_image_multiset (insert a B) f =  {# f a #} + set_image_multiset B f"
  apply (simp add: set_image_multiset_def plus_multiset_def card_having_image_union )
  by (metis One_nat_def count_empty)
  

definition card_ge_applic_set ::  "('nr, 'nc, 'ni::linorder) abox \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) form set" where
  "card_ge_applic_set ab x = {f \<in> ab. numrestrc_ge_applicable f ab \<and> inst_of_Inst_fact f = x}"

definition card_ge_applic ::  "('nr, 'nc, 'ni::linorder) abox \<Rightarrow> 'ni \<Rightarrow> nat" where
  "card_ge_applic ab x = card (card_ge_applic_set ab x)"

definition neq_unrelated :: "('nr, 'nc, 'ni::linorder) abox \<Rightarrow> 'ni \<Rightarrow> ('ni \<times> 'ni) set" where
  "neq_unrelated ab x = {(z1, z2). 
        z1 \<le> x \<and> z2 \<le> x 
      \<and> z1 \<in> fv_abox ab \<and> z2 \<in> fv_abox ab 
      \<and> (FactFm (Eq False z1 z2) \<notin> ab) \<and> (FactFm (Eq False z2 z1) \<notin> ab)}"


definition pair_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('a * 'b)" where "pair_fun f a = (a, f a)"

definition node_potential :: "('nr, 'nc, 'ni::linorder) tableau \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) concept potential" where
  "node_potential tab x = (node_active tab x,
                           card (varbounds tab x),
                           (varbounds tab x, node_concepts tab x),
                           card (neq_unrelated (abox tab) x),
                           card_ge_applic (abox tab) x)"

definition pair_node_potential :: "('nr, 'nc, 'ni::linorder) tableau \<Rightarrow> 'ni \<Rightarrow> ('ni * ('nr, 'nc, 'ni) concept potential)" where
  "pair_node_potential tab = pair_fun (node_potential tab)"

definition node_potential_for_tableau :: "('nr, 'nc, 'ni::linorder) tableau \<Rightarrow> ('ni * ('nr, 'nc, 'ni) concept potential) set" where
    "node_potential_for_tableau tab =  ((pair_node_potential tab) ` (fv_tableau tab))"

definition tableau_potential :: "('nr, 'nc, 'ni::linorder) tableau \<Rightarrow> ('nr, 'nc, 'ni) concept tableau_potential" where
  "tableau_potential tab = (if contains_clash (abox tab)
                            then {#}
                            else set_image_multiset (node_potential_for_tableau tab) snd)"

definition tableau_potential_for_set :: "('nr, 'nc, 'ni::linorder) tableau \<Rightarrow> 'ni set \<Rightarrow> ('nr, 'nc, 'ni) concept tableau_potential" where
  "tableau_potential_for_set tab A = (set_image_multiset (pair_node_potential tab ` A) snd)"
  
definition is_fact_tableau :: "('nr, 'nc, 'ni) tableau \<Rightarrow> bool" where
  "is_fact_tableau tab = (\<forall> f \<in> (abox tab). is_fact f)"  

definition is_nontrivial_tableau :: "('nr, 'nc, 'ni) tableau \<Rightarrow> bool" where
  "is_nontrivial_tableau tab = (fv_abox (abox tab) \<noteq> {})"
  
lemma tableau_potential_tableau_potential_for_set:
  "tableau_potential tab = 
       (if contains_clash (abox tab)
                            then {#}
                            else tableau_potential_for_set tab (fv_tableau tab))"
by (simp add: tableau_potential_def tableau_potential_for_set_def node_potential_for_tableau_def)

definition tableau_potential_ord :: "('nr, 'nc, 'ni) concept tableau_potential rel" where
  "tableau_potential_ord  = mult potential_ord"
  
lemma wf_tableau_potential_ord [simp]: "wf tableau_potential_ord"
by (simp add: tableau_potential_ord_def wf_mult)


definition (* tableau_consistent_ord :: "('nr, 'nc, 'ni) concept tableau_potential rel" where*)
  "tableau_consistent_ord = {(t, t'). (\<not> contains_clash (abox t)) < (\<not> contains_clash (abox t')) } "

lemma wf_tableau_consistent_ord [simp]: "wf tableau_consistent_ord"
by (simp add: wf_def tableau_consistent_ord_def)

definition (* cons_tableau_potential_ord :: "('nr, 'nc, 'ni) concept tableau_potential rel" where*)
  "cons_tableau_potential_ord  = tableau_consistent_ord <*lex*> tableau_potential_ord"



(* ------------------------------------------------ *)
(* Specific properties of the above functions *)
(* ------------------------------------------------ *)


lemma inj_pair_fun [simp]: "inj (pair_fun f)"
by (simp add: inj_on_def pair_fun_def)

lemma snd_pair_fun [simp]:  "snd (pair_fun f x) = f x"
by (simp add: pair_fun_def)

lemma snd_pair_node_potential [simp]:
  "snd (pair_node_potential tab x) = node_potential tab x"
by (simp add: pair_node_potential_def)

lemma inj_pair_node_potential [simp]: "inj (pair_node_potential tab)"
by (simp add: pair_node_potential_def)

lemma finite_node_concepts_abox [simp]: "finite ab \<Longrightarrow> finite (node_concepts_abox ab x)"
by (simp add: node_concepts_abox_def)

lemma finite_node_concepts [simp]: "finite (abox tab) \<Longrightarrow> finite (node_concepts tab x)"
by (simp add: node_concepts_def)

lemma var_in_fv_tableau:
"f \<in> abox tab \<Longrightarrow> x \<in> fv_form f \<Longrightarrow> x \<in> fv_tableau tab"
by (fastforce simp add: fv_abox_def)


lemma FactFm_Inst_node_concepts:  "FactFm (Inst x c) \<in> abox tab \<Longrightarrow> c \<in> node_concepts tab x"
by (simp add: node_concepts_def) (fastforce simp add: node_concepts_abox_def image_def)

lemma node_concepts_FactFm_Inst: "c \<in> node_concepts tab x \<Longrightarrow> FactFm (Inst x c) \<in> abox tab"
apply (auto simp add: node_concepts_def node_concepts_abox_def image_def)
apply (auto split : form.split_asm)
apply (auto split : fact.split_asm)
done

lemma FactFm_Inst_node_concepts_eq:
  "(FactFm (Inst x c) \<in> abox tab) = (c \<in> node_concepts tab x)"
by (fast intro: FactFm_Inst_node_concepts node_concepts_FactFm_Inst)


lemma card_having_image_finite_fv_tableau [simp]:
   "finite (fv_tableau tab) \<Longrightarrow> 
        card_having_image (node_potential_for_tableau tab) f = 
         (\<lambda>b. card {a \<in> node_potential_for_tableau tab. f a = b})"
apply (subgoal_tac "finite (node_potential_for_tableau tab)")
apply (erule card_having_image_for_finite)
apply (simp add: node_potential_for_tableau_def)
done


(* TODO: apparently not needed
lemma card_having_image_tableau_potential_decreasees [rule_format]:
   "\<forall> y. card_having_image (node_potential_for_tableau tab') snd y
     \<le> card_having_image (node_potential_for_tableau tab) snd y \<Longrightarrow>
     card_having_image (node_potential_for_tableau tab') snd x
     < card_having_image (node_potential_for_tableau tab) snd x
      \<Longrightarrow> tableau_potential tab' \<subset># tableau_potential tab"
apply (simp add:tableau_potential_def  subset_mset_def subseteq_mset_def )
apply (simp add: set_image_multiset_def)
apply (simp add: Abs_multiset_inject)
apply auto
done
*)

lemma set_mset_Abs_multiset: "finite {x. 0 < card (C x)} \<Longrightarrow>
    set_mset (Abs_multiset (\<lambda>b. card (C b))) = {x. 0 < card (C x)}"
apply (subgoal_tac "(\<lambda>b. card (C b)) \<in> multiset")
apply (simp add: set_mset_def)
apply (simp add: multiset_def)
done


lemma set_mset_set_image_multiset:
  "finite A \<Longrightarrow>  set_mset (set_image_multiset (pair_fun f ` A) snd) = f ` A"
apply (simp add: image_def set_mset_def set_image_multiset.rep_eq pair_fun_def 
  card_having_image_for_finite)
apply (fastforce simp add: card_gt_0_iff)
done

lemma set_mset_tableau_potential_for_set:
  "finite A \<Longrightarrow> set_mset (tableau_potential_for_set tab A) = node_potential tab ` A"
by (simp add: tableau_potential_for_set_def pair_node_potential_def set_mset_set_image_multiset)



lemma tableau_potential_for_set_empty [simp]: "tableau_potential_for_set tab {} = {#}"
by (simp add: tableau_potential_for_set_def) 


lemma card_having_image_entails_empty:
   "finite S \<Longrightarrow> \<forall>a. card_having_image S f a = 0 \<Longrightarrow> S = {}"
by (auto simp add: card_having_image_def)


lemma set_image_multiset_entails_empty:
  "finite S \<Longrightarrow> (set_image_multiset S f = {#}) = (S = {})" 
apply (rule iffI) prefer 2 apply simp
apply (simp add: set_image_multiset_def  multiset_eq_iff card_having_image_entails_empty)
done


lemma tableau_potential_for_set_empty_equiv:
   "finite S \<Longrightarrow> (tableau_potential_for_set tab S = {#}) = (S = {})"
apply (simp add: tableau_potential_for_set_def)
apply (rule trans)
apply (rule set_image_multiset_entails_empty) 
apply simp+
done

(* TODO: still needed after redef of is_nontrivial_tableau ? 
lemma tableau_potential_clash_free_nontrivial: 
      "\<not> contains_clash (abox tab) \<Longrightarrow>
       is_nontrivial_tableau tab \<Longrightarrow> 
       finite (fv_tableau tab) \<Longrightarrow>
       tableau_potential tab \<noteq>  {#}"    
apply (clarsimp simp add: is_nontrivial_tableau_def)
apply (clarsimp simp add: tableau_potential_tableau_potential_for_set 
       split add: form.split_asm fact.split_asm)
apply (fastforce simp add: tableau_potential_for_set_empty_equiv dest: var_in_fv_tableau)+
done
*)
lemma tableau_potential_clash_free_nontrivial: 
      "\<not> contains_clash (abox tab) \<Longrightarrow>
       is_nontrivial_tableau tab \<Longrightarrow> 
       finite (fv_tableau tab) \<Longrightarrow>
       tableau_potential tab \<noteq>  {#}"    
apply (clarsimp simp add: is_nontrivial_tableau_def)
apply (clarsimp simp add: tableau_potential_tableau_potential_for_set 
       split : form.split_asm fact.split_asm)
apply (simp add: tableau_potential_for_set_empty_equiv)
done

lemma card_having_image_pair_fun: "finite A \<Longrightarrow> 
    card_having_image ((pair_fun f) ` A) snd b =
    card {a \<in> A. snd (pair_fun f a) = b}"
apply (simp add: card_having_image_def)
apply (insert card_image [where f = "pair_fun f" and A = "{a \<in> A. snd (pair_fun f a) = b}"])
apply (subgoal_tac "inj_on (pair_fun f) {a \<in> A. snd (pair_fun f a) = b}")
apply simp
apply (drule sym)
apply (simp only:)
apply (rule arg_cong [where f=card])
apply fastforce
apply (simp add: inj_on_def pair_fun_def)
done

lemma card_having_image_pair_node_potential: "finite A \<Longrightarrow> 
    card_having_image (pair_node_potential tab ` A) snd =
    (\<lambda> b. card {a \<in> A. snd (pair_node_potential tab a) = b})"
by (simp add: pair_node_potential_def card_having_image_pair_fun fun_eq_iff)



(* ------------------------------------------------ *)
(* Decompositions of sets etc *)
(* ------------------------------------------------ *)


lemma tableau_potential_for_set_union [simp]: 
    "finite A \<Longrightarrow> finite B \<Longrightarrow>  A \<inter> B = {} \<Longrightarrow> C =  (A \<union> B) \<Longrightarrow>
    tableau_potential_for_set tab C = 
    tableau_potential_for_set tab A + tableau_potential_for_set tab B"
apply (simp add: tableau_potential_for_set_def image_Un)
apply (rule set_image_multiset_union)
apply simp_all
apply (simp add: image_Int [THEN sym]) 
done


(* ------------------------------------------------ *)
(* Variance / invariance properties *)
(* ------------------------------------------------ *)


(* General invariance *)

(* the converse does not hold: tab' and tab can have the same potential, 
   without being pointwise identical *)
lemma tableau_potential_for_set_same:
  "finite A \<Longrightarrow>
   \<forall> a \<in> A. node_potential tab' a = node_potential tab a \<Longrightarrow> 
   tableau_potential_for_set tab' A = tableau_potential_for_set tab A"
apply (simp add: tableau_potential_for_set_def)
apply (simp add: set_image_multiset_def)
apply (rule arg_cong [where f=Abs_multiset])
apply (clarsimp simp add: card_having_image_pair_node_potential fun_eq_iff)
apply (rule arg_cong [where f=card])
apply fastforce
done


lemma strongly_decreasing_tableau_potential_for_set : "finite A \<Longrightarrow>
         \<forall>x\<in>A. (node_potential tab' x, node_potential tab x)
                \<in> potential_ord \<or>
                node_potential tab' x = node_potential tab x \<Longrightarrow>
         S =
         {a \<in> A. node_potential tab' a \<noteq> node_potential tab a} \<Longrightarrow>
         S \<noteq> {} \<Longrightarrow>
         strongly_decreasing (tableau_potential_for_set tab' S)
          (tableau_potential_for_set tab S) potential_ord"

apply (clarsimp simp add: strongly_decreasing_def)
apply (rule conjI)

apply (fastforce simp add: tableau_potential_for_set_empty_equiv)
apply (rule ballI)
apply (rename_tac x k)
apply (simp add: set_mset_tableau_potential_for_set)
apply (simp add: image_def)
apply (elim exE conjE)
apply (rename_tac x k xk)
apply (drule_tac x=xk in bspec)
apply fastforce+
done


lemma tableau_potential_for_set_multstar: 
   "finite A \<Longrightarrow> 
   \<forall> x \<in> A. (node_potential tab' x,  node_potential tab x) \<in> potential_ord\<^sup>= \<Longrightarrow>
   (tableau_potential_for_set tab' A, tableau_potential_for_set tab A) \<in> multstar potential_ord"
apply (case_tac "tableau_potential_for_set tab' A = tableau_potential_for_set tab A")
apply (simp add: multstar_Id_mult)+

apply (subgoal_tac "\<exists> S. S = {a \<in> A. node_potential tab' a \<noteq>  node_potential tab a}")
  prefer 2 apply (intro exI) apply (rule refl)
apply (elim exE)
apply (case_tac "S = {}")
apply (simp add: multstar_Id_mult tableau_potential_for_set_same)


(* subgoal 1 *)
apply (subgoal_tac "tableau_potential_for_set tab' A =
                    tableau_potential_for_set tab' (A - S) + tableau_potential_for_set tab' S")
(* subgoal 2 *)
apply (subgoal_tac "tableau_potential_for_set tab A =
                    tableau_potential_for_set tab (A - S) + tableau_potential_for_set tab S")
(* subgoal 3 *)
apply (subgoal_tac "tableau_potential_for_set tab' (A - S) = tableau_potential_for_set tab (A - S)")
(* subgoal 4 *)
apply (subgoal_tac 
   "strongly_decreasing (tableau_potential_for_set tab' S) (tableau_potential_for_set tab S) potential_ord")
(* subgoal 5 *)
apply (subgoal_tac "tableau_potential_for_set tab S \<noteq> {#}")

apply (simp only:)
apply (rule one_step_implies_mult)
apply simp
apply simp
apply (simp add: strongly_decreasing_def)

(* proof subgoal 5 *)
apply (simp add: tableau_potential_for_set_empty_equiv)

(* proof subgoal 4 *)
apply (rule strongly_decreasing_tableau_potential_for_set) apply assumption+

(* proof subgoal 3 *)
apply (rule tableau_potential_for_set_same) apply simp apply simp
(* proof subgoal 2 *)
apply (rule tableau_potential_for_set_union) apply simp apply simp apply fast apply fast
(* proof subgoal 1 *)
apply (rule tableau_potential_for_set_union) apply simp apply simp apply fast apply fast
done



lemma node_active_same: 
"fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow> node_active tab' x = node_active tab x"
by (simp add: node_active_def)


(* Invariance for specific rules *)



lemma fv_abox_same_add_subconcepts: "FactFm (Inst x c) \<in> ab \<Longrightarrow>
    ab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> ab \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow> 
    fv_abox ab' = fv_abox ab"
apply (case_tac "C = {}")
apply simp

apply (subgoal_tac "fv_abox ((\<lambda>c. FactFm (Inst x c)) ` C) = insert x (\<Union>x\<in>C. fv_concept x)")
  prefer 2 apply (simp add: fv_abox_def)
apply (drule fv_form_fv_abox)
apply simp
apply (drule sub_concepts_pn_incl_fv_concept)
apply blast
done

lemma node_active_same_extend:
    "abox tab' = E \<union> abox tab \<Longrightarrow>
    fv_abox E \<subseteq> fv_abox (abox tab) \<Longrightarrow>
    node_active tab' y = node_active tab y"
by (fastforce simp add: node_active_def)

(* TODO: check whether 
node_active tab y = node_active tab' y
or
node_active tab' y = node_active tab y
is more appropriate
*)
lemma node_active_same_add_subconcepts: 
    "FactFm (Inst x c) \<in> abox tab \<Longrightarrow>
    abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>
    node_active tab y = node_active tab' y"
by (simp only: node_active_def fv_abox_same_add_subconcepts)


(* properties of neq_unrelated *)
definition "fv_abox_bounded ab x = {z \<in> fv_abox ab. z \<le> x}"

lemma neq_unrelated_antimono: "ab \<subseteq> ab' \<Longrightarrow>
       fv_abox_bounded ab' x \<subseteq> fv_abox_bounded ab x \<Longrightarrow> 
       neq_unrelated ab' x \<subseteq> neq_unrelated ab x"
by (fastforce simp add: neq_unrelated_def fv_abox_bounded_def) 

lemma node_concepts_change_add_subconcepts_this: 
    "abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
    node_concepts tab' x = C \<union> node_concepts tab x"
by (simp add: node_concepts_def)

lemma node_concepts_same_add_subconcepts_other: 
    "abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    node_concepts tab' y = node_concepts tab y"
by (simp add: node_concepts_def)

(* TODO: really used ? *)
lemma node_concepts_subconcepts_inter: "
   (\<lambda>c. FactFm (Inst x c)) ` C \<inter> abox tab = {} \<Longrightarrow>  
   C \<inter> node_concepts tab x = {}"
apply (simp add: node_concepts_def)
apply (subgoal_tac "(node_concepts_abox ((\<lambda>c. FactFm (Inst x c)) ` C \<inter> abox tab) x) = {}")
  prefer 2 apply simp
apply (simp (no_asm_use))
done


lemma node_concepts_subset_add_subconcepts:
  "abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
   \<exists> c \<in> C. (FactFm (Inst x c)) \<notin> abox tab  \<Longrightarrow>
    node_concepts tab x \<subset> node_concepts tab' x"
by (drule node_concepts_change_add_subconcepts_this) (fastforce simp add:  FactFm_Inst_node_concepts_eq)


(* TODO: maybe move elsewhere *)

lemma numrestrc_ge_blocked_mono: 
  "numrestrc_ge_blocked A x n r c \<Longrightarrow> A \<subseteq> B \<Longrightarrow> numrestrc_ge_blocked B x n r c"
by (fastforce simp add: numrestrc_ge_blocked_def)

(* TODO: move elsewhere *)
lemma fv_abox_mono: "ab \<subseteq> ab' \<Longrightarrow> fv_abox ab \<subseteq> fv_abox ab'"
by (auto simp add: fv_abox_def)


(* TODO: remove 
lemma numrestrc_ge_applicable_antimono:
   "numrestrc_ge_applicable f A \<Longrightarrow>
   f = (FactFm (Inst x ([\<ge>] n r c)))  \<Longrightarrow> 
   B \<subseteq> A \<Longrightarrow> 
   neq_complete x B \<Longrightarrow>
   f \<in> B \<Longrightarrow>  numrestrc_ge_applicable f B"
by (fastforce simp add: numrestrc_ge_applicable.simps numrestrc_ge_blocked_mono)
*)
lemma numrestrc_ge_applicable_antimono:
   "numrestrc_ge_applicable f A \<Longrightarrow>
   f = (FactFm (Inst x ([\<ge>] n r c)))  \<Longrightarrow> 
   B \<subseteq> A \<Longrightarrow> 
   f \<in> B \<Longrightarrow>  numrestrc_ge_applicable f B"
by (fastforce simp add: numrestrc_ge_applicable.simps numrestrc_ge_blocked_mono)


(* TODO: try to replace inst_of_Inst_fact by is_Inst_fact *)
(* TODO: move elsewhere *)
lemma is_Inst_fact_inst_of_Inst_fact:
   "is_Inst_fact {x} f \<Longrightarrow> inst_of_Inst_fact f = x"
apply (case_tac f)
apply (auto simp add: inst_of_Inst_fact_def split : fact.split)
done

lemma is_Inst_fact_unfold: 
   "is_Inst_fact xs fn = (\<exists> x c. fn = FactFm (Inst x c) \<and> (x \<in> xs))"
by (auto simp add: split: form.split fact.split)

lemma card_ge_applic_set_union_incl:
  "\<forall> f \<in> B. \<not> is_Inst_fact {x} f \<Longrightarrow>
  neq_complete x A \<Longrightarrow>
   card_ge_applic_set (B \<union> A) x \<subseteq>  card_ge_applic_set A x"
apply (clarsimp simp add: card_ge_applic_set_def inst_of_Inst_fact_def simp del: is_Inst_fact.simps)
apply (elim disjE)
apply fastforce
apply (clarsimp simp add: numrestrc_ge_applicable.simps)
apply (drule numrestrc_ge_blocked_mono [where B="B \<union> A"])
apply fast+
done

(*
lemma card_ge_applic_union:
  "finite A \<Longrightarrow> \<forall> f\<in> B. numrestrc_ge_applicable f (B \<union> A) \<longrightarrow> inst_of_Inst_fact f \<noteq> y 
  \<Longrightarrow> card_ge_applic (B \<union> A) y \<le> card_ge_applic A y"
   apply (simp add: card_ge_applic_def)
   apply (rule card_mono) apply (simp add: card_ge_applic_set_def)
   apply (clarsimp simp add: card_ge_applic_set_def del: numrestrc_ge_applicable_cases)
   apply (elim disjE)
   apply (rename_tac f)
   apply (drule_tac x=f in bspec) apply simp+
   apply (erule numrestrc_ge_applicable_antimono) defer apply simp+
done
*)

lemma card_ge_applic_antimono_image:
  "x \<noteq> y \<Longrightarrow> finite A \<Longrightarrow> 
  card_ge_applic ((\<lambda>c. FactFm (Inst x c)) ` C \<union> A) y \<le> card_ge_applic A y"
apply (simp add: card_ge_applic_def)
apply (rule card_mono) apply (simp add: card_ge_applic_set_def)
apply (clarsimp simp add: card_ge_applic_set_def del: numrestrc_ge_applicable_cases)
apply (clarsimp simp add: numrestrc_ge_applicable.simps inst_of_Inst_fact_def)
apply (intro conjI)
apply (fastforce simp add: image_def)
apply (intro notI)
apply (drule_tac B=" ((\<lambda>c. FactFm (Inst x c)) ` C \<union> A)" in  numrestrc_ge_blocked_mono) 
apply fast apply fast
(*apply (fastforce simp add: neq_complete_def)*)
done


lemma neq_complete_numrestrc_ge_rule_facts:
   "neq_complete z (numrestrc_ge_rule_facts c r x Y \<union> A) \<Longrightarrow>
       \<forall> y\<in> Y. (z::'a::linorder) < y \<Longrightarrow> neq_complete z A"
apply (simp add: neq_complete_def FactFm_Eq_numrestrc_ge_rule_facts)
apply (subgoal_tac "\<forall> z' \<le> z. z' \<notin> Y") prefer 2 apply fastforce
apply simp
done

lemma card_ge_applic_numrestrc_ge_rule_facts_le: "finite A \<Longrightarrow> (z::'a::linorder) \<notin> Y \<Longrightarrow>
          \<forall> y\<in> Y. (z::'a::linorder) < y \<Longrightarrow>
          card_ge_applic (numrestrc_ge_rule_facts c r x Y \<union> A) z  \<le> card_ge_applic A z"
apply (simp add: card_ge_applic_def)
apply (rule card_mono) apply (simp add: card_ge_applic_set_def)
apply (clarsimp simp add: card_ge_applic_set_def del: numrestrc_ge_applicable_cases)
apply (clarsimp simp add: numrestrc_ge_applicable.simps inst_of_Inst_fact_def)
apply (elim disjE)
apply (simp add: numrestrc_ge_rule_facts_def)
apply (intro conjI)
apply (fastforce simp add: image_def)
apply (intro notI)
apply (drule_tac B=" (numrestrc_ge_rule_facts c r x Y \<union> A)" in  numrestrc_ge_blocked_mono) 
apply fast apply fast
(* apply (simp add: neq_complete_numrestrc_ge_rule_facts) *)
done

(*
lemma card_ge_applic_numrestrc_ge_rule_facts_eq:
  "finite A \<Longrightarrow> z \<notin> Y \<Longrightarrow> z \<noteq> x \<Longrightarrow> 
   card_ge_applic (numrestrc_ge_rule_facts c r x Y \<union> A) z = card_ge_applic A z"
apply (clarsimp simp add:  numrestrc_ge_rule_facts_def)
apply (clarsimp simp add: card_ge_applic_def)
oops
*)

lemma card_ge_applic_set_numrestrc_ge_rule_facts_other:
   "z \<notin> Y \<Longrightarrow>
   neq_complete z A \<Longrightarrow>
    (card_ge_applic_set (numrestrc_ge_rule_facts c r x Y \<union> A) z)
    \<subseteq>(card_ge_applic_set A z)"
apply (simp add:  numrestrc_ge_rule_facts_def)
apply (rule card_ge_applic_set_union_incl)
apply (fastforce simp add: inst_of_Inst_fact_def)
apply assumption
done

lemma card_ge_applic_numrestrc_ge_rule_facts_for_applicable: 
 "finite A \<Longrightarrow> x \<notin> Y \<Longrightarrow> finite (Y :: ('ni :: linorder) set) \<Longrightarrow> 
   numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] (card Y) r c))) A \<Longrightarrow>
   neq_complete x A \<Longrightarrow>
  card_ge_applic (numrestrc_ge_rule_facts c r x Y \<union> A) x < card_ge_applic A x"
apply (clarsimp simp add:  card_ge_applic_def)
apply (rule psubset_card_mono)
apply (simp add: card_ge_applic_set_def)
apply (subgoal_tac "card_ge_applic_set (numrestrc_ge_rule_facts c r x Y \<union> A) x
    \<subseteq> card_ge_applic_set A x")
   prefer 2 apply (erule card_ge_applic_set_numrestrc_ge_rule_facts_other) apply assumption
apply (subgoal_tac "FactFm (Inst x ([\<ge>] (card Y) r c)) \<in>  card_ge_applic_set A x")
apply (subgoal_tac "FactFm (Inst x ([\<ge>] (card Y) r c)) \<notin>  card_ge_applic_set (numrestrc_ge_rule_facts c r x Y \<union> A) x")
apply fast
apply (clarsimp simp add: card_ge_applic_set_def)+
apply (simp add: inst_of_Inst_fact_def numrestrc_ge_applicable.simps)
done


lemma in_node_concepts_abox: "(c \<in> node_concepts_abox A x) = (FactFm (Inst x c) \<in> A)"
apply (auto simp add: node_concepts_abox_def image_def)
apply (auto split : "form.split_asm" fact.split_asm form.split)
done

lemma node_concepts_abox_inclusion: "node_concepts_abox A y2 \<subseteq> node_concepts_abox A y1 \<Longrightarrow> 
 FactFm (Inst y2 c) \<in> A \<Longrightarrow>
 FactFm (Inst y1 c) \<in> A"
by (drule_tac c=c in subsetD) (simp add: in_node_concepts_abox)+
 
lemma card_ge_applic_rename_in_abox:
    "finite A \<Longrightarrow> y1 \<noteq> y2 \<Longrightarrow> subst_free_abox A \<Longrightarrow>
    \<not> contains_clash (rename_in_abox A [ISubst y2 y1]) \<Longrightarrow>
     node_concepts_abox A y2 \<subseteq> node_concepts_abox A y1 \<Longrightarrow>
     card_ge_applic (rename_in_abox A [ISubst y2 y1]) y1 \<le> card_ge_applic A y1"
apply (simp add: card_ge_applic_def)
apply (rule card_mono) apply (simp add: card_ge_applic_set_def)
apply (clarsimp simp add: card_ge_applic_set_def inst_of_Inst_fact_def)
apply (simp add: numrestrc_ge_applicable.simps)
apply (clarsimp simp add: rename_in_abox_inversion)
apply (clarsimp simp add: rename_in_abox_inversion rename_in_form_inversion_FactFm 
  rename_in_fact_inversion_Inst)
apply (simp add: subst_free_abox_def)
apply (rename_tac n r c x cx)
apply (subgoal_tac "subst_free_form (FactFm (Inst x cx))") prefer 2 apply fast
apply (simp add:  subst_free_concept_rename_in_concept)
apply (intro conjI)
apply (clarsimp split : if_split_asm)
apply (erule node_concepts_abox_inclusion, assumption)
apply (subgoal_tac "\<not> numrestrc_ge_blocked
           (rename_in_abox A [ISubst y2 y1])
           (rename_in_var y1 [ISubst y2 y1]) n r
           (rename_in_concept c [ISubst y2 y1])")
apply (erule numrestrc_ge_not_blocked, assumption)
apply (rule refl)+
apply simp
apply (subgoal_tac "subst_free_form (FactFm (Inst y2 ([\<ge>] n r c)))") prefer 2 apply (clarsimp split: if_split_asm)
apply (clarsimp split: if_split_asm)
apply (simp add:  subst_free_concept_rename_in_concept)+
(* TODO: continue here - open neq_complete goal *)
done

(* TODO: can be removed
lemma card_ge_applic_rename_in_abox:
    "finite A \<Longrightarrow> y1 \<noteq> y2 \<Longrightarrow> subst_free_abox A \<Longrightarrow>
    \<not> contains_clash (rename_in_abox A [ISubst y2 y1]) \<Longrightarrow>
     node_concepts_abox A y2 \<subseteq> node_concepts_abox A y1 \<Longrightarrow>
     card_ge_applic (rename_in_abox A [ISubst y2 y1]) y1 \<le> card_ge_applic A y1"
by (simp add:  card_ge_applic2_rename_in_abox)
*)

(* TODO: open neq_complete goal *)
lemma card_ge_applic_rename_in_abox_other:
  "finite A \<Longrightarrow> x \<noteq> y1 \<Longrightarrow> x \<noteq> y2 \<Longrightarrow> subst_free_abox A \<Longrightarrow>
    \<not> contains_clash (rename_in_abox A [ISubst y2 y1]) \<Longrightarrow>
   card_ge_applic (rename_in_abox A [ISubst y2 y1]) x \<le> card_ge_applic A x"
apply (simp add: card_ge_applic_def)
apply (rule card_mono) apply (simp add: card_ge_applic_set_def)
apply (clarsimp simp add: card_ge_applic_set_def inst_of_Inst_fact_def)
apply (simp add: numrestrc_ge_applicable.simps)
apply (clarsimp simp add: rename_in_abox_inversion)
apply (clarsimp simp add: rename_in_abox_inversion rename_in_form_inversion_FactFm 
  rename_in_fact_inversion_Inst split:if_split_asm)
apply (simp add: subst_free_abox_def)
apply (rename_tac n r c cx)
apply (subgoal_tac "subst_free_form (FactFm (Inst x cx))") prefer 2 apply fast
apply (simp add:  subst_free_concept_rename_in_concept)
apply (subgoal_tac "\<not> numrestrc_ge_blocked
           (rename_in_abox A [ISubst y2 y1])
           (rename_in_var x [ISubst y2 y1]) n r
           (rename_in_concept c [ISubst y2 y1])")
(* apply (rule conjI) *)
(* subgoal not numrestrc_ge_not_blocked *)
apply (erule numrestrc_ge_not_blocked, assumption)
apply (rule refl)+
(* subgoal neq_complete 
defer*)
apply simp
apply (subgoal_tac "subst_free_form (FactFm (Inst y2 ([\<ge>] n r c)))") prefer 2 apply (clarsimp split: if_split_asm)
apply (clarsimp split: if_split_asm)
apply (simp add:  subst_free_concept_rename_in_concept)+
done

(* TODO: can be removed
lemma card_ge_applic_rename_in_abox_other:
  "finite A \<Longrightarrow> x \<noteq> y1 \<Longrightarrow> x \<noteq> y2 \<Longrightarrow> subst_free_abox A \<Longrightarrow>
    \<not> contains_clash (rename_in_abox A [ISubst y2 y1]) \<Longrightarrow>
   card_ge_applic (rename_in_abox A [ISubst y2 y1]) x \<le> card_ge_applic A x"
by (simp add: card_ge_applic_card_ge_applic2 card_ge_applic2_rename_in_abox_other)
*)


(* ------------------------------------------------ *)
(* Properties of tableau potential for set decompositions *)
(* ------------------------------------------------ *)

lemma neq_unrelated_add_subconcepts:
  "ab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> ab \<Longrightarrow>
  fv_abox ab' = fv_abox ab \<Longrightarrow>
   neq_unrelated ab' y = neq_unrelated ab y"
by (auto simp add: neq_unrelated_def)


lemma potential_decreases_add_subconcepts_this:
   "FactFm (Inst x c) \<in> abox tab \<Longrightarrow>
   fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow> 
   finite C \<Longrightarrow>
    C \<noteq> {} \<Longrightarrow>
    abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
    \<exists> c \<in> C. (FactFm (Inst x c)) \<notin> abox tab  \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>
    varbounds tab' = varbounds tab \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow> 
    deco_respecting_bounds tab' \<Longrightarrow>
     (node_potential tab' x, node_potential tab x)  \<in> potential_ord"
apply (frule FactFm_Inst_node_concepts)
apply (simp add: node_potential_def potential_ord_def bool_ord_def node_active_same_add_subconcepts)
apply (simp add: bounded_measure_ord_def)

apply (simp add: deco_respecting_bounds_def fv_abox_image_FactFm)
apply (subgoal_tac "fv_abox (abox tab') = fv_abox (abox tab)")
   prefer 2 apply (simp add: fv_abox_def)
apply (simp add: neq_unrelated_add_subconcepts)

apply (subgoal_tac "node_concepts tab x \<subset> node_concepts tab' x")
   prefer 2 apply (rule node_concepts_subset_add_subconcepts) apply assumption+ 
apply fast
done

(* slightly more general than the above *)
lemma potential_decreases_add_subconcepts_this2:
   "c \<in> node_concepts tab x \<Longrightarrow>
   fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow> 
    finite C \<Longrightarrow>
    C \<noteq> {} \<Longrightarrow>
    abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
    \<exists> c \<in> C. (FactFm (Inst x c)) \<notin> abox tab  \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>

    varbounds tab' = varbounds tab \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow> 
    deco_respecting_bounds tab' \<Longrightarrow>
     (node_potential tab' x, node_potential tab x)  \<in> potential_ord"
apply (frule node_active_same [where x=x]) 
apply (simp add: node_potential_def potential_ord_def bool_ord_def node_active_same_add_subconcepts)
apply (simp add: bounded_measure_ord_def)
apply (simp add: neq_unrelated_add_subconcepts)

apply (rule disjI1)
apply (intro conjI)
apply (simp add: deco_respecting_bounds_def fv_abox_image_FactFm)
apply (subgoal_tac "x \<in> fv_abox (abox tab)") prefer 2 apply blast
apply simp
apply (simp add: node_concepts_change_add_subconcepts_this)
apply (fastforce simp add: FactFm_Inst_node_concepts_eq)
done

(*
lemma potential_decreases_add_subconcepts_choose:
   "FactFm (Inst x ([<] n r c)) \<in> abox tab \<Longrightarrow>
    FactFm (AtomR True r x y) \<in> abox tab \<Longrightarrow>
    finite C \<Longrightarrow>
    C \<noteq> {} \<Longrightarrow>
    abox tab' = (\<lambda>c. FactFm (Inst y c)) ` C \<union> abox tab \<Longrightarrow>
    \<exists> c \<in> C. (FactFm (Inst y c)) \<notin> abox tab  \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>
    fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow>
    varbounds tab' = varbounds tab \<Longrightarrow>
    successor_varbounds_closed tab \<Longrightarrow>
    finite (varbounds tab y) \<Longrightarrow> 
    deco_respecting_bounds tab \<Longrightarrow>
     (node_potential tab' y, node_potential tab y)  \<in> potential_ord"
apply (frule node_active_same [where x=y]) 
apply (simp add: node_potential_def potential_ord_def bool_ord_def node_active_same_add_subconcepts)
apply (simp add: bounded_measure_ord_def)
apply (simp add: neq_unrelated_add_subconcepts)

apply (rule disjI1)

apply (simp add: node_concepts_change_add_subconcepts_this)
apply (intro conjI)


(* subgoal C \<subseteq> varbounds tab y *)
apply (subgoal_tac "sub_concepts_pn c \<subseteq> varbounds tab y")
   prefer 2 apply (simp add: successor_varbounds_closed_def)
apply fast

(* subgoal  node_concepts tab y \<subseteq> varbounds tab y*)
apply (subgoal_tac "y \<in> fv_abox (abox tab)") 
   prefer 2 apply (drule_tac fv_form_fv_abox [where f="FactFm (AtomR True r x y)"]) apply simp
apply (simp add: deco_respecting_bounds_def)

(* subgoal  node_concepts tab y \<subset> C \<union> node_concepts tab y *)
apply (fastforce simp add: FactFm_Inst_node_concepts_eq)
done
*)

lemma potential_decreases_add_subconcepts_choose_for_vb_aux1:
   "FactFm (Inst x ([<] n r c)) \<in> abox tab \<Longrightarrow>
    FactFm (AtomR True r x y) \<in> abox tab \<Longrightarrow>
    successor_varbounds_closed tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    sub_concepts_pn c \<subseteq> varbounds tab y"
apply (simp add: successor_varbounds_closed_def)

apply (subgoal_tac "([<] n r c) \<in> varbounds tab x") 
      prefer 2 
      apply (fastforce dest: fv_form_fv_abox 
        simp add: deco_respecting_bounds_def node_concepts_def in_node_concepts_abox [THEN sym])
      
   apply (subgoal_tac "c \<in> varbounds tab y") prefer 2 apply fast
   apply (simp add: bounds_subset_closed_pn_def)
done


lemma potential_decreases_add_subconcepts_choose_for_vb:
   "FactFm (Inst x ([<] n r c)) \<in> abox tab \<Longrightarrow>
    FactFm (AtomR True r x y) \<in> abox tab \<Longrightarrow>
    finite C \<Longrightarrow>
    C \<noteq> {} \<Longrightarrow>
    abox tab' = (\<lambda>c. FactFm (Inst y c)) ` C \<union> abox tab \<Longrightarrow>
    \<exists> c \<in> C. (FactFm (Inst y c)) \<notin> abox tab  \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>
    fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow>
    varbounds tab' = varbounds tab \<Longrightarrow>
    successor_varbounds_closed tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    finite (varbounds tab y) \<Longrightarrow> 
    deco_respecting_bounds tab \<Longrightarrow>
     (node_potential tab' y, node_potential tab y)  \<in> potential_ord"
apply (frule node_active_same [where x=y]) 
apply (simp add: node_potential_def potential_ord_def bool_ord_def node_active_same_add_subconcepts)
apply (simp add: bounded_measure_ord_def)
apply (simp add: neq_unrelated_add_subconcepts)
apply (rule disjI1)
apply (simp add: node_concepts_change_add_subconcepts_this)
apply (intro conjI)

(* subgoal C \<subseteq> varbounds tab y *)
apply (subgoal_tac "sub_concepts_pn c \<subseteq> varbounds tab y")
   prefer 2
   apply (rule potential_decreases_add_subconcepts_choose_for_vb_aux1) apply assumption+
apply fast

(* subgoal  node_concepts tab y \<subseteq> varbounds tab y*)
apply (subgoal_tac "y \<in> fv_abox (abox tab)") 
   prefer 2 apply (drule_tac fv_form_fv_abox [where f="FactFm (AtomR True r x y)"]) apply simp
apply (simp add: deco_respecting_bounds_def)

(* subgoal  node_concepts tab y \<subset> C \<union> node_concepts tab y *)
apply (fastforce simp add: FactFm_Inst_node_concepts_eq)

done

lemma potential_weakly_decreases_add_subconcepts_other:
   "abox tab' = (\<lambda>c. FactFm (Inst x c)) ` C \<union> abox tab \<Longrightarrow>
    fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    varbounds tab' = varbounds tab \<Longrightarrow>
    y \<noteq> x \<Longrightarrow>
  (node_potential tab' y, node_potential tab y)  \<in> potential_ord\<^sup>= "
apply (frule node_active_same [where x=y]) 
apply (simp add: node_potential_def potential_ord_def bool_ord_def node_active_same_add_subconcepts)
apply (simp add: node_concepts_same_add_subconcepts_other)
apply (simp add: neq_unrelated_add_subconcepts)
apply (simp add: nat_ord_or_eq card_ge_applic_antimono_image)
done


(* TODO: move elsewhere *)
lemma mult_empty_less: "trans r \<Longrightarrow> M \<noteq> {#} \<Longrightarrow> ({#}, M) \<in> mult r"
apply (subgoal_tac "({#} + {#}, {#} + M) \<in> mult r") apply simp
apply (fastforce intro: one_step_implies_mult)
done

lemma mult_not_less_empty_aux: "(M, N) \<in> mult r \<Longrightarrow> N \<noteq> {#}"
apply (unfold mult_def)
apply (induct rule: trancl_induct)
apply clarsimp+
done

lemma mult_not_less_empty [simp]: "(M, {#}) \<notin> mult r"
by (fast dest: mult_not_less_empty_aux)

lemma tableau_potential_split_vars_ws_decreasing2:
 "V = fv_tableau tab - {x} \<Longrightarrow>
  x \<in> fv_tableau tab \<Longrightarrow>
  fv_tableau tab' = V \<union> R \<Longrightarrow>
  finite (fv_tableau tab) \<Longrightarrow>
  finite R \<Longrightarrow> 
  V \<inter> R = {} \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
  strongly_decreasing 
     (tableau_potential_for_set tab' R) (tableau_potential_for_set tab {x}) potential_ord \<Longrightarrow>
 (tableau_potential_for_set tab' V, tableau_potential_for_set tab V) \<in> multstar potential_ord \<Longrightarrow>
 (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"

apply (subgoal_tac "trans potential_ord") prefer 2 apply simp
apply (drule one_step_implies_mult_ws_decreasing2) apply assumption+


apply (subgoal_tac "tableau_potential_for_set tab' (fv_tableau tab') =
                    tableau_potential_for_set tab' V + tableau_potential_for_set tab' R")

apply (subgoal_tac "tableau_potential_for_set tab (fv_tableau tab) =
                    tableau_potential_for_set tab V + tableau_potential_for_set tab {x}")

apply (simp only: tableau_potential_ord_def tableau_potential_tableau_potential_for_set)
apply simp
apply (subgoal_tac "tableau_potential_for_set tab (fv_tableau tab - {x}) +
                    tableau_potential_for_set tab {x} \<noteq> {#}")
apply (simp add: mult_empty_less)
apply (simp add:  tableau_potential_for_set_empty_equiv)
apply (rule tableau_potential_for_set_union, fast+)+ 
done


(* TODO: tableau_potential_split_vars_ws_decreasing2 is an instance of 
         tableau_potential_split_vars_ws_decreasing3 *)
(* M: modified variables; U: unchanged variables; N: new variables *)
lemma tableau_potential_split_vars_ws_decreasing3:
 "U = fv_tableau tab - M \<Longrightarrow>
  M \<subseteq> fv_tableau tab \<Longrightarrow>
  fv_tableau tab' = U \<union> N \<Longrightarrow>
  finite (fv_tableau tab) \<Longrightarrow>
  finite M \<Longrightarrow> 
  finite N \<Longrightarrow> 
  U \<inter> N = {} \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
  
   strongly_decreasing 
     (tableau_potential_for_set tab' N) (tableau_potential_for_set tab M) potential_ord \<Longrightarrow>

   (tableau_potential_for_set tab' U, tableau_potential_for_set tab U) \<in> multstar potential_ord \<Longrightarrow>

     (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"

apply (subgoal_tac "trans potential_ord") prefer 2 apply simp
apply (drule one_step_implies_mult_ws_decreasing2) apply assumption+

apply (subgoal_tac "tableau_potential_for_set tab' (fv_tableau tab') = 
                    tableau_potential_for_set tab'  U + tableau_potential_for_set tab' N")

apply (subgoal_tac "tableau_potential_for_set tab (fv_tableau tab) = 
                    tableau_potential_for_set tab U + tableau_potential_for_set tab M")

apply (simp only: tableau_potential_ord_def tableau_potential_tableau_potential_for_set)
apply simp
apply (subgoal_tac "tableau_potential_for_set tab (fv_tableau tab - M) +
                    tableau_potential_for_set tab M \<noteq> {#}")
apply (simp add: mult_empty_less)
apply (clarsimp simp add:  tableau_potential_for_set_empty_equiv)
apply (rule tableau_potential_for_set_union, fast+)+
done


lemma tableau_potential_change_one: "x \<in> fv_tableau tab \<Longrightarrow>
   fv_tableau tab' = fv_tableau tab \<Longrightarrow> 
   finite (fv_tableau tab) \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
   (node_potential tab' x, node_potential tab x) \<in> potential_ord \<Longrightarrow>
   (tableau_potential_for_set tab' (fv_tableau tab - {x}), 
    tableau_potential_for_set tab (fv_tableau tab - {x})) \<in> multstar potential_ord
\<Longrightarrow> (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (rule tableau_potential_split_vars_ws_decreasing2 [where x=x and R = "{x}"]) 
apply (rule refl)
apply simp_all
apply fast
apply (simp add: strongly_decreasing_def)
apply (simp add: tableau_potential_for_set_def pair_node_potential_def pair_fun_def)+
done


lemma tableau_potential_decreases_numrestrc_ge: 
  "x \<in> fv_tableau tab \<Longrightarrow>
   Y \<inter> (fv_tableau tab) = {} \<Longrightarrow>
   finite Y \<Longrightarrow>
   finite (fv_tableau tab) \<Longrightarrow>
   fv_tableau tab' = fv_tableau tab \<union> Y \<Longrightarrow> 
  \<not> contains_clash (abox tab) \<Longrightarrow>
   (node_potential tab' x, node_potential tab x) \<in> potential_ord \<Longrightarrow>
   \<forall> y \<in> Y. (node_potential tab' y, node_potential tab x) \<in> potential_ord \<Longrightarrow>
   (tableau_potential_for_set tab' (fv_tableau tab - {x}), 
      tableau_potential_for_set tab (fv_tableau tab - {x})) \<in> multstar potential_ord
\<Longrightarrow> (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"

apply (rule tableau_potential_split_vars_ws_decreasing2 [where x=x and R = "insert x Y"]) 
apply (rule refl)
apply simp_all
apply fast
apply fast
apply (subgoal_tac "(pair_node_potential tab' x) \<notin> (pair_node_potential tab' ` Y)")
   prefer 2 apply (insert inj_pair_node_potential [of tab']) apply (fast dest: injD)

apply (simp add: tableau_potential_for_set_def strongly_decreasing_def set_image_multiset_insert 
  pair_node_potential_def set_mset_set_image_multiset) 
done

(* TODO: redundance between finite (abox tab) and  finite (fv_tableau tab) *)
lemma tableau_potential_decreases_add_subconcepts_this:
   "FactFm (Inst x c) \<in> abox tab \<Longrightarrow>
    finite C \<Longrightarrow>
    C \<noteq> {} \<Longrightarrow>
    abox tab' = ((\<lambda> c. FactFm (Inst x c)) ` C) \<union> abox tab \<Longrightarrow>
    \<exists> c \<in> C. (FactFm (Inst x c)) \<notin> abox tab  \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>
    varbounds tab' = varbounds tab \<Longrightarrow>
    fv_abox (abox tab') = fv_abox (abox tab) \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    finite (fv_tableau tab) \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow>
    deco_respecting_bounds tab' \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
 (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (rule tableau_potential_change_one [where x=x])
apply (simp add: var_in_fv_tableau)
apply assumption+
apply (rule potential_decreases_add_subconcepts_this) apply assumption+
apply (rule tableau_potential_for_set_multstar)
apply simp
apply (rule ballI)
apply (rule potential_weakly_decreases_add_subconcepts_other)
apply assumption+
apply clarsimp
done


lemma tableau_potential_decreases_add_subconcepts_choose:
   "FactFm (Inst x ([<] n r c)) \<in> abox tab \<Longrightarrow>
    FactFm (AtomR True r x y) \<in> abox tab \<Longrightarrow>
    finite C \<Longrightarrow>
    C \<noteq> {} \<Longrightarrow>
    abox tab' = ((\<lambda> c. FactFm (Inst y c)) ` C) \<union> abox tab \<Longrightarrow>
    \<exists> c \<in> C. (FactFm (Inst y c)) \<notin> abox tab  \<Longrightarrow>
    C \<subseteq> sub_concepts_pn c \<Longrightarrow>
    fv_tableau tab' = fv_tableau tab \<Longrightarrow>
    varbounds tab' = varbounds tab \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    finite (varbounds tab y) \<Longrightarrow> 
    deco_respecting_bounds tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    successor_varbounds_closed tab \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
 (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (rule tableau_potential_change_one [where x=y])
apply (simp add: var_in_fv_tableau)
apply assumption
apply simp
apply assumption
apply (rule potential_decreases_add_subconcepts_choose_for_vb) apply assumption+
apply (rule tableau_potential_for_set_multstar)
apply simp
apply (rule ballI)
apply (rule potential_weakly_decreases_add_subconcepts_other)
apply assumption+
apply clarsimp
done


(* TODO: maybe unify the finite ... hypotheses *)
lemma tableau_potential_decreases_using_potential_ord_for_conjc_tableau_rule: 
   "conjc_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>   
    finite_varbounds tab \<Longrightarrow>
    deco_respecting_bounds tab' \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: conjc_tableau_rule_def ex_rule_closure_def)
apply (rename_tac f)
apply (clarsimp simp add: conjc_tableau_rule_indiv_def lift_to_tableau_rule_def)

apply (clarsimp simp add: conjc_rule_indiv.simps)
apply (rename_tac x c1 c2)
apply (subgoal_tac "finite {c2, c1}") prefer 2 apply simp
apply (rule tableau_potential_decreases_add_subconcepts_this)
apply assumption+
apply simp_all
apply clarsimp
apply (fastforce simp add: Let_def)
apply (fastforce simp add: finite_varbounds_def dest: fv_form_fv_abox)+
done

lemma tableau_potential_decreases_using_potential_ord_for_disjc_tableau_rule: 
   "disjc_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    finite_varbounds tab \<Longrightarrow>
    deco_respecting_bounds tab' \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: disjc_tableau_rule_def ex_rule_closure_def)
apply (rename_tac f)
apply (clarsimp simp add: disjc_tableau_rule_indiv_def lift_to_tableau_rule_def)

apply (clarsimp simp add: disjc_rule_indiv.simps)
apply (elim disjE)

apply clarsimp
apply (rename_tac x c1 c2)
apply (subgoal_tac "finite {c1}") prefer 2 apply simp
apply (rule tableau_potential_decreases_add_subconcepts_this)
apply assumption+
apply simp_all
apply (fastforce simp add: Let_def)
apply (fastforce dest: fv_form_fv_abox)
apply (fastforce simp add: finite_varbounds_def dest: fv_form_fv_abox)+

apply clarsimp
apply (rename_tac x c1 c2)
apply (subgoal_tac "finite {c2}") prefer 2 apply simp
apply (rule tableau_potential_decreases_add_subconcepts_this)
apply assumption+
apply simp_all
apply (fastforce simp add: Let_def)
apply (fastforce simp add: finite_varbounds_def dest: fv_form_fv_abox)+
done


lemma tableau_potential_decreases_using_potential_ord_for_choose_tableau_rule: 
   "choose_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    finite_varbounds tab \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    successor_varbounds_closed tab \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: choose_tableau_rule_def ex_rule_closure_def)
apply (rename_tac f)
apply (clarsimp simp add: choose_tableau_rule_indiv_def lift_to_tableau_rule_def)

apply (clarsimp simp add: choose_rule_indiv.simps)
apply (elim disjE)
apply clarsimp

apply (rename_tac x n r c y)
apply (subgoal_tac "finite {c}") prefer 2 apply simp
apply (rule tableau_potential_decreases_add_subconcepts_choose)
apply assumption+
apply simp_all
apply (fastforce dest: fv_form_fv_abox)
apply (drule fv_form_fv_abox)+ apply clarsimp
apply (fastforce simp add: finite_varbounds_def dest: fv_form_fv_abox)

apply (rename_tac x n r c y)
apply (subgoal_tac "finite {neg_norm_concept False c}") prefer 2 apply simp
apply (rule tableau_potential_decreases_add_subconcepts_choose)
apply assumption+
apply simp_all
apply (fastforce dest: fv_form_fv_abox)
apply (fastforce simp add: finite_varbounds_def dest: fv_form_fv_abox)
done


lemma node_concepts_abox_AtomR: 
   "node_concepts_abox {FactFm (AtomR True r x y) |y. y \<in> Y} z = {}"
by (auto simp add: node_concepts_abox_def)

lemma node_concepts_abox_Inst_diff:
"node_concepts_abox {FactFm (Inst y c) |y. y \<in> Y} z = (if z \<in> Y then {c} else {})"
by (auto simp add: node_concepts_abox_def image_def)

lemma node_concepts_abox_Eq: 
   "node_concepts_abox {FactFm (Eq False y1 y2) |y1 y2. y1 \<in> Y \<and> y2 \<in> Y \<and> y1 < y2} z = {}"
by (auto simp add: node_concepts_abox_def)

lemma node_concepts_abox_numrestrc_ge_rule_facts [simp]:
    "node_concepts_abox (numrestrc_ge_rule_facts c r x Y) z = (if z \<in> Y then {c} else {})"
by (simp add: numrestrc_ge_rule_facts_def 
  node_concepts_abox_AtomR node_concepts_abox_Inst_diff node_concepts_abox_Eq)

lemma eq_fv_abox_bounded: 
   "z \<le> x \<Longrightarrow> (z \<in> fv_abox ab) = (z \<in> fv_abox_bounded ab x)"
by (simp add: fv_abox_bounded_def)


lemma fv_abox_bounded_self [simp]: 
   "(x::'a::linorder) \<in> fv_abox ab \<Longrightarrow> x \<in> fv_abox_bounded ab x"
by (simp add: fv_abox_bounded_def)


lemma fv_abox_bounded_numrestrc_ge_rule_facts:
 "\<forall> y\<in> Y. z < y \<Longrightarrow>
   (x:: 'a::linorder) \<in> fv_abox ab \<Longrightarrow> 
   fv_concept c \<inter> Y = {} \<Longrightarrow>
   fv_concept c \<subseteq> fv_abox ab \<Longrightarrow>
   fv_abox_bounded (numrestrc_ge_rule_facts c r x Y) z = 
      (if Y = {} then {} else  ({x'. x' \<le> z} \<inter> insert x (fv_concept c)))"
apply (clarsimp simp add: fv_abox_bounded_def numrestrc_ge_rule_facts_def)
apply (fastforce simp add: fv_abox_def)+
done

(* TODO: remove redundancies in premises *)
lemma neq_unrelated_numrestrc_ge_this:
 "ab' =  numrestrc_ge_rule_facts c r x Y \<union> ab \<Longrightarrow>
   \<forall> z\<in> Y. x < z \<Longrightarrow>
   x \<in> fv_abox ab \<Longrightarrow> 
   fv_concept c \<inter> Y = {} \<Longrightarrow>
   fv_concept c \<subseteq> fv_abox ab \<Longrightarrow>
   neq_unrelated ab' x  = neq_unrelated ab x"
apply (simp add: neq_unrelated_def)
apply (simp add: eq_fv_abox_bounded cong add: conj_cong)

apply (subgoal_tac "fv_abox_bounded (numrestrc_ge_rule_facts c r x Y) x = 
      (if Y = {} then {} else  ({x'. x' \<le> x} \<inter> insert x (fv_concept c)))")
   prefer 2 apply (rule fv_abox_bounded_numrestrc_ge_rule_facts, assumption+)
apply simp
apply (simp cong add: conj_cong disj_cong)

apply (subgoal_tac "\<forall> z1 z2. z1 \<le> x \<longrightarrow> z2 \<le> x \<longrightarrow> 
     FactFm (Eq False z1 z2) \<notin> numrestrc_ge_rule_facts c r x Y")
   prefer 2 apply (fastforce simp add: FactFm_Eq_numrestrc_ge_rule_facts)
apply (simp cong add: conj_cong disj_cong)
apply (fastforce simp add: fv_abox_bounded_def)
done

lemma neq_unrelated_numrestrc_ge_other:
 "ab' =  numrestrc_ge_rule_facts c r x Y \<union> ab \<Longrightarrow>
   \<forall> y\<in> Y. z < y \<Longrightarrow>
   z \<notin> Y \<Longrightarrow> 
   x \<in> fv_abox ab \<Longrightarrow> 
   fv_concept c \<inter> Y = {} \<Longrightarrow>
   fv_concept c \<subseteq> fv_abox ab \<Longrightarrow>
   neq_unrelated ab' z  = neq_unrelated ab z"
apply (simp add: neq_unrelated_def)
apply (simp add: eq_fv_abox_bounded cong add: conj_cong)
apply (subgoal_tac "fv_abox_bounded (numrestrc_ge_rule_facts c r x Y) z = 
      (if Y = {} then {} else  ({x'. x' \<le> z} \<inter> insert x (fv_concept c)))")
   prefer 2 apply (rule fv_abox_bounded_numrestrc_ge_rule_facts, assumption+)

apply (subgoal_tac "\<forall> z1 z2. z1 \<le> z \<longrightarrow> z2 \<le> z \<longrightarrow> 
     FactFm (Eq False z1 z2) \<notin> numrestrc_ge_rule_facts c r x Y")
   prefer 2 apply (fastforce simp add: FactFm_Eq_numrestrc_ge_rule_facts)
apply (simp cong add: conj_cong disj_cong)
apply (fastforce simp add: fv_abox_bounded_def)
done

(* TODO: choose better name *)
lemma numrestrc_ge_successor_varbounds_old_same: 
  "z \<notin> Y \<Longrightarrow> 
  numrestrc_ge_successor_varbounds_old Y r tab x z = varbounds tab z"
by (simp add: numrestrc_ge_successor_varbounds_old_def)

lemma numrestrc_ge_successor_varbounds_new_same: 
  "z \<notin> Y \<Longrightarrow> 
  numrestrc_ge_successor_varbounds_new Y r tab x z = varbounds tab z"
by (simp add: numrestrc_ge_successor_varbounds_new_def)

lemma potential_decreases_numrestrc_ge_this:
 "tab' =  \<lparr>abox = numrestrc_ge_rule_facts c r x Y \<union> abox tab,
          varbounds = numrestrc_ge_successor_varbounds_old Y r tab x \<rparr> \<Longrightarrow>
  x \<notin> Y \<Longrightarrow>
  \<forall> z\<in> Y. x < z \<Longrightarrow>
   fv_concept c \<inter> Y = {} \<Longrightarrow>
   fv_concept c \<subseteq> fv_abox (abox tab) \<Longrightarrow>
  finite (Y :: ('ni :: linorder) set) \<Longrightarrow>
  finite (abox tab) \<Longrightarrow>
  numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] (card Y) r c))) (abox tab) \<Longrightarrow>
  neq_complete x (abox tab) \<Longrightarrow> 
      (node_potential tab' x, node_potential tab x) \<in> potential_ord" 

apply (subgoal_tac "x \<in> fv_abox (abox tab)")
apply (subgoal_tac "x \<in> fv_abox (abox tab')")
apply (subgoal_tac "node_active tab' x = node_active tab x") 
   prefer 2 apply (simp add: node_active_def) 
apply (subgoal_tac "varbounds tab' x = varbounds tab x") 
   prefer 2 apply (simp add: numrestrc_ge_successor_varbounds_old_same)

apply (subgoal_tac "node_concepts tab' x = node_concepts tab x") 
   prefer 2 apply (simp add: node_concepts_def)
apply (subgoal_tac "neq_unrelated (abox tab') x = neq_unrelated (abox tab) x") 
   prefer 2 apply (rule neq_unrelated_numrestrc_ge_this) apply simp apply assumption+
apply (simp add: node_potential_def potential_ord_def bool_ord_def nat_ord_def)
apply (simp add: numrestrc_ge_applicable.simps)

apply (rule card_ge_applic_numrestrc_ge_rule_facts_for_applicable)
apply simp_all
apply (simp add: numrestrc_ge_applicable.simps)
apply (clarsimp simp add: numrestrc_ge_applicable.simps numrestrc_ge_blocked_def)
apply (simp add: fv_abox_def)
apply (erule rev_bexI) apply simp
done

lemma is_NumRestrC_concept_unfold: 
   "is_NumRestrC_concept nros rs c = (\<exists> nro \<in> nros. \<exists> r \<in> rs. \<exists> n c'. c = (NumRestrC nro n r c'))"
by (auto simp add: is_NumRestrC_concept_def split : "concept.split_asm")

lemma concept_of_NumRestrC_concept_NumRestrC [simp]: 
   "concept_of_NumRestrC_concept (NumRestrC nro n r c) = c"
by (simp add: concept_of_NumRestrC_concept_def)


lemma successor_varbounds_inclusion: 
    "bounds_subset_closed_pn (varbounds tab) \<Longrightarrow> 
     successor_varbounds r (varbounds tab x) \<subseteq> varbounds tab x"
apply (clarsimp simp add: successor_varbounds_def)
apply (clarsimp simp add: is_NumRestrC_concept_unfold bounds_subset_closed_pn_def)
apply (rename_tac s nro' n' c')
apply (subgoal_tac "sub_concepts_pn (NumRestrC nro' n' r c') \<subseteq> varbounds tab x") prefer 2 apply fast
apply (subgoal_tac "c' \<in>  sub_concepts_pn (NumRestrC nro' n' r c')") prefer 2 apply (simp add: Let_def)
apply (fast dest: sub_concepts_pn_closed)
done



inductive_set strict_NumRestrC_subc :: "(('nr, 'nc, 'ni) concept * ('nr, 'nc, 'ni) concept) set" where
"(c, (NumRestrC nro n r c)) \<in> strict_NumRestrC_subc" 

inductive_set strict_NumRestrC_subc_hg :: "(('nr, 'nc, 'ni) concept * ('nr, 'nc, 'ni) concept) set" where
"is_NumRestrC_concept UNIV {r} c' \<Longrightarrow>
 is_NumRestrC_concept UNIV {r} c \<Longrightarrow>
 height_concept c' < height_concept c \<Longrightarrow>
(c', c) \<in> strict_NumRestrC_subc_hg" 

lemma wf_strict_NumRestrC_subc: "wf strict_NumRestrC_subc"
apply (subgoal_tac "wf nat_ord") prefer 2 apply simp
apply (drule wf_inv_image [where f= height_concept])
apply (erule wf_subset)
apply (clarsimp simp add:  inv_image_def strict_NumRestrC_subc.simps nat_ord_def)
done

lemma wf_strict_NumRestrC_subc_hg: "wf strict_NumRestrC_subc_hg"
apply (subgoal_tac "wf nat_ord") prefer 2 apply simp
apply (drule wf_inv_image [where f= height_concept])
apply (erule wf_subset)
apply (clarsimp simp add:  inv_image_def strict_NumRestrC_subc_hg.simps nat_ord_def)
done

lemma acyc_strict_NumRestrC_subc_hg: "acyclic strict_NumRestrC_subc_hg" 
by (rule wf_acyclic) (rule wf_strict_NumRestrC_subc_hg)

lemma acyc_inters: "acyclic r \<Longrightarrow> acyclic (r \<inter> A)"
apply (clarsimp simp add: acyclic_def)
apply (drule trancl_mono [where s=r]) 
apply fast+
done

lemma acyc_restr: "finite A \<Longrightarrow> acyclic r \<Longrightarrow> wf((r \<inter> A)\<inverse>)"
apply (rule finite_acyclic_wf_converse)
apply simp
apply (simp add: acyc_inters)
done

lemma wf_strict_NumRestrC_subc_hg_for_finite:
  "finite A \<Longrightarrow> wf((strict_NumRestrC_subc_hg \<inter> A)\<inverse>)"
by (erule acyc_restr) (rule acyc_strict_NumRestrC_subc_hg) 

lemma strict_NumRestrC_subc_hg_max:
    "\<exists> c'. c' \<in> NGE \<Longrightarrow> 
     finite NGE \<Longrightarrow>
     \<exists> m \<in> NGE. \<forall>y. (m, y) \<in> strict_NumRestrC_subc_hg \<longrightarrow> y \<notin> NGE"
apply (subgoal_tac "finite (NGE \<times> NGE)")
apply (drule wf_strict_NumRestrC_subc_hg_for_finite) prefer 2 apply simp
apply (simp add: wf_eq_minimal)
apply (drule_tac x=NGE in spec)
apply blast
done

lemma sub_concepts_pn_height_concept [rule_format]:
  "\<forall> sc \<in> (sub_concepts_pn c). height_concept sc \<le> height_concept c"
by (induct c) (auto simp add: Let_def)


lemma successor_varbounds_strict_inclusion_aux: 
    "NGE = {c \<in> varbounds tab x. is_NumRestrC_concept UNIV {r} c} \<Longrightarrow> 
     \<exists> c'. c' \<in> NGE \<Longrightarrow> 
     finite (varbounds tab x) \<Longrightarrow>
    \<not> (varbounds tab x  \<subseteq> successor_varbounds r (varbounds tab x))"
apply (subgoal_tac "(\<exists> m \<in> NGE. \<forall>y. (m, y) \<in> strict_NumRestrC_subc_hg \<longrightarrow> y \<notin> NGE)")
   prefer 2 apply (erule strict_NumRestrC_subc_hg_max) apply simp
apply (elim bexE)
apply (rename_tac maxc)

apply (clarsimp simp add: subset_eq)
apply (rule_tac x=maxc in rev_bexI) apply assumption
apply (clarsimp simp add: successor_varbounds_def)

apply (rename_tac maxc c' supmaxc)
apply (subgoal_tac "(maxc, supmaxc) \<in> strict_NumRestrC_subc_hg", fast)

apply (drule sub_concepts_pn_height_concept)
apply (clarsimp simp add: strict_NumRestrC_subc_hg.simps is_NumRestrC_concept_unfold)
done

(* TODO: move elsewhere *)
lemma deco_respecting_boundsD: 
  "deco_respecting_bounds tab \<Longrightarrow>
   FactFm (Inst x c) \<in> abox tab \<Longrightarrow>
   c \<in> varbounds tab x"
apply (frule fv_form_fv_abox)
apply (clarsimp simp add: FactFm_Inst_node_concepts_eq)
apply (fastforce simp add: deco_respecting_bounds_def)
done

 
lemma successor_varbounds_strict_inclusion: 
   "numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] (card Y) r c))) (abox tab) \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    successor_varbounds r (varbounds tab x) \<subset> varbounds tab x"
apply (simp add: subset_not_subset_eq)
apply (rule conjI)
apply (erule successor_varbounds_inclusion)

apply (rule successor_varbounds_strict_inclusion_aux)
apply (rule refl)
prefer 2 apply assumption
apply (clarsimp simp add: numrestrc_ge_applicable.simps)
apply (drule deco_respecting_boundsD) apply assumption
apply (fastforce simp add: is_NumRestrC_concept_def)
done

lemma fv_abox_numrestrc_ge_rule_facts_cond [simp]:
"fv_abox (numrestrc_ge_rule_facts c r x Y) = 
   (if Y = {} then {} else (insert x Y \<union>  fv_concept c))"
by (auto simp add: numrestrc_ge_rule_facts_def fv_abox_def)


lemma numrestrc_ge_successor_varbounds_old_varbounds_strict_inclusion:
   "y \<in> Y \<Longrightarrow>
    numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] (card Y) r c))) (abox tab) \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    numrestrc_ge_successor_varbounds_old Y r tab x y \<subset> varbounds tab x"
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
apply (rule successor_varbounds_strict_inclusion) apply assumption+
done

(*
y \<in> Y \<Longrightarrow>
    numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] card Y r c)))
     (abox tab) \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    successor_varbounds r (varbounds tab x) \<union> varbounds_forw tab x
    \<subset> varbounds tab x
*)
(* TODO: cannot work *)
lemma numrestrc_ge_successor_varbounds_new_varbounds_strict_inclusion:
   "y \<in> Y \<Longrightarrow>
    numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] (card Y) r c))) (abox tab) \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    finite (varbounds tab x) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    numrestrc_ge_successor_varbounds_new Y r tab x y \<subset> varbounds tab x"
apply (simp add: numrestrc_ge_successor_varbounds_new_def)
oops

(* TODO: clean up preconditions *)
lemma potential_decreases_numrestrc_ge_other:
 "numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] (card Y) r c))) (abox tab) \<Longrightarrow>
  y \<in> Y \<Longrightarrow> 
  finite (varbounds tab x) \<Longrightarrow>
  bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
  deco_respecting_bounds tab \<Longrightarrow>
  tab' =  \<lparr>abox = numrestrc_ge_rule_facts c r x Y \<union> abox tab,
          varbounds = numrestrc_ge_successor_varbounds_old Y r tab x \<rparr> \<Longrightarrow>
      (node_potential tab' y, node_potential tab x) \<in> potential_ord"
apply (subgoal_tac "x \<in> fv_abox (abox tab)") 
   prefer 2 apply (fastforce simp add: numrestrc_ge_applicable.simps dest: fv_form_fv_abox)
apply (subgoal_tac "y \<in> fv_abox (numrestrc_ge_rule_facts c r x Y)")
   prefer 2 apply fastforce
apply (simp add: node_potential_def potential_ord_def bool_ord_def nat_ord_def)
apply (simp add: node_active_def split : if_split_asm)
apply (rule disjI1)
apply (rule psubset_card_mono) apply assumption 
apply (rule numrestrc_ge_successor_varbounds_old_varbounds_strict_inclusion) apply assumption+
done

definition tableau_invariant :: "('nr, 'nc, 'ni :: linorder) tableau \<Rightarrow> bool" where
  "tableau_invariant = (\<lambda> tab.  
      (
       finite (abox tab) \<and>
       finite_varbounds tab \<and>
       subst_free_abox (abox tab) \<and>
       bounds_subset_closed_pn (varbounds tab) \<and>
       bounds_renaming_closed tab \<and>
       deco_respecting_bounds tab \<and>
       successor_varbounds_closed tab
      ))"

definition rule_resp_invariant ::  "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a arule \<Rightarrow> bool" where
  "rule_resp_invariant initcond invar rl = (\<forall> t t'. rl t t' \<longrightarrow> initcond t \<longrightarrow> invar t \<longrightarrow> invar t')"

lemma rule_resp_invariant_conj_invar: "
    (rule_resp_invariant (\<lambda> t. initcond t \<and> iv1 t) iv2 rl \<and> rule_resp_invariant initcond iv1 rl)
   \<Longrightarrow> rule_resp_invariant initcond (\<lambda> t. iv1 t \<and> iv2 t) rl"
by (simp add: rule_resp_invariant_def)

lemma rule_resp_invariant_disj_rule: 
 "rule_resp_invariant initcond invar (alternative_rule_of_set rls) = 
   (\<forall> rl \<in> rls. rule_resp_invariant initcond invar rl)"
by (fastforce simp add: rule_resp_invariant_def alternative_rule_of_set_def)


lemma tableau_potential_decreases_using_potential_ord_for_numrestrc_ge_tableau_rule: 
" numrestrc_ge_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    finite_varbounds tab  \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    successor_varbounds_closed tab \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: numrestrc_ge_tableau_rule_def ex_rule_closure_def)
apply (rename_tac f)
apply (clarsimp 
  simp add: numrestrc_ge_tableau_rule_indiv.simps lift_to_tableau_rule_def
  del: numrestrc_ge_applicable_cases)


apply (rename_tac x r c Y)
apply (subgoal_tac "x \<in> fv_abox (abox tab)")
   prefer 2 apply (fastforce simp add: numrestrc_ge_applicable.simps dest: fv_form_fv_abox)
apply (subgoal_tac "fv_concept c \<subseteq> fv_abox (abox tab)")
   prefer 2 apply (fastforce simp add: numrestrc_ge_applicable.simps dest: fv_form_fv_abox)
apply (subgoal_tac "Y \<inter> (fv_tableau tab) = {}") 
   prefer 2 apply (fastforce simp add: fresh_set_incr_def) 
apply (rule tableau_potential_decreases_numrestrc_ge) 
apply assumption+
apply simp+
      apply (simp add: fv_abox_def) 
  
  apply blast
apply assumption+

apply (rule potential_decreases_numrestrc_ge_this)
apply (rule refl)
apply fast
apply (simp add: fresh_set_incr_def)
apply (fastforce)
apply simp_all

apply (rule ballI)
apply (rule potential_decreases_numrestrc_ge_other) apply assumption+
apply simp_all
apply (simp add: finite_varbounds_def)


(* tableau potential remains the same for all other nodes *)
apply (rule tableau_potential_for_set_multstar)
apply simp
apply (rule ballI)
apply (rename_tac x r c Y z)
apply (subgoal_tac "z \<notin> Y \<and> z\<noteq> x") prefer 2 apply fast
apply (clarsimp simp add: node_potential_def)
apply (subgoal_tac "node_active tab' z = node_active tab z") 
   prefer 2 
   apply (simp add: node_active_def)
   apply (subgoal_tac "fv_concept c \<subseteq> fv_abox (abox tab)") 
       prefer 2 apply (frule fv_form_fv_abox)
   apply blast 
apply simp
apply (subgoal_tac "node_concepts tab' z = node_concepts tab z")
   prefer 2  apply simp apply (simp add: node_concepts_def)
apply (subgoal_tac "neq_unrelated (abox tab') z = neq_unrelated (abox tab) z")
   prefer 2 apply (rule neq_unrelated_numrestrc_ge_other) 
   apply (simp add: fresh_set_incr_def)
   apply (simp add: fresh_set_incr_def)
   apply assumption+
   apply fast
   apply assumption

apply (simp add: potential_ord_def nat_ord_def)
apply (simp add: numrestrc_ge_successor_varbounds_old_same)
apply (subgoal_tac "card_ge_applic (numrestrc_ge_rule_facts c r x Y \<union> abox tab) z 
    \<le> card_ge_applic (abox tab) z")
   prefer 2 apply (rule card_ge_applic_numrestrc_ge_rule_facts_le) apply simp+ defer
apply arith
apply (simp add: fresh_set_incr_def)
done

(* lemmas about join_varbounds *)
lemma join_varbounds_bounds_renaming_closed: 
   "(y1 :: 'a :: linorder) < y2 \<Longrightarrow>
    y1 \<in> fv_tableau tab \<Longrightarrow> 
    y2 \<in> fv_tableau tab \<Longrightarrow> 
    bounds_renaming_closed tab \<Longrightarrow>
    join_varbounds y2 y1 (varbounds tab) x = 
        (if x = y2 then {} else (varbounds tab) x)"
apply (auto simp add: join_varbounds_def bounds_renaming_closed_def)
  done


lemma node_concepts_rename_in_abox_subset:
  "x \<noteq> y2 \<or> y1 = y2 \<Longrightarrow> 
  subst_free_abox ab \<Longrightarrow>
  node_concepts_abox ab x \<subseteq> node_concepts_abox (rename_in_abox ab [ISubst y2 y1]) x"
apply (case_tac "y1 = y2")
apply simp
apply (clarsimp simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  simp del: is_Inst_fact.simps )
apply (intro exI conjI)
apply assumption
apply (simp split : if_split_asm)+
apply (simp add: subst_free_abox_def)
apply (rename_tac c)
apply (subgoal_tac "subst_free_form (FactFm (Inst x c))") prefer 2 apply fast
apply (simp  add: subst_free_concept_rename_in_concept)
done


lemma node_concepts_rename_in_abox_eq_for_incl:
  "subst_free_abox ab \<Longrightarrow>
  node_concepts_abox ab y2 \<subseteq> node_concepts_abox ab y1 \<Longrightarrow>
   node_concepts_abox (rename_in_abox ab [ISubst y2 y1]) y1 =
   node_concepts_abox ab y1"
apply (rule subset_antisym)
prefer 2
apply (rule node_concepts_rename_in_abox_subset) apply fast apply assumption

apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps )

apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst)
apply (clarsimp split : if_split_asm)
apply (rename_tac c)
apply (subgoal_tac "FactFm (Inst y1 c) \<in> ab") prefer 2 apply fastforce
apply (intro exI conjI)
prefer 2 apply (rule refl) apply assumption
apply simp
apply (simp add: subst_free_abox_def)
apply (subgoal_tac "subst_free_form (FactFm (Inst y1 c))") prefer 2 apply fast
apply (simp  add: subst_free_concept_rename_in_concept)

apply (intro exI conjI)
prefer 2 apply (rule refl) apply assumption
apply simp
apply (simp add: subst_free_abox_def)
apply (rename_tac c)
apply (subgoal_tac "subst_free_form (FactFm (Inst y1 c))") prefer 2 apply fast
apply (simp  add: subst_free_concept_rename_in_concept)
done

lemma node_concepts_rename_in_abox_eq_other:
  "x \<noteq> y1 \<Longrightarrow> 
  x \<noteq> y2 \<Longrightarrow>
  subst_free_abox ab \<Longrightarrow>
   node_concepts_abox (rename_in_abox ab [ISubst y2 y1]) x =
   node_concepts_abox ab x"
apply (rule subset_antisym)
prefer 2
apply (rule node_concepts_rename_in_abox_subset) apply fast apply assumption+
   
apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst)
apply (clarsimp split: if_split_asm)
apply (intro exI conjI)
apply assumption
apply (rule refl)
apply simp

apply (simp add: subst_free_abox_def)
apply (rename_tac c)
apply (subgoal_tac "subst_free_form (FactFm (Inst x c))") prefer 2 apply fast
apply (simp  add: subst_free_concept_rename_in_concept)
done

(* TODO: maybe not used *)
lemma node_concepts_rename_in_abox_strict_incl: 
  "subst_free_abox ab \<Longrightarrow>
  \<not> node_concepts_abox ab y2 \<subseteq> node_concepts_abox ab y1 \<Longrightarrow>
       node_concepts_abox ab y1 \<subset> node_concepts_abox (rename_in_abox ab [ISubst y2 y1]) y1"
apply (rule psubsetI)
apply (rule node_concepts_rename_in_abox_subset) apply fast apply assumption+
apply clarsimp

apply (case_tac "y1 = y2")
apply simp

apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps)
apply clarsimp
apply (rename_tac c)
apply (drule_tac x="FactFm (Inst y1 c)" in spec) apply simp
apply (drule_tac x="FactFm (Inst y2 c)" in spec) apply simp

apply (simp add: subst_free_abox_def)
apply (rename_tac c)
apply (subgoal_tac "subst_free_form (FactFm (Inst y2 c))") prefer 2 apply fast
apply (simp  add: subst_free_concept_rename_in_concept)
done

lemma node_concepts_abox_rename_in_abox_split:
  "node_concepts_abox (rename_in_abox ab [ISubst y2 y1]) y1 =
  (\<lambda> c. rename_in_concept c [ISubst y2 y1]) ` (node_concepts_abox ab y1 \<union> node_concepts_abox ab y2)"
apply (case_tac "y1 = y2")
apply simp
apply (rule subset_antisym)
apply clarsimp
apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps)
apply (clarsimp simp add: rename_in_form_inversion_FactFm rename_in_fact_inversion_Inst 
  split :if_split_asm)
apply fastforce

apply clarsimp
apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps)
apply fastforce
done


lemma rename_in_concept_for_subst_free: "subst_free_abox ab \<Longrightarrow>
   (\<lambda>c. rename_in_concept c ren) ` node_concepts_abox ab y = node_concepts_abox ab y"
apply (rule subset_antisym)
apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps)
apply (fastforce simp add: subst_free_abox_def subst_free_concept_rename_in_concept)

apply (simp add: node_concepts_abox_def is_Inst_fact_unfold image_def rename_in_form_rename_in_abox_rewr
  del: is_Inst_fact.simps)
apply (fastforce simp add: subst_free_abox_def subst_free_concept_rename_in_concept)
done

lemma node_concepts_varbounds_pres:
  "bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    subst_free_abox (abox tab) \<Longrightarrow>
    y1 < y2 \<Longrightarrow>
    bounds_renaming_closed tab \<Longrightarrow>
    y1 \<in> fv_abox (abox tab) \<Longrightarrow>
    y2 \<in> fv_abox (abox tab) \<Longrightarrow>
     node_concepts_abox (rename_in_abox (abox tab) [ISubst y2 y1]) y1  \<subseteq> varbounds tab y1"
apply (subgoal_tac "varbounds tab y2 \<subseteq> varbounds tab y1") 
   prefer 2 apply (simp add: bounds_renaming_closed_def)
apply (simp add: deco_respecting_bounds_def)
apply (simp add: node_concepts_def)
apply (simp add: node_concepts_abox_rename_in_abox_split image_Un rename_in_concept_for_subst_free)
apply fast
done


(* The converse does not hold, for example for 
FactFm (Eq False y2 b) \<in> ab \<and> b \<noteq> y2 
*)
lemma neq_unrelated_rename_same_incl:
     "ab' = rename_in_abox ab [ISubst y2 y1] \<Longrightarrow>
   (y1::'a::linorder) < y2 \<Longrightarrow>
   y1 \<in> fv_abox ab \<Longrightarrow>
   y2 \<in> fv_abox ab \<Longrightarrow>
   neq_unrelated ab' y1 \<subseteq> neq_unrelated ab y1"
apply (simp add: neq_unrelated_def)
apply (clarsimp simp add: FactFm_Eq_rename_in_abox_inversion)
apply fastforce
done

lemma neq_unrelated_rename_other_incl:
     "ab' = rename_in_abox ab [ISubst y2 y1] \<Longrightarrow>
   (y1::'a::linorder) < y2 \<Longrightarrow>
   y1 \<in> fv_abox ab \<Longrightarrow>
   y2 \<in> fv_abox ab \<Longrightarrow>
   neq_unrelated ab' x \<subseteq> neq_unrelated ab x"
apply (simp add: neq_unrelated_def)
apply (clarsimp simp add: FactFm_Eq_rename_in_abox_inversion)
apply fastforce
done



lemma finite_neq_unrelated [simp]:
  "finite (abox tab) \<Longrightarrow> finite (neq_unrelated (abox tab) x)"
apply (rule finite_subset [where B="fv_abox (abox tab) \<times> fv_abox (abox tab)"])
apply (clarsimp simp add: neq_unrelated_def)
apply simp
done

(*
lemma "strongly_decreasing {#} (tableau_potential_for_set tab {y2}) potential_ord"
*)

lemma tableau_potential_decreases_renaming:
     "tab' =
       \<lparr>abox = rename_in_abox (abox tab) [ISubst y2 y1],
        varbounds = join_varbounds y2 y1 (varbounds tab)\<rparr> \<Longrightarrow>
       finite (abox tab) \<Longrightarrow>
       subst_free_abox (abox tab) \<Longrightarrow>
       finite_varbounds tab \<Longrightarrow>
       bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
       deco_respecting_bounds tab \<Longrightarrow>
       bounds_renaming_closed tab \<Longrightarrow>
       \<not> contains_clash (abox tab') \<Longrightarrow> 
       y1 < y2 \<Longrightarrow>
       y1 \<in> fv_abox (abox tab) \<and> y2 \<in> fv_abox (abox tab) \<and>
                    y1 \<in> fv_abox (abox tab') \<and> y2 \<notin> fv_abox (abox tab') \<Longrightarrow>
       finite (fv_tableau tab) \<Longrightarrow>
       \<not> contains_clash (abox tab) \<Longrightarrow>
       (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (subgoal_tac "y1 \<noteq> y2") prefer 2 apply simp
apply (elim conjE)
apply (rule tableau_potential_split_vars_ws_decreasing2 [where R="{}" and x=y2])
   apply (rule refl)
   apply assumption+
   apply simp_all apply blast

(*** node potential of substituted var y2 ***)
apply (subgoal_tac "\<not> node_active tab' y2 \<and> node_active tab y2") 
   prefer 2 apply (simp add: node_active_def)
apply (simp add: strongly_decreasing_def)
apply (simp add: tableau_potential_for_set_def node_potential_def potential_ord_def bool_ord_def)

(* node potential for  vars \<noteq> y2 *)
apply (rule tableau_potential_for_set_multstar)
apply simp
apply (rule ballI)
apply (rename_tac x)

apply (case_tac "x= y1")

  (*** node potential of substituting var y1 ***)
apply (subgoal_tac "node_active tab' y1 = node_active tab y1") 
  prefer 2 apply (simp add: node_active_def)

apply (subgoal_tac "varbounds tab' y1 = varbounds tab y1") 
   prefer 2 apply (simp add: join_varbounds_bounds_renaming_closed)

apply (simp add: node_potential_def potential_ord_def bool_ord_def nat_ord_def)

apply (case_tac "node_concepts tab y2 \<subseteq> node_concepts tab y1")

(*node_concepts tab y2 \<subseteq> node_concepts tab y1 \<longrightarrow> no bounded_measure decrease *)
apply (subgoal_tac "node_concepts tab' y1 = node_concepts tab y1")
  prefer 2 apply (simp add: node_concepts_def node_concepts_rename_in_abox_eq_for_incl)
apply (subgoal_tac "neq_unrelated (abox tab') y1 \<subseteq> neq_unrelated (abox tab) y1")
  prefer 2 apply (rule neq_unrelated_rename_same_incl) apply simp apply assumption+

apply (subgoal_tac "(neq_unrelated (abox tab') y1 = neq_unrelated (abox tab) y1) \<or>
  neq_unrelated (abox tab') y1 \<subset> neq_unrelated (abox tab) y1")
  prefer 2 apply fast

apply (elim disjE)
(* case neq_unrelated equal *)
apply simp
apply (subgoal_tac "card_ge_applic (rename_in_abox (abox tab) [ISubst y2 y1]) y1
       \<le> card_ge_applic (abox tab) y1") 
     prefer 2 apply (rule card_ge_applic_rename_in_abox) 
              apply assumption+ apply (simp add: node_concepts_def)
apply arith

(* case neq_unrelated strict inclusion *)
apply (subgoal_tac "card( neq_unrelated (abox tab') y1) 
                  < card (neq_unrelated (abox tab) y1)")
   prefer 2 apply (rule psubset_card_mono) apply simp apply assumption+
apply simp

(* \<not> node_concepts tab y2 \<subseteq> node_concepts tab y1 \<longrightarrow>  bounded_measure decrease *)
apply (rule disjI1)
apply (simp add: bounded_measure_ord_def)
apply (simp add: node_concepts_def node_concepts_rename_in_abox_strict_incl finite_varbounds_def)
apply (rule node_concepts_varbounds_pres) apply assumption+

                                                          
  (*** node potential of vars x unequal y1 and y2 ***)
apply (subgoal_tac "x \<noteq> y2") prefer 2 apply fast
apply (subgoal_tac "node_active tab' x = node_active tab x") 
  prefer 2 apply (simp add: node_active_def)

apply (subgoal_tac "varbounds tab' x = varbounds tab x") 
   prefer 2 apply (simp add: join_varbounds_bounds_renaming_closed)

apply (simp add: node_potential_def potential_ord_def bool_ord_def nat_ord_def)

apply (subgoal_tac "node_concepts tab' x = node_concepts tab x")
  prefer 2 apply (simp add: node_concepts_def node_concepts_rename_in_abox_eq_other)

apply (subgoal_tac "neq_unrelated (abox tab') x \<subseteq> neq_unrelated (abox tab) x")
  prefer 2 apply (rule neq_unrelated_rename_other_incl) apply simp apply assumption+

apply (subgoal_tac "(neq_unrelated (abox tab') x = neq_unrelated (abox tab) x) \<or>
  neq_unrelated (abox tab') x \<subset> neq_unrelated (abox tab) x")
  prefer 2 apply fast

apply (elim disjE)
(* case neq_unrelated equal *)
apply simp
apply (subgoal_tac "card_ge_applic (rename_in_abox (abox tab) [ISubst y2 y1]) x
       \<le> card_ge_applic (abox tab) x") 
     prefer 2 apply (rule card_ge_applic_rename_in_abox_other)
              apply assumption+
apply arith
(* case neq_unrelated strict inclusion *)
apply (subgoal_tac "card( neq_unrelated (abox tab') x) 
                  < card (neq_unrelated (abox tab) x)")
   prefer 2 apply (rule psubset_card_mono) apply simp apply assumption+
apply simp
done

(* TODO: still incorporate clash-freeness of tab'*)
lemma tableau_potential_decreases_using_potential_ord_for_eq_tableau_rule: 
   "eq_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    subst_free_abox (abox  tab) \<Longrightarrow>
    finite_varbounds tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    bounds_renaming_closed tab \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: eq_tableau_rule_def ex_rule_closure_def)
apply (rename_tac f)
apply (clarsimp 
  simp add: eq_tableau_rule_indiv.simps lift_to_tableau_rule_def
  del: eq_applicable_cases)

apply (rename_tac y1 y2)
apply (subgoal_tac "y1 \<in> fv_abox (abox tab) \<and> y2 \<in> fv_abox (abox tab)")
   prefer 2  apply (fastforce simp add: eq_applicable.simps dest: fv_form_fv_abox) 

apply (elim conjE)
apply (intro conjI impI)
apply simp
apply (rule tableau_potential_decreases_renaming) 
  apply (rule refl) apply assumption+ defer apply simp_all

apply (subgoal_tac "y2 < y1") prefer 2 apply (clarsimp simp add: eq_applicable.simps) apply simp
apply (rule tableau_potential_decreases_renaming) 
              apply (rule refl) apply assumption+ defer apply simp_all

sorry (* clash-freeness of tab' *)


lemma tableau_potential_decreases_using_potential_ord_for_numrestrc_lt_tableau_rule: 
   "numrestrc_lt_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    subst_free_abox (abox  tab) \<Longrightarrow>
    finite_varbounds tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    bounds_renaming_closed tab \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: numrestrc_lt_tableau_rule_def ex_rule_closure_def)
apply (rename_tac f)
apply (clarsimp 
  simp add: numrestrc_lt_tableau_rule_indiv.simps lift_to_tableau_rule_def
  del: numrestrc_lt_applicable_cases)

apply (rename_tac y1 y2)
apply (subgoal_tac "FactFm (AtomR True r x y1) \<in> abox tab") prefer 2 apply fast
apply (subgoal_tac "FactFm (AtomR True r x y2) \<in> abox tab") prefer 2 apply fast

apply (subgoal_tac "y1 \<in> fv_abox (abox tab) \<and> y2 \<in> fv_abox (abox tab)")
   prefer 2 apply (fastforce dest: fv_form_fv_abox)

apply (elim conjE)

apply (rule tableau_potential_decreases_renaming) 
  apply (rule refl) apply assumption+ apply simp_all

sorry (* clash-freeness of tab' *)


lemma neq_unrelated_strict_incl:
   "ab' = insert (FactFm (Eq False x y)) (abox tab) \<Longrightarrow>
    x < y \<Longrightarrow>
    x \<in> fv_abox (abox tab) \<Longrightarrow>
    y \<in> fv_abox (abox tab) \<Longrightarrow>
    \<forall>s. FactFm (Eq s x y) \<notin> abox tab \<Longrightarrow>
    \<forall>s. FactFm (Eq s y x) \<notin> abox tab \<Longrightarrow>
    neq_unrelated ab' y \<subset> neq_unrelated (abox tab) y"
apply (subgoal_tac "(x, y) \<in> neq_unrelated (abox tab) y")
  prefer 2 apply (simp add: neq_unrelated_def)
apply (subgoal_tac "(x, y) \<notin> neq_unrelated ab' y")
  prefer 2 apply (simp add: neq_unrelated_def)
apply (subgoal_tac "neq_unrelated ab' y \<subseteq> neq_unrelated (abox tab) y")
  prefer 2 
  apply (rule neq_unrelated_antimono)
  apply fastforce
  apply (fastforce simp add: fv_abox_bounded_def)
  apply simp
apply clarsimp
done

lemma finite_card_ge_applicable_set [simp]: 
  "finite ab \<Longrightarrow> finite (card_ge_applic_set ab z)"
by (simp add: card_ge_applic_set_def)

lemma card_ge_applic_insert_ineq: 
     "finite ab \<Longrightarrow>
      ab' = insert (FactFm (Eq False x y)) ab \<Longrightarrow>
      card_ge_applic ab' z \<le> card_ge_applic ab z"
apply (simp add: card_ge_applic_def)
apply (rule card_mono, simp)
apply (clarsimp simp add: card_ge_applic_set_def)
apply (clarsimp simp add: numrestrc_ge_applicable.simps)
apply (fast dest: numrestrc_ge_blocked_mono [where B="(insert (FactFm (Eq False x y)) ab)"])
done


lemma tableau_potential_decreases_add_inequality: 
  "tab' = \<lparr>abox = insert (FactFm (Eq False x y)) (abox tab), 
           varbounds =  (varbounds tab) \<rparr> \<Longrightarrow>
   finite (abox tab) \<Longrightarrow>
   bounds_renaming_closed tab \<Longrightarrow>
   \<not> contains_clash (abox tab) \<Longrightarrow>
   finite (fv_tableau tab) \<Longrightarrow>
   x < y \<Longrightarrow>
   x \<in> fv_abox (abox tab) \<Longrightarrow>
   y \<in> fv_abox (abox tab) \<Longrightarrow>
   \<forall>s. FactFm (Eq s x y) \<notin> abox tab \<Longrightarrow>
   \<forall>s. FactFm (Eq s y x) \<notin> abox tab \<Longrightarrow>
   (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord "
apply (subgoal_tac "\<forall> z \<in> fv_abox (abox tab). node_active tab' z = node_active tab z")
  prefer 2
  apply (rule ballI)
  apply (rule node_active_same_extend [where E="{(FactFm (Eq False x y))}"])
  apply simp
  apply fastforce
  
apply (subgoal_tac "\<forall> z \<in> fv_abox (abox tab). node_concepts tab' z = node_concepts tab z")
  prefer 2
  apply (simp add: node_concepts_def)

apply (rule tableau_potential_split_vars_ws_decreasing2 [where x=y and R="{y}"])
apply (rule refl)
apply simp_all
apply fast

(* stronly decreasing for y *)
apply (simp add: tableau_potential_for_set_def strongly_decreasing_def)
apply (simp add: node_potential_def potential_ord_def 
       bool_ord_def nat_ord_def bounded_measure_ord_def)
apply (subgoal_tac "card (neq_unrelated (abox tab') y) < card (neq_unrelated (abox tab) y)")
  prefer 2
  apply (rule psubset_card_mono)
  apply simp_all
  apply (rule neq_unrelated_strict_incl) apply simp apply assumption+

(* weakly decreasing for all others *)
apply (rule tableau_potential_for_set_multstar) apply simp
apply (rule ballI)
apply clarsimp
apply (clarsimp simp add: node_potential_def potential_ord_def bool_ord_def nat_ord_def)
apply (rename_tac z)
apply (subgoal_tac "card (neq_unrelated (abox tab') z) \<le> card (neq_unrelated (abox tab) z)")
  prefer 2 
  apply (rule card_mono, simp)
  apply (rule neq_unrelated_antimono) apply fastforce apply (fastforce simp add: fv_abox_bounded_def)
apply clarsimp

apply (subgoal_tac "card_ge_applic (abox tab') z \<le> card_ge_applic (abox tab) z")
apply simp
apply (rule card_ge_applic_insert_ineq, assumption) apply simp
done

lemma tableau_potential_decreases_using_potential_ord_for_eq_compl_tableau_rule: 
   "eq_compl_tableau_rule tab tab' \<Longrightarrow>
    finite (abox tab) \<Longrightarrow>
    subst_free_abox (abox  tab) \<Longrightarrow>
    finite_varbounds tab \<Longrightarrow>
    bounds_subset_closed_pn (varbounds tab) \<Longrightarrow>
    deco_respecting_bounds tab \<Longrightarrow>
    bounds_renaming_closed tab \<Longrightarrow>
  \<not> contains_clash (abox tab) \<Longrightarrow>
    (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (clarsimp simp add: eq_compl_tableau_rule.simps)

apply (elim disjE)

(* cases insert x \<noteq> y *)
apply clarsimp
apply (rule tableau_potential_decreases_add_inequality, rule refl)
apply simp_all

(* cases rename y := x *)
apply (rule tableau_potential_decreases_renaming)
apply (rule refl)
apply simp_all

sorry (* contains clash in rename_abox *)

(*---------- almost the same def as above, with reach predicate *)
definition reach :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "reach rl init = Collect (rl^** init)"
  
lemma invariant_in_reach:
  "invar init \<Longrightarrow> rule_resp_invariant (\<lambda> a. True) invar rl \<Longrightarrow> s \<in> reach rl init \<Longrightarrow> invar s"
by (simp add: reach_def)
   (fastforce elim: rtranclp_induct simp add: rule_resp_invariant_def)

lemma tableau_invariant_initial: "tableau_invariant (initial_tableau ab)"
sorry

(*-------------------------------------------------------------------------------*)
(* Proof of invariants *)
(*-------------------------------------------------------------------------------*)

(*--- auxiliary lemmas ---*)


(* TODO: move elsewhere *)
lemma finite_image_set2_dep:
  "finite {x. P x} \<Longrightarrow> finite {y. Q y} \<Longrightarrow> finite {f x y | x y. P x \<and> Q y \<and> R x y}"
  by (rule finite_subset [where B = "\<Union>x \<in> {x. P x}. \<Union>y \<in> {y. Q y}. {f x y}"]) auto


   (* TODO: move elsewhere *)
lemma finite_rename_in_abox [simp]: "finite A \<Longrightarrow> finite (rename_in_abox A ren)"
by (clarsimp simp add: rename_in_abox_def)

lemma finite_numrestrc_ge_rule_facts [simp]: 
  "finite Y \<Longrightarrow> finite (numrestrc_ge_rule_facts c r x Y)"
by (auto simp add: numrestrc_ge_rule_facts_def finite_image_set2_dep)

(* the preconditions are not minimal *)
lemma finite_join_varbounds: 
  "finite (varb v) \<Longrightarrow> finite (varb v2) \<Longrightarrow> finite (join_varbounds v2 v1 varb v)"
by (fastforce simp add: join_varbounds_def)


lemma finite_successor_varbounds: "finite varb \<Longrightarrow> finite (successor_varbounds r varb)"
by (simp add: successor_varbounds_def)


(*--- finite abox preservation ---*)

lemma finite_abox_conjc_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) conjc_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def conjc_tableau_rule_def ex_rule_closure_def)
   (clarsimp simp add: conjc_tableau_rule_indiv_def lift_to_tableau_rule_def conjc_rule_indiv.simps)
lemma finite_abox_disjc_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) disjc_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def disjc_tableau_rule_def ex_rule_closure_def)
   (fastforce simp add: disjc_tableau_rule_indiv_def lift_to_tableau_rule_def disjc_rule_indiv.simps)
lemma finite_abox_eq_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def eq_tableau_rule_def
       ex_rule_closure_def eq_tableau_rule_indiv.simps)
apply (rename_tac ab ab' x y)
apply (case_tac "x < y")
apply clarsimp+
done
lemma finite_abox_eq_compl_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) eq_compl_tableau_rule"
  by (fastforce  simp add: rule_resp_invariant_def eq_compl_tableau_rule.simps)
lemma finite_abox_choose_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) choose_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def choose_tableau_rule_def ex_rule_closure_def)
  (fastforce simp add: choose_tableau_rule_indiv_def lift_to_tableau_rule_def choose_rule_indiv.simps)
lemma finite_abox_numrestrc_ge_tableau_rule_indiv:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) (numrestrc_ge_tableau_rule_indiv f)"
by (clarsimp simp add: rule_resp_invariant_def numrestrc_ge_tableau_rule_indiv.simps)
lemma finite_abox_numrestrc_ge_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) numrestrc_ge_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def numrestrc_ge_tableau_rule_def
       ex_rule_closure_def numrestrc_ge_tableau_rule_indiv.simps)
lemma finite_abox_numrestrc_lt_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab.  finite (abox tab)) numrestrc_lt_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def numrestrc_lt_tableau_rule_def
       ex_rule_closure_def numrestrc_lt_tableau_rule_indiv.simps)

(*--- finite varbounds preservation ---*)
lemma finite_varbounds_lift_to_tableau_rule [rule_format]:
      "lift_to_tableau_rule rl_indiv t t' \<Longrightarrow>
       \<forall> ab ab'. rl_indiv ab ab' \<longrightarrow> fv_abox ab' \<subseteq> fv_abox ab \<Longrightarrow>
       finite_varbounds t \<Longrightarrow> finite_varbounds t' "
by (fastforce simp add: lift_to_tableau_rule_def finite_varbounds_def)

lemma finite_varbounds_conjc_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds conjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       conjc_tableau_rule_def conjc_tableau_rule_indiv_def)
apply (erule finite_varbounds_lift_to_tableau_rule)
apply (fastforce simp add: conjc_rule_indiv.simps dest: fv_form_fv_abox)+
done
lemma finite_varbounds_disjc_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds disjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       disjc_tableau_rule_def disjc_tableau_rule_indiv_def)
apply (erule finite_varbounds_lift_to_tableau_rule)
apply (fastforce simp add: disjc_rule_indiv.simps dest: fv_form_fv_abox)+
done
lemma finite_varbounds_eq_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       eq_tableau_rule_def eq_tableau_rule_indiv.simps)
apply (rename_tac t t' x y)
apply (case_tac "x < y")
apply (clarsimp simp add: finite_varbounds_def)
apply (fastforce simp add:  finite_join_varbounds dest: fv_form_fv_abox)
apply (clarsimp simp add: finite_varbounds_def)
apply (fastforce simp add:  finite_join_varbounds dest: fv_form_fv_abox)
done
lemma finite_varbounds_eq_compl_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds eq_compl_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def 
       eq_compl_tableau_rule.simps finite_varbounds_def)
apply (elim disjE)
apply fastforce
apply (clarsimp simp add: join_varbounds_def split: if_split_asm)
done
lemma finite_varbounds_choose_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds choose_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       choose_tableau_rule_def choose_tableau_rule_indiv_def)
apply (erule finite_varbounds_lift_to_tableau_rule)
apply (fastforce simp add: choose_rule_indiv.simps dest: fv_form_fv_abox)+
done

lemma finite_varbounds_numrestrc_ge_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds numrestrc_ge_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_ge_tableau_rule_def numrestrc_ge_tableau_rule_indiv.simps)
apply (clarsimp simp add: finite_varbounds_def)
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
   (* TODO numrestrc_ge_successor_varbounds_old_def: finite varbounds *) 
apply (fastforce simp add: fresh_set_def 
       intro: finite_successor_varbounds
       dest: fv_form_fv_abox)
done

lemma finite_varbounds_numrestrc_lt_tableau_rule:
  "rule_resp_invariant initcond finite_varbounds numrestrc_lt_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_lt_tableau_rule_def numrestrc_lt_tableau_rule_indiv.simps)
apply (clarsimp simp add: finite_varbounds_def)
apply (rename_tac t S x r c y1 y2)
apply (subgoal_tac " FactFm (AtomR True r x y1) \<in> abox t \<and> FactFm (Inst y1 c) \<in> abox t")
   prefer 2 apply blast
apply (subgoal_tac " FactFm (AtomR True r x y2) \<in> abox t \<and> FactFm (Inst y2 c) \<in> abox t")
   prefer 2 apply blast
apply (subgoal_tac "y1 \<in> fv_abox (abox t)")
   prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (subgoal_tac "y2 \<in> fv_abox (abox t)")
   prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (fast intro: finite_join_varbounds)
done


(*--- bounds_subset preservation ---*)
(* no dependencies on initcond *)

lemma bounds_subset_closed_pn_lift_to_tableau_rule [rule_format]:
      "lift_to_tableau_rule rl_indiv t t' \<Longrightarrow>
       bounds_subset_closed_pn (varbounds t) \<Longrightarrow> bounds_subset_closed_pn (varbounds t')"
by (fastforce simp add: lift_to_tableau_rule_def)

lemma bounds_subset_closed_pn_join_varbounds:
   "bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
       bounds_subset_closed_pn (join_varbounds y x (varbounds t))"
by (fastforce simp add: bounds_subset_closed_pn_def join_varbounds_def)

lemma bounds_subset_closed_conjc_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) conjc_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       conjc_tableau_rule_def conjc_tableau_rule_indiv_def)
   (erule bounds_subset_closed_pn_lift_to_tableau_rule, assumption)

lemma bounds_subset_closed_disjc_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) disjc_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       disjc_tableau_rule_def disjc_tableau_rule_indiv_def)
   (erule bounds_subset_closed_pn_lift_to_tableau_rule, assumption)

lemma bounds_subset_closed_eq_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       eq_tableau_rule_def eq_tableau_rule_indiv.simps)
apply (auto simp add: bounds_subset_closed_pn_join_varbounds)
done
lemma bounds_subset_closed_eq_compl_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) eq_compl_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def eq_compl_tableau_rule.simps)
apply (auto simp add: bounds_subset_closed_pn_join_varbounds)
done
lemma bounds_subset_closed_choose_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) choose_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       choose_tableau_rule_def choose_tableau_rule_indiv_def)
   (erule bounds_subset_closed_pn_lift_to_tableau_rule, assumption)

lemma bounds_subset_closed_numrestrc_ge_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) numrestrc_ge_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_ge_tableau_rule_def numrestrc_ge_tableau_rule_indiv.simps)
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
apply (simp add: bounds_subset_closed_pn_def)
apply (clarsimp simp add: successor_varbounds_def)
apply (fastforce dest: sub_concepts_pn_closed)
done

lemma bounds_subset_closed_numrestrc_lt_tableau_rule:
  "rule_resp_invariant initcond (\<lambda> tab. bounds_subset_closed_pn (varbounds tab)) numrestrc_lt_tableau_rule"
by (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_lt_tableau_rule_def numrestrc_lt_tableau_rule_indiv.simps
       bounds_subset_closed_pn_join_varbounds)



(*--- deco_respecting_bounds preservation ---*)
(* initcond depends on: 
bounds_subset_closed_pn : conjc, disjc, choose_tableau_rule
subst_free_abox : eq, numrestrc_lt
successor_varbounds_closed : choose
*)

lemma deco_respecting_bounds_lift_to_tableau_rule [rule_format]:
      "lift_to_tableau_rule rl_indiv t t' \<Longrightarrow>
      bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
       \<forall> ab ab'. rl_indiv ab ab' \<longrightarrow> 
          (fv_abox ab' \<subseteq> fv_abox ab \<and> 
          (\<forall>x\<in>fv_abox ab'. node_concepts_abox ab' x \<subseteq> 
                        (\<Union> (sub_concepts_pn ` (node_concepts_abox ab x))))) \<Longrightarrow>
       deco_respecting_bounds t \<Longrightarrow> deco_respecting_bounds t'"
apply (clarsimp simp add: deco_respecting_bounds_def lift_to_tableau_rule_def node_concepts_def)
apply (drule spec, drule spec, drule mp, assumption)
apply (drule_tac x=x in bspec) apply fast
apply clarsimp
apply (drule_tac x=x in bspec, assumption)
apply (fastforce simp add: bounds_subset_closed_pn_def)
done

lemma "FactFm (Inst x c) \<in> ab \<Longrightarrow> c \<in> node_concepts_abox ab x"
by (fastforce simp add: node_concepts_abox_def image_def)


lemma deco_respecting_bounds_conjc_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
  rule_resp_invariant initcond deco_respecting_bounds conjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  conjc_tableau_rule_def conjc_tableau_rule_indiv_def)
apply (erule deco_respecting_bounds_lift_to_tableau_rule) apply simp_all
apply (intro conjI ballI)
apply (fastforce dest: fv_form_fv_abox simp add: conjc_rule_indiv.simps)

apply (clarsimp simp add: conjc_rule_indiv.simps split :if_split_asm)
apply (fastforce elim: rev_bexI simp add: Let_def in_node_concepts_abox [THEN sym])+
done

lemma deco_respecting_bounds_disjc_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
  rule_resp_invariant initcond deco_respecting_bounds disjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  disjc_tableau_rule_def disjc_tableau_rule_indiv_def)
apply (erule deco_respecting_bounds_lift_to_tableau_rule) apply simp_all
apply (intro conjI ballI)
apply (fastforce dest: fv_form_fv_abox simp add: disjc_rule_indiv.simps)

apply (clarsimp simp add: disjc_rule_indiv.simps split : if_split_asm)
apply (fastforce elim: rev_bexI simp add: Let_def in_node_concepts_abox [THEN sym] 
  split : if_split_asm)+
done

lemma deco_respecting_bounds_eq_tableau_rule [rule_format]:
  "\<forall> t. initcond t \<longrightarrow> subst_free_abox (abox t) \<Longrightarrow>
  rule_resp_invariant initcond deco_respecting_bounds eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       eq_tableau_rule_def eq_tableau_rule_indiv.simps)
apply (clarsimp simp add: deco_respecting_bounds_def node_concepts_def)
apply (rename_tac t t' x y v c)
apply (case_tac "x < y")

(* case x < y *)
apply (clarsimp split : if_split_asm)
apply (elim disjE)
apply (clarsimp simp add: join_varbounds_def)
apply (intro conjI impI ballI)
apply clarsimp

apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply fast

apply (fastforce simp add: node_concepts_rename_in_abox_eq_other)
apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply (rename_tac t v c x y)
apply (subgoal_tac "x \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) 
apply fast

apply (fastforce dest: fv_form_fv_abox)

(* case \<not> x < y *)

apply (clarsimp split : if_split_asm)
apply (elim disjE)
apply (clarsimp simp add: join_varbounds_def)
apply (intro conjI impI ballI)
apply clarsimp

apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply fast

apply (fastforce simp add: node_concepts_rename_in_abox_eq_other)
apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply (rename_tac t v c x y)
apply (subgoal_tac "y \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) 
apply fast

apply (fastforce dest: fv_form_fv_abox)
done


lemma deco_respecting_bounds_eq_compl_tableau_rule [rule_format]:
  "\<forall> t. initcond t \<longrightarrow> subst_free_abox (abox t) \<Longrightarrow>
  rule_resp_invariant initcond deco_respecting_bounds eq_compl_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def eq_compl_tableau_rule.simps)
apply (clarsimp simp add: deco_respecting_bounds_def node_concepts_def)
apply (rename_tac t t' x y v c)

apply (elim disjE)

(* case insert inequality *)
apply clarsimp
apply fastforce

(* case rename for equality *)
apply (clarsimp split : if_split_asm)
apply (elim disjE)
apply (clarsimp simp add: join_varbounds_def)
apply (intro conjI impI ballI)
apply clarsimp

apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply fast

apply (fastforce simp add: node_concepts_rename_in_abox_eq_other)
apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply (rename_tac t v c x y)
apply (subgoal_tac "x \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) 
apply fast
done


(* TODO: hogged-up proof, should be beautified *)
lemma deco_respecting_bounds_choose_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> successor_varbounds_closed t \<Longrightarrow>
  \<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
  rule_resp_invariant initcond deco_respecting_bounds choose_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  choose_tableau_rule_def choose_tableau_rule_indiv_def)

apply (clarsimp simp add: deco_respecting_bounds_def lift_to_tableau_rule_def node_concepts_def)
apply (clarsimp simp add: choose_rule_indiv.simps)
apply (elim disjE)
apply (clarsimp split : if_split_asm)
apply (elim disjE)
apply clarsimp

apply (rename_tac t y x n r c)
apply (simp add: successor_varbounds_closed_def)
apply (subgoal_tac "([<] n r c) \<in> varbounds t x") 
      prefer 2 
      apply (fastforce dest: fv_form_fv_abox simp add: deco_respecting_bounds_def node_concepts_def in_node_concepts_abox [THEN sym])
      
apply fast

apply (rename_tac t y c' x n r c)
apply (subgoal_tac "y \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) apply fast
apply (elim disjE)
apply (rename_tac t y' c' x n r c y)
apply (subgoal_tac "y' \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) apply fast

apply (fastforce simp add: successor_varbounds_closed_def)

apply (clarsimp split : if_split_asm)
apply (elim disjE)

apply (rename_tac t y c' x n r c)
apply (simp add: successor_varbounds_closed_def)
apply (subgoal_tac "([<] n r c) \<in> varbounds t x") 
      prefer 2 
      apply (fastforce dest: fv_form_fv_abox simp add: deco_respecting_bounds_def node_concepts_def in_node_concepts_abox [THEN sym])
apply (subgoal_tac "c \<in> varbounds t y") prefer 2 apply fast
apply (unfold bounds_subset_closed_pn_def)
apply (subgoal_tac "sub_concepts_pn c \<subseteq> varbounds t y") prefer 2 apply blast
apply (subgoal_tac "neg_norm_concept False c \<in> sub_concepts_pn c") apply blast
apply (rule neg_norm_concept_sub_concepts_pn)

apply (rename_tac t y c' x n r c)
apply (subgoal_tac "y \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) apply blast
apply (elim disjE)
apply (rename_tac t y' c' x n r c y)
apply (subgoal_tac "y' \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) apply blast
apply (rename_tac t y' c' x n r c y)
apply (subgoal_tac "y' \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox) apply blast
done

lemma FactFm_Inst_node_concepts_abox: 
   "FactFm (Inst x c) \<in> ab \<Longrightarrow> c \<in> node_concepts_abox ab x"
by (fastforce simp add: node_concepts_abox_def image_def)


lemma deco_respecting_bounds_numrestrc_ge_tableau_rule_aux1: 
   "FactFm (Inst x ([\<ge>] n r c)) \<in> abox t \<Longrightarrow>
       \<forall>x\<in>fv_abox (abox t).
          node_concepts_abox (abox t) x \<subseteq> varbounds t x \<Longrightarrow>
     c \<in> successor_varbounds r (varbounds t x)"
apply (simp add: successor_varbounds_def)
apply (subgoal_tac "([\<ge>] n r c) \<in> varbounds t x") 
   prefer 2 apply (fastforce dest: FactFm_Inst_node_concepts_abox fv_form_fv_abox)
apply (intro exI conjI)
apply assumption
apply (simp add: is_NumRestrC_concept_def)
apply simp
done

lemma not_in_fv_abox_node_concepts_empty:
   "y \<notin> fv_abox ab \<Longrightarrow> node_concepts_abox ab y = {}"
by (auto simp add: fv_abox_def node_concepts_abox_def split : form.split fact.split)
    
lemma deco_respecting_bounds_numrestrc_ge_tableau_rule_aux2: 
    "FactFm (Inst x ([\<ge>] n r c)) \<in> abox t \<Longrightarrow>
       \<forall>x\<in>fv_abox (abox t).
          node_concepts_abox (abox t) x \<subseteq> varbounds t x \<Longrightarrow>
       x \<notin> Y \<Longrightarrow>
       y \<in> Y \<Longrightarrow>
       fresh_set_incr Y (abox t) \<Longrightarrow>
       cy \<in> node_concepts_abox (abox t) y \<Longrightarrow>
       cy \<in> successor_varbounds r (varbounds t x)"
apply (simp add: successor_varbounds_def)
apply (subgoal_tac "([\<ge>] n r c) \<in> varbounds t x") 
   prefer 2 apply (fastforce dest: FactFm_Inst_node_concepts_abox fv_form_fv_abox)
apply (intro exI conjI)
apply assumption
apply (simp add: is_NumRestrC_concept_def)
apply (simp add: bounds_subset_closed_pn_def)

apply (drule fresh_set_incr_fresh_set)
apply (simp add: fresh_set_def)

apply (subgoal_tac "y \<notin> fv_abox (abox t)") prefer 2 apply fast
apply (fast dest: not_in_fv_abox_node_concepts_empty)
done

lemma deco_respecting_bounds_numrestrc_ge_tableau_rule:
  "rule_resp_invariant initcond deco_respecting_bounds numrestrc_ge_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_ge_tableau_rule_def numrestrc_ge_tableau_rule_indiv.simps)
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
apply (clarsimp simp add: deco_respecting_bounds_def node_concepts_def)
apply (intro conjI impI ballI)
prefer 7 apply (fast intro: deco_respecting_bounds_numrestrc_ge_tableau_rule_aux1)
prefer 7 apply (fast intro: deco_respecting_bounds_numrestrc_ge_tableau_rule_aux2)
apply (fastforce simp add: fresh_set_def dest: fresh_set_incr_fresh_set fv_form_fv_abox)+
done


lemma deco_respecting_bounds_numrestrc_lt_tableau_rule [rule_format]:
  "\<forall> t. initcond t \<longrightarrow> subst_free_abox (abox t) \<Longrightarrow>
  rule_resp_invariant initcond deco_respecting_bounds numrestrc_lt_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_lt_tableau_rule_def numrestrc_lt_tableau_rule_indiv.simps)
apply (clarsimp simp add: deco_respecting_bounds_def node_concepts_def)
apply (rename_tac t S x r c y1 y2)
apply (subgoal_tac "y1 \<in> fv_abox (abox t)")
  prefer 2 apply (drule_tac x=y1 in bspec, assumption) apply (fastforce dest: fv_form_fv_abox)
apply (subgoal_tac "y2 \<in> fv_abox (abox t)")
  prefer 2 apply (drule_tac x=y2 in bspec, assumption) apply (fastforce dest: fv_form_fv_abox)

apply simp
apply (intro conjI impI ballI)
apply (clarsimp simp add: join_varbounds_def)

apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split 
  image_Un rename_in_concept_for_subst_free)
apply fast

apply (simp add: join_varbounds_def node_concepts_abox_rename_in_abox_split
  image_Un rename_in_concept_for_subst_free)
apply (intro conjI impI)
apply fast
apply fast

apply (simp add: node_concepts_rename_in_abox_eq_other)
done




(*--- successor_varbounds_closed preservation ---*)


lemma successor_varbounds_closed_conjc_tableau_rule:
  "rule_resp_invariant initcond successor_varbounds_closed conjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  conjc_tableau_rule_def conjc_tableau_rule_indiv_def lift_to_tableau_rule_def
  conjc_rule_indiv.simps)
apply (clarsimp simp add: successor_varbounds_closed_def)
done

lemma successor_varbounds_closed_disjc_tableau_rule:
  "rule_resp_invariant initcond successor_varbounds_closed disjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  disjc_tableau_rule_def disjc_tableau_rule_indiv_def lift_to_tableau_rule_def
  disjc_rule_indiv.simps)
apply (fastforce simp add: successor_varbounds_closed_def)
done

lemma bounds_subset_closed_pn_varbounds: "bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
             [<] n r c \<in> varbounds t x \<Longrightarrow> c \<in> varbounds t x"
apply (simp add: bounds_subset_closed_pn_def)
apply (subgoal_tac "c \<in> sub_concepts_pn ([<] n r c)")
apply fast
apply (simp add: Let_def)
done

lemma successor_varbounds_closed_rename:
  "\<forall> t. initcond t \<longrightarrow> bounds_renaming_closed t \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> contraction_stable t \<Longrightarrow>
       initcond t \<Longrightarrow>
       successor_varbounds_closed t \<Longrightarrow>
       (x::'a::linorder) < y \<Longrightarrow>
       x \<in> fv_abox (abox t) \<Longrightarrow>
       y \<in> fv_abox (abox t) \<Longrightarrow>
       \<not> neq_complete y (abox t) \<Longrightarrow>
       successor_varbounds_closed
        \<lparr>abox = rename_in_abox (abox t) [ISubst y x],
         varbounds = join_varbounds y x (varbounds t)\<rparr> "
apply (subgoal_tac "x \<noteq> y") prefer 2 apply simp
apply (clarsimp simp add: successor_varbounds_closed_def)
apply (rename_tac x' n r c y')

apply (clarsimp simp add: FactFm_AtomR_rename_in_abox_inversion)

apply (clarsimp simp add: join_varbounds_def)
(* 1 subgoal *)
apply (case_tac "y' = y")

(* 2 subg, case y' = y *)
apply simp

(* 1 subg, case y' \<noteq> y *)
apply simp
apply (intro conjI impI)

(* 2 subgoals *)
apply (case_tac "x' = x")
apply simp
apply (fast dest: bounds_subset_closed_pn_varbounds)

(* 2 subg, case y' \<noteq> y *)
apply (simp split : if_split_asm)
apply fast

(* 1 subg, case y' \<noteq> y , y' \<noteq> x  *)
apply (case_tac "x' = x")
apply simp

(* 2 subg, case y' \<noteq> y , y' \<noteq> x , x' = x *)
apply (subgoal_tac "[<] n r c \<in> varbounds t x") 
  prefer 2 apply (fastforce simp add: bounds_renaming_closed_def)

apply (case_tac "FactFm (AtomR True r x y') \<in> abox t")

(* 3 subg *)
apply simp+
(* 2 subg, problematic case requiring contraction stability *)
apply (subgoal_tac "\<forall>x<y. x \<in> fv_abox (abox t) \<longrightarrow> varbounds t x \<subseteq> varbounds t y")
  prefer 2 apply (fastforce simp add: contraction_stable_def) 
apply fastforce
(* 1 subg *)
apply (simp split : if_split_asm)
done



(* TODO for the following two: 
  the remaining goal corresponds to a clash state of the resulting abox.
  Include this into the notion of rule_resp_invariant ?
*)
lemma successor_varbounds_closed_eq_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_renaming_closed t \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> contraction_stable t \<Longrightarrow> 
   rule_resp_invariant initcond successor_varbounds_closed eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  eq_tableau_rule_def eq_tableau_rule_indiv.simps)
apply (rename_tac t t' x y)

apply (subgoal_tac "x \<in> fv_abox (abox t) \<and> y \<in> fv_abox (abox t)")
   prefer 2 apply (fastforce simp add: eq_applicable.simps dest: fv_form_fv_abox)

apply (case_tac "x < y")
apply (subgoal_tac "\<not> neq_complete y (abox t)")
apply clarsimp
apply (rule successor_varbounds_closed_rename, assumption+)
defer

apply (subgoal_tac "\<not> neq_complete x (abox t)")
apply clarsimp
apply (rule successor_varbounds_closed_rename, assumption+)
apply simp+

sorry (* neq_complete *)

(* same situation as for eq: 
neq_complete y2 (abox t)   and  y1 < y2 and there will be a contraction y2 := y1
that will lead to a clashed abox
*)
lemma successor_varbounds_closed_numrestrc_lt_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_renaming_closed t \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> contraction_stable t \<Longrightarrow> 
   rule_resp_invariant initcond successor_varbounds_closed numrestrc_lt_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  numrestrc_lt_tableau_rule_def numrestrc_lt_tableau_rule_indiv.simps)

apply (rename_tac t S x r c y1 y2) 
apply (rule successor_varbounds_closed_rename, assumption+)
apply (subgoal_tac "FactFm (Inst y1 c) \<in> abox t") prefer 2 apply fast
apply (fastforce dest: fv_form_fv_abox)
apply (subgoal_tac "FactFm (Inst y2 c) \<in> abox t") prefer 2 apply fast
apply (fastforce dest: fv_form_fv_abox)

sorry (* neq_complete *)


lemma successor_varbounds_closed_choose_tableau_rule:
  "rule_resp_invariant initcond successor_varbounds_closed choose_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  choose_tableau_rule_def choose_tableau_rule_indiv_def lift_to_tableau_rule_def
  choose_rule_indiv.simps)
apply (elim disjE)
apply (clarsimp simp add: successor_varbounds_closed_def)+
done


(* TODO: move the following lemmas about successor_varbounds elsewhere *)

lemma sub_concepts_pn_trans: 
   "sub_concepts_pn c \<subseteq> sub_concepts_pn c' \<Longrightarrow> c \<in> sub_concepts_pn c' "
apply (insert sub_concepts_pn_self [of c])
apply fast
done

lemma NumRestrC_successor_varbounds_pres: "([<] n r' c) \<in> successor_varbounds r vbs \<Longrightarrow>
       c \<in> successor_varbounds r vbs"
apply (clarsimp simp add: successor_varbounds_def)
apply (intro exI conjI)
apply assumption+
apply (drule sub_concepts_pn_closed)
apply (clarsimp simp add: Let_def)
apply (erule sub_concepts_pn_trans)
done

lemma NumRestrC_successor_varbounds: "([<] n r c) \<in> vbs \<Longrightarrow>
       c \<in> successor_varbounds r vbs"
apply (clarsimp simp add: successor_varbounds_def)
apply (intro exI conjI)
apply assumption+
apply (clarsimp simp add: is_NumRestrC_concept_unfold)
apply (clarsimp simp add: Let_def)
done


lemma successor_varbounds_closed_numrestrc_ge_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_renaming_closed t \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow> 
   \<forall> t. initcond t \<longrightarrow> contraction_stable t \<Longrightarrow> 
   rule_resp_invariant initcond successor_varbounds_closed numrestrc_ge_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
  numrestrc_ge_tableau_rule_def numrestrc_ge_tableau_rule_indiv.simps)
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
apply (clarsimp simp add: successor_varbounds_closed_def)

apply (rename_tac t x r c Y y')
apply (intro conjI impI allI)
apply (rename_tac t x r c Y y' n r' c' y)

apply (erule NumRestrC_successor_varbounds_pres)

apply (erule NumRestrC_successor_varbounds_pres)

apply (simp add: numrestrc_ge_rule_facts_def)

apply (subgoal_tac "y' \<in> fv_abox (abox t)") 
   prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (drule fresh_set_incr_fresh_set) apply (simp add: fresh_set_def) apply fast


apply (clarsimp simp add: numrestrc_ge_rule_facts_def)
apply (erule NumRestrC_successor_varbounds)

apply (subgoal_tac "y \<in> fv_abox (abox t)") 
   prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (drule fresh_set_incr_fresh_set) apply (simp add: fresh_set_def) apply fast

apply (clarsimp simp add: numrestrc_ge_rule_facts_def)
done



(*--- contraction_stable preservation ---*)

lemma contraction_stable_lift_to_tableau_rule: 
   "lift_to_tableau_rule rl_indiv t t' \<Longrightarrow>
       \<forall> f. rl_indiv (abox t) (abox t') \<longrightarrow> f \<in> abox t' \<longrightarrow> 
                is_atomic_role_fact UNIV f \<longrightarrow>  f \<in> abox t \<Longrightarrow>
       rl_indiv (abox t) (abox t') \<longrightarrow> fv_abox (abox t) = fv_abox (abox t') \<Longrightarrow>
       \<forall> x. rl_indiv (abox t) (abox t') \<longrightarrow> neq_complete x (abox t) = neq_complete x (abox t') \<Longrightarrow> 
       contraction_stable t \<Longrightarrow> contraction_stable t'"
by (fastforce
  simp add: lift_to_tableau_rule_def contraction_stable_def is_atomic_role_fact_def)


lemma contraction_stable_conjc_tableau_rule:
  "rule_resp_invariant initcond contraction_stable conjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       conjc_tableau_rule_def conjc_tableau_rule_indiv_def)
apply (erule contraction_stable_lift_to_tableau_rule)
apply (fastforce simp add: conjc_rule_indiv.simps is_atomic_role_fact_def)
apply (clarsimp simp add: conjc_rule_indiv.simps)
apply (drule fv_form_fv_abox) apply simp apply fast
apply (clarsimp simp add: conjc_rule_indiv.simps)
apply (rule neq_complete_not_eq_fact) apply clarsimp+ 
apply (drule fv_form_fv_abox) apply simp apply fast
apply fastforce+
done

lemma contraction_stable_disjc_tableau_rule:
  "rule_resp_invariant initcond contraction_stable disjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       disjc_tableau_rule_def disjc_tableau_rule_indiv_def)
apply (erule contraction_stable_lift_to_tableau_rule)
apply (fastforce simp add: disjc_rule_indiv.simps is_atomic_role_fact_def)
apply (clarsimp simp add: disjc_rule_indiv.simps)
apply (drule fv_form_fv_abox) apply fastforce

apply (clarsimp simp add: disjc_rule_indiv.simps)

apply (drule fv_form_fv_abox)
apply (elim disjE)
apply simp apply (rule neq_complete_not_eq_fact) apply clarsimp+ apply fast apply fastforce
apply simp apply (rule neq_complete_not_eq_fact) apply clarsimp+ apply fast apply fastforce+
done

lemma contraction_stable_choose_tableau_rule:
  "rule_resp_invariant initcond contraction_stable choose_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       choose_tableau_rule_def choose_tableau_rule_indiv_def)
apply (erule contraction_stable_lift_to_tableau_rule)
apply (fastforce simp add: choose_rule_indiv.simps is_atomic_role_fact_def)
apply (clarsimp simp add: choose_rule_indiv.simps)
apply (drule fv_form_fv_abox)+ apply fastforce

apply (clarsimp simp add: choose_rule_indiv.simps)

apply (drule fv_form_fv_abox)+
apply (elim disjE)
apply simp apply (rule neq_complete_not_eq_fact) apply clarsimp+ apply fast apply fastforce
apply simp apply (rule neq_complete_not_eq_fact) apply clarsimp+ apply fast apply fastforce+
done

lemma neq_complete_rename_in_abox: 
    "neq_complete z ab \<Longrightarrow> 
    (x :: 'a :: linorder) < y \<Longrightarrow>
       x \<in> fv_abox ab \<Longrightarrow>
       y \<in> fv_abox ab \<Longrightarrow>   
       neq_complete z (rename_in_abox ab [ISubst y x])"
by (clarsimp simp add: neq_complete_def FactFm_Eq_rename_in_abox_inversion) blast


(* TODO: for proving open goal in Strategies / saturated_rename_numrestrc_ge_aux,
   which however is not essential*)
lemma "neq_complete (rename_in_var x [ISubst v1 v2]) (rename_in_abox ab [ISubst v1 v2]) \<Longrightarrow>
       v2 < v1 \<Longrightarrow>
       neq_complete x ab"
apply (simp add: neq_complete_def FactFm_Eq_rename_in_abox_inversion split : if_split_asm)
sorry (* theorem for Strategies *)

(*
lemma "neq_complete x (abox tab) \<Longrightarrow> (x' :: 'a :: linorder) < x \<Longrightarrow> 
       x' \<in> fv_abox (abox tab) \<Longrightarrow>
       x \<in> fv_abox (abox tab) \<Longrightarrow>   

   varbounds tab x' \<subseteq> varbounds tab x"
apply (simp add: neq_complete_def)
apply (drule_tac x=x' in spec) apply (drule mp) apply simp
apply (drule_tac x=x in spec) apply (drule mp) apply simp
*)

(* TODO: beautify proof *)
lemma contraction_stable_join_varbounds: 
  "bounds_renaming_closed t \<Longrightarrow>
   contraction_stable t \<Longrightarrow>
       x < y \<Longrightarrow>
       x \<in> fv_abox (abox t) \<Longrightarrow>
       y \<in> fv_abox (abox t) \<Longrightarrow>
       contraction_stable
        \<lparr>abox = rename_in_abox (abox t) [ISubst y x],
         varbounds = join_varbounds y x (varbounds t)\<rparr>"
apply (subgoal_tac "x \<noteq> y") prefer 2 apply simp

apply (clarsimp simp add: contraction_stable_def)
apply (simp add: FactFm_AtomR_rename_in_abox_inversion)
apply (simp add: join_varbounds_bounds_renaming_closed)
apply (subgoal_tac "varbounds t y \<subseteq> varbounds t x") 
  prefer 2 apply (simp add: bounds_renaming_closed_def)

apply (elim disjE)

apply (intro conjI impI)
apply simp_all
apply (elim conjE)
apply (subgoal_tac "\<not> neq_complete ya (abox t)") 
  prefer 2 apply (fastforce dest:  neq_complete_rename_in_abox)
apply blast
apply (subgoal_tac "\<not> neq_complete ya (abox t)") 
  prefer 2 apply (fastforce dest:  neq_complete_rename_in_abox)
apply blast
apply (subgoal_tac "\<not> neq_complete x (abox t)") 
  prefer 2 apply (fastforce dest:  neq_complete_rename_in_abox)

apply (intro impI)
apply (case_tac "neq_complete y (abox t)") apply (fast dest: neq_complete_mono)
apply (drule_tac x=r in spec)
apply (drule_tac x=y in spec)
apply (drule mp, fast)
apply simp
apply (drule_tac x=xa in spec)
apply (drule mp, simp)
apply (drule mp, simp)
apply fast

apply (intro conjI impI)
apply simp_all
apply (elim conjE)
apply (subgoal_tac "\<not> neq_complete ya (abox t)") 
  prefer 2 apply (fastforce dest:  neq_complete_rename_in_abox)
apply blast
apply (subgoal_tac "\<not> neq_complete ya (abox t)") 
  prefer 2 apply (fastforce dest:  neq_complete_rename_in_abox)
apply blast
apply (subgoal_tac "\<not> neq_complete x (abox t)") 
  prefer 2 apply (fastforce dest:  neq_complete_rename_in_abox)


apply (intro impI)
apply (case_tac "neq_complete y (abox t)") apply (fast dest: neq_complete_mono)
apply (drule_tac x=r in spec)
apply (drule_tac x=y in spec)
apply (drule mp, fast)
apply simp
apply (drule_tac x=xa in spec)
apply (drule mp, simp)
apply (drule mp, simp)
apply fast
done

lemma contraction_stable_eq_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_renaming_closed t \<Longrightarrow> 
   rule_resp_invariant initcond contraction_stable eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       eq_tableau_rule_def eq_tableau_rule_indiv.simps)
apply (rename_tac x y)
apply (subgoal_tac "x \<in> fv_abox (abox t) \<and> y \<in> fv_abox (abox t)")
prefer 2 apply (fastforce simp add: eq_applicable.simps dest: fv_form_fv_abox)
apply (case_tac "x < y")
apply (clarsimp simp add: contraction_stable_join_varbounds)+
done


lemma contraction_stable_numrestrc_lt_tableau_rule:
  "\<forall> t. initcond t \<longrightarrow> bounds_renaming_closed t \<Longrightarrow> 
   rule_resp_invariant initcond contraction_stable numrestrc_lt_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
      numrestrc_lt_tableau_rule_def numrestrc_lt_tableau_rule_indiv.simps)
apply (rename_tac t S x r c y1 y2)
apply (subgoal_tac "FactFm (Inst y1 c) \<in> abox t")  prefer 2 apply simp
apply (subgoal_tac "FactFm (Inst y2 c) \<in> abox t")  prefer 2 apply simp
apply (subgoal_tac "y1 \<in> fv_abox (abox t) \<and> y2 \<in> fv_abox (abox t)")
prefer 2 apply (fastforce simp add: eq_applicable.simps dest: fv_form_fv_abox)
apply (clarsimp simp add: contraction_stable_join_varbounds)
done

lemma FactFm_AtomR_numrestrc_ge_rule_facts:
  "(FactFm (AtomR True r' y y') \<in> numrestrc_ge_rule_facts c r x Y) = 
       (r' = r \<and> y = x \<and> y' \<in> Y)"
by (simp add: numrestrc_ge_rule_facts_def)

lemma neq_complete_numrestrc_ge_rule_facts_same:
   "Y \<noteq> {} \<Longrightarrow> 
       (x :: 'a :: linorder) \<notin> Y \<Longrightarrow>
       x \<in> fv_abox (abox t) \<Longrightarrow>
       \<forall> y \<in> Y. x < y \<Longrightarrow>
       fv_concept c \<subseteq> fv_abox (abox t) \<Longrightarrow>
       neq_complete x (abox t) \<Longrightarrow>
       neq_complete x (numrestrc_ge_rule_facts c r x Y \<union> abox t)"
apply (clarsimp simp add: neq_complete_def FactFm_Eq_numrestrc_ge_rule_facts)
apply (intro conjI impI)
apply simp_all
apply fastforce+
done

(* TODO: move elsewhere *)
lemma fresh_set_incr_fv_abox: "fresh_set_incr Y ab \<Longrightarrow> y \<notin> (Y \<inter> fv_abox ab)"
by (fastforce simp add: fresh_set_incr_def)

lemma neq_complete_numrestrc_ge_rule_facts_other:
      "Y \<noteq> {} \<Longrightarrow> 
       (x :: 'a :: linorder) \<in> fv_abox (abox t) \<Longrightarrow>
       y \<in> fv_abox (abox t) \<Longrightarrow>
       fv_concept c \<subseteq> fv_abox (abox t) \<Longrightarrow>
       fresh_set_incr Y (abox t) \<Longrightarrow> 
       neq_complete y (abox t) \<Longrightarrow>
       neq_complete y (numrestrc_ge_rule_facts c r x Y \<union> abox t)"
apply (subgoal_tac "x \<notin> Y") prefer 2 apply (fast dest: fresh_set_incr_fv_abox)
apply (subgoal_tac "y \<notin> Y") prefer 2 apply (fast dest: fresh_set_incr_fv_abox)
apply (subgoal_tac "\<forall> z \<in> Y. x < z") prefer 2 apply (simp add: fresh_set_incr_def)
apply (subgoal_tac "\<forall> z \<in> Y. y < z") prefer 2 apply (simp add: fresh_set_incr_def)
apply (clarsimp simp add: neq_complete_def FactFm_Eq_numrestrc_ge_rule_facts)
apply (subgoal_tac "\<forall> y' \<in> Y. \<forall> v. FactFm (Eq False v y') \<notin> abox t")
  prefer 2 apply (simp add: in_fresh_set_incr_notin_abox) 
apply (subgoal_tac "\<forall> y' \<in> Y. \<forall> v. FactFm (Eq False y' v) \<notin> abox t")
  prefer 2 apply (simp add: in_fresh_set_incr_notin_abox) 

apply simp_all
apply (intro conjI impI)
apply fastforce+
done


lemma "fresh_set_incr Y ab \<Longrightarrow> x \<in> fv_abox ab \<Longrightarrow> \<forall>y\<in>Y. x < y"
by (simp add: fresh_set_incr_def)


lemma contraction_stable_numrestrc_ge_tableau_rule:
  "rule_resp_invariant initcond contraction_stable numrestrc_ge_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
      numrestrc_ge_tableau_rule_def numrestrc_ge_tableau_rule_indiv.simps)
(*apply (subgoal_tac "neq_complete x (abox t)")*)
apply (subgoal_tac "x \<in> fv_abox (abox t)") 
   prefer 2 apply (fastforce dest: fv_form_fv_abox) 
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
apply (clarsimp simp add: contraction_stable_def)
apply (intro conjI allI impI)

(* case 1 *)
apply (simp add: FactFm_AtomR_numrestrc_ge_rule_facts)
apply (fastforce simp add: fresh_set_def dest: fresh_set_incr_fresh_set)

(* case 2 *)
apply (fastforce simp add: fresh_set_def  dest: fresh_set_incr_fresh_set fv_form_fv_abox)

(* case 3 *)
apply (simp add: FactFm_AtomR_numrestrc_ge_rule_facts)
apply (rule disjI1)
apply (rule neq_complete_numrestrc_ge_rule_facts_same) 
  apply assumption+
  apply (simp add: fresh_set_incr_def)
  apply (fastforce dest: fv_form_fv_abox)
  apply assumption

(* case 4 *)
apply (case_tac "y = x")
(* case y = x *)
apply simp
apply (rule disjI1)
apply (rule neq_complete_numrestrc_ge_rule_facts_same) 
  apply assumption+
  apply (simp add: fresh_set_incr_def)
  apply (fastforce dest: fv_form_fv_abox)
  apply assumption
(* case y \<noteq> x *)
apply (subgoal_tac "x \<notin> Y") 
   prefer 2 apply (fastforce simp add: fresh_set_def dest: fresh_set_incr_fresh_set)
apply (rename_tac t x r c Y r' y y')
apply (drule_tac x=r' in spec)
apply (drule_tac x=y in spec)
apply (drule mp, fast)
apply (subgoal_tac "y \<in> fv_abox (abox t)") prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (elim disjE)

(* case neq_complete y (abox t) *)
apply (rule disjI1)
apply (rule neq_complete_numrestrc_ge_rule_facts_other) apply simp_all
apply (fastforce dest: fv_form_fv_abox)

(* case \<forall>x<y. x \<in> fv_abox (abox t) \<longrightarrow> varbounds t x \<subseteq> varbounds t y *)
apply (rule disjI2)
apply (subgoal_tac "\<forall> z \<in> Y. y < z") prefer 2 apply (simp add: fresh_set_incr_def) 
apply (intro allI impI conjI)
apply fastforce
apply fastforce
apply fastforce
apply (fastforce dest: fv_form_fv_abox)
done

(*--- invariant preservation for tableau rules ---*)


lemma bounds_renaming_closed_lift_to_tableau_rule [rule_format]:
      "lift_to_tableau_rule rl_indiv t t' \<Longrightarrow>
       \<forall> ab ab'. rl_indiv ab ab' \<longrightarrow> fv_abox ab' \<subseteq> fv_abox ab \<Longrightarrow>
       bounds_renaming_closed t \<Longrightarrow> bounds_renaming_closed t'"
by (fastforce simp add: lift_to_tableau_rule_def bounds_renaming_closed_def)

lemma bounds_renaming_closed_conjc_tableau_rule: 
    "rule_resp_invariant initcond bounds_renaming_closed conjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       conjc_tableau_rule_def conjc_tableau_rule_indiv_def)
apply (erule bounds_renaming_closed_lift_to_tableau_rule)
apply (fastforce simp add: conjc_rule_indiv.simps dest: fv_form_fv_abox)
apply assumption
done

lemma bounds_renaming_closed_disjc_tableau_rule: 
    "rule_resp_invariant initcond bounds_renaming_closed disjc_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       disjc_tableau_rule_def disjc_tableau_rule_indiv_def)
apply (erule bounds_renaming_closed_lift_to_tableau_rule)
apply (fastforce simp add: disjc_rule_indiv.simps dest: fv_form_fv_abox)
apply assumption
done

lemma bounds_renaming_closed_choose_tableau_rule: 
    "rule_resp_invariant initcond bounds_renaming_closed choose_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       choose_tableau_rule_def choose_tableau_rule_indiv_def)
apply (erule bounds_renaming_closed_lift_to_tableau_rule)
apply (fastforce simp add: choose_rule_indiv.simps dest: fv_form_fv_abox)
apply assumption
done

lemma bounds_renaming_closed_renaming:
    "bounds_renaming_closed t \<Longrightarrow>
       x < y \<Longrightarrow>
       x \<in> fv_tableau t \<Longrightarrow>
       y \<in> fv_tableau t \<Longrightarrow>
       bounds_renaming_closed
        \<lparr>abox = rename_in_abox (abox t) [ISubst y x],
           varbounds = join_varbounds y x (varbounds t)\<rparr>"
apply (clarsimp simp add: bounds_renaming_closed_def join_varbounds_def)
apply fast
done

lemma bounds_renaming_closed_eq_tableau_rule: 
    "rule_resp_invariant initcond bounds_renaming_closed eq_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       eq_tableau_rule_def eq_tableau_rule_indiv.simps)
apply (rename_tac t t' x y)
apply (subgoal_tac "x \<in> fv_tableau t \<and> y \<in> fv_tableau t")
   prefer 2 apply (clarsimp simp add: eq_applicable.simps) apply (fastforce dest: fv_form_fv_abox)
apply (case_tac "x < y")
apply clarsimp
apply (rule bounds_renaming_closed_renaming, simp_all)
apply clarsimp
apply (rule bounds_renaming_closed_renaming, simp_all)
done

lemma bounds_renaming_closed_numrestrc_lt_tableau_rule: 
    "rule_resp_invariant initcond bounds_renaming_closed numrestrc_lt_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_lt_tableau_rule_def numrestrc_lt_tableau_rule_indiv.simps)
apply (rename_tac t S x r c y1 y2)
apply (subgoal_tac "y1 \<in> fv_tableau t \<and> y2 \<in> fv_tableau t")
   prefer 2 
   apply (subgoal_tac "FactFm (Inst y1 c) \<in> abox t \<and> FactFm (Inst y2 c) \<in> abox t")
      prefer 2 apply clarsimp 
   apply (fastforce dest: fv_form_fv_abox)
apply clarsimp
apply (rule bounds_renaming_closed_renaming, simp_all)
done


lemma fresh_set_incr_in_fv_tableau_rewr:
"fresh_set_incr Y (abox t) \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<in> fv_tableau t \<Longrightarrow> (y < x) = False"
by (fastforce simp add: fresh_set_incr_def)

lemma fresh_set_incr_in_fv_concept_rewr:
"fresh_set_incr Y (abox t) \<Longrightarrow> y \<in> Y \<Longrightarrow> v \<in> fv_concept c 
  \<Longrightarrow> fv_concept c \<subseteq> fv_tableau t \<Longrightarrow> (y < v) = False"
by (fastforce simp add: fresh_set_incr_def)

lemma fresh_set_incr_same_in_fv_tableau_rewr:
"fresh_set_incr Y (abox t) \<Longrightarrow> y \<in> Y \<Longrightarrow> (y \<in> fv_tableau t) = False"
by (fastforce simp add: fresh_set_incr_def)

lemma fresh_set_incr_same_in_fv_concept_rewr:
"fresh_set_incr Y (abox t) \<Longrightarrow> y \<in> Y 
  \<Longrightarrow> fv_concept c \<subseteq> fv_tableau t \<Longrightarrow> (y \<in> fv_concept c) = False" 
by (fastforce simp add: fresh_set_incr_def)

         
lemma successor_varbounds_containment_for_expansion_stable:
      "expansion_stable t \<Longrightarrow>
       bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
       bounds_renaming_closed t \<Longrightarrow>
       \<not> numrestrc_ge_blocked (abox t) x (card Y) r c \<Longrightarrow>
       x \<in> fv_tableau t \<Longrightarrow>
       x' \<in> fv_tableau t \<Longrightarrow>
       successor_varbounds r (varbounds t x) \<subseteq> varbounds t x'"
apply (case_tac "x' < x")
apply (subgoal_tac "varbounds t x \<subseteq> varbounds t x' ") 
  prefer 2 apply (simp add: bounds_renaming_closed_def)
apply (subgoal_tac "successor_varbounds r (varbounds t x) \<subseteq> varbounds t x")
   prefer 2 apply (fast dest: successor_varbounds_inclusion)
apply fast
apply (case_tac "x' = x")
apply simp
apply (fast dest: successor_varbounds_inclusion)

apply (subgoal_tac "x < x'") prefer 2 apply simp
apply (subgoal_tac "varbounds t x' \<subseteq> varbounds t x ") prefer 2 apply (simp add: bounds_renaming_closed_def)

apply (subgoal_tac "\<not> numrestrc_ge_complete x (abox t)") 
   prefer 2 apply (fastforce simp add: numrestrc_ge_complete_def)
apply (subgoal_tac "varbounds t x' = varbounds t x ") prefer 2 apply (fastforce simp add: expansion_stable_def) 
apply simp
apply (fast dest: successor_varbounds_inclusion)
done

lemma bounds_renaming_closed_numrestrc_ge_tableau_rule: 
    "\<forall> t. initcond t \<longrightarrow> expansion_stable t \<Longrightarrow> 
     \<forall> t. initcond t \<longrightarrow> bounds_subset_closed_pn (varbounds t) \<Longrightarrow>
rule_resp_invariant initcond bounds_renaming_closed numrestrc_ge_tableau_rule"
apply (clarsimp simp add: rule_resp_invariant_def  ex_rule_closure_def 
       numrestrc_ge_tableau_rule_def numrestrc_ge_tableau_rule_indiv.simps)
apply (simp add: numrestrc_ge_successor_varbounds_old_def)
apply (subgoal_tac "x \<in> fv_tableau t") prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (subgoal_tac "fv_concept c \<subseteq> fv_tableau t") prefer 2 apply (fastforce dest: fv_form_fv_abox)
apply (simp (no_asm_simp) add: bounds_renaming_closed_def)
apply (intro conjI impI allI)
apply simp_all
apply (simp_all add: fresh_set_incr_same_in_fv_concept_rewr)
apply (simp_all add: fresh_set_incr_same_in_fv_tableau_rewr)
apply (simp_all add: fresh_set_incr_in_fv_tableau_rewr)
apply (simp_all add: fresh_set_incr_in_fv_concept_rewr)

apply (fast dest: successor_varbounds_inclusion)
apply (rule successor_varbounds_containment_for_expansion_stable, simp_all) 
   apply (fastforce dest: fv_form_fv_abox)
apply (rule successor_varbounds_containment_for_expansion_stable, simp_all) 

apply (simp add: bounds_renaming_closed_def) apply fast
apply (simp add: bounds_renaming_closed_def)
apply (simp add: bounds_renaming_closed_def)

apply (rename_tac t x r c Y x' y)
apply (subgoal_tac "x' \<in> fv_tableau t") apply fast apply (fastforce dest: fv_form_fv_abox)

apply (simp add: bounds_renaming_closed_def) 
apply (rename_tac t x r c Y x' y)
apply (subgoal_tac "x' \<in> fv_tableau t") apply fast apply (fastforce dest: fv_form_fv_abox)

apply (simp add: bounds_renaming_closed_def) apply fast

apply (simp add: bounds_renaming_closed_def) 

apply (simp add: bounds_renaming_closed_def)
apply (rename_tac t x r c Y x' y)
apply (subgoal_tac "x' \<in> fv_tableau t") apply fast apply (fastforce dest: fv_form_fv_abox)

apply (simp add: bounds_renaming_closed_def)
done

lemma subst_free_abox_conjc_tableau_rule: 
   "rule_resp_invariant initcond (\<lambda>t. subst_free_abox (abox t)) conjc_tableau_rule"
sorry

lemma rule_resp_invariant_tableau_invariant_conjc_tableau_rule [simp]:
   "rule_resp_invariant initcond tableau_invariant conjc_tableau_rule"
apply (simp add: tableau_invariant_def)
apply (intro rule_resp_invariant_conj_invar conjI)
apply (rule successor_varbounds_closed_conjc_tableau_rule)
apply (fast intro: deco_respecting_bounds_conjc_tableau_rule)
apply (rule bounds_renaming_closed_conjc_tableau_rule)
apply (rule bounds_subset_closed_conjc_tableau_rule)
apply (rule subst_free_abox_conjc_tableau_rule)
apply (rule finite_varbounds_conjc_tableau_rule)
apply (rule finite_abox_conjc_tableau_rule)
done

lemma rule_resp_invariant_tableau_invariant_disjc_tableau_rule [simp]: 
   "rule_resp_invariant initcond tableau_invariant disjc_tableau_rule"
sorry (* invariant individual rule *)
lemma rule_resp_invariant_tableau_invariant_eq_tableau_rule [simp]: 
   "rule_resp_invariant initcond tableau_invariant eq_tableau_rule"
sorry (* invariant individual rule *)
lemma rule_resp_invariant_tableau_invariant_eq_compl_tableau_rule [simp]: 
   "rule_resp_invariant initcond tableau_invariant eq_compl_tableau_rule"
sorry (* invariant individual rule *)

lemma rule_resp_invariant_tableau_invariant_choose_tableau_rule [simp]: 
   "rule_resp_invariant initcond tableau_invariant choose_tableau_rule"
sorry (* invariant individual rule *)
lemma rule_resp_invariant_tableau_invariant_numrestrc_ge_tableau_rule [simp]: 
   "rule_resp_invariant initcond tableau_invariant numrestrc_ge_tableau_rule"
sorry (* invariant individual rule *)
lemma rule_resp_invariant_tableau_invariant_numrestrc_lt_tableau_rule [simp]: 
   "rule_resp_invariant initcond tableau_invariant numrestrc_lt_tableau_rule"
sorry (* invariant individual rule *)


lemma rule_resp_invariant_tableau_invariant_concept_tableau_rule: 
   "rule_resp_invariant (\<lambda> a. True) tableau_invariant concept_tableau_rule"
by (simp add: concept_tableau_rule_def set_concept_tableau_rules_def rule_resp_invariant_disj_rule)


lemma tableau_invariant_in_reach:
  "tab \<in> reach concept_tableau_rule (initial_tableau ab) \<Longrightarrow> tableau_invariant tab"
apply (rule invariant_in_reach [where invar = tableau_invariant and init = "(initial_tableau ab)"])
apply (rule tableau_invariant_initial)
apply (rule rule_resp_invariant_tableau_invariant_concept_tableau_rule)
apply assumption
done


lemma tableau_potential_decreases_using_potential_ord_reach: 
      "concept_tableau_rule tab tab' \<Longrightarrow>
      tab \<in> reach concept_tableau_rule (initial_tableau ab) \<Longrightarrow>
      \<not> contains_clash (abox tab) \<Longrightarrow>
      \<not> contains_clash (abox tab') \<Longrightarrow>
       (tableau_potential tab', tableau_potential tab) \<in> tableau_potential_ord"
apply (subgoal_tac "tab'\<in> reach concept_tableau_rule (initial_tableau ab)")
   prefer 2 apply (simp add: reach_def)
apply (frule tableau_invariant_in_reach [where tab=tab])
apply (frule tableau_invariant_in_reach [where tab=tab'])
apply (simp add: concept_tableau_rule_def set_concept_tableau_rules_def alternative_rule_of_set_def)
apply (elim disjE)
(* conjc *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_conjc_tableau_rule 
  simp add: tableau_invariant_def)
(* disjc *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_disjc_tableau_rule 
  simp add: tableau_invariant_def)
(* eq *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_eq_tableau_rule
  simp add: tableau_invariant_def)+
(* eq_compl *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_eq_compl_tableau_rule
  simp add: tableau_invariant_def)+
(* choose *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_choose_tableau_rule
  simp add: tableau_invariant_def)+
(* numrestrc_ge *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_numrestrc_ge_tableau_rule
  simp add: tableau_invariant_def)+
(* numrestrc_lt *)
apply (fastforce elim: tableau_potential_decreases_using_potential_ord_for_numrestrc_lt_tableau_rule
  simp add: tableau_invariant_def)+
done

(* --- non-triviality of tableau after rule application ---*)

lemma conjc_tableau_rule_applic_nontrivial:
 "conjc_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  conjc_tableau_rule_def ex_rule_closure_def 
  conjc_tableau_rule_indiv_def lift_to_tableau_rule_def 
  conjc_rule_indiv.simps is_nontrivial_tableau_def)
apply (fastforce dest: fv_form_fv_abox)
done

lemma disjc_tableau_rule_applic_nontrivial:
 "disjc_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  disjc_tableau_rule_def ex_rule_closure_def 
  disjc_tableau_rule_indiv_def lift_to_tableau_rule_def 
  disjc_rule_indiv.simps is_nontrivial_tableau_def)
apply (fastforce dest: fv_form_fv_abox)
done

lemma eq_tableau_rule_applic_nontrivial:
 "eq_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  eq_tableau_rule_def ex_rule_closure_def 
  eq_tableau_rule_indiv.simps
  eq_rule_indiv.simps is_nontrivial_tableau_def)
apply (fastforce dest: fv_form_fv_abox)
done

lemma eq_compl_tableau_rule_applic_nontrivial:
 "eq_compl_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  eq_compl_tableau_rule.simps ex_rule_closure_def 
  eq_tableau_rule_indiv.simps
  eq_rule_indiv.simps is_nontrivial_tableau_def)
done

lemma choose_tableau_rule_applic_nontrivial:
 "choose_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  choose_tableau_rule_def ex_rule_closure_def 
  choose_tableau_rule_indiv_def lift_to_tableau_rule_def   
  choose_rule_indiv.simps is_nontrivial_tableau_def)
apply (fastforce dest: fv_form_fv_abox)
done

lemma numrestrc_ge_tableau_rule_applic_nontrivial:
 "numrestrc_ge_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  numrestrc_ge_tableau_rule_def ex_rule_closure_def  
  numrestrc_ge_tableau_rule_indiv.simps
  is_nontrivial_tableau_def)
apply (fastforce dest: fv_form_fv_abox)
done

lemma numrestrc_lt_tableau_rule_applic_nontrivial:
 "numrestrc_lt_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (clarsimp simp add: 
  numrestrc_lt_tableau_rule_def ex_rule_closure_def  
  numrestrc_lt_tableau_rule_indiv.simps
  is_nontrivial_tableau_def)
apply (fastforce dest: fv_form_fv_abox)
done

lemma concept_tableau_rule_applic_nontrivial:
 "concept_tableau_rule tab tab' \<Longrightarrow> is_nontrivial_tableau tab"
apply (simp add: concept_tableau_rule_def set_concept_tableau_rules_def alternative_rule_of_set_def)
apply (elim disjE)
apply (simp add: conjc_tableau_rule_applic_nontrivial)
apply (simp add: disjc_tableau_rule_applic_nontrivial)
apply (simp add: eq_tableau_rule_applic_nontrivial)
apply (simp add: eq_compl_tableau_rule_applic_nontrivial)
apply (simp add: choose_tableau_rule_applic_nontrivial)
apply (simp add: numrestrc_ge_tableau_rule_applic_nontrivial)
apply (simp add: numrestrc_lt_tableau_rule_applic_nontrivial)
done


lemma finite_in_reach_concept_tableau_rule:
  "tab \<in> reach concept_tableau_rule (initial_tableau ab) \<Longrightarrow> finite (fv_tableau tab)"
  sorry
  
lemma wf_tableau_using_potential_ord_reach: "wf {(pot', pot). 
   \<exists> tab tab'. pot = tableau_potential tab \<and> pot' = tableau_potential tab' 
   \<and> \<not> contains_clash (abox tab) 
   \<and> concept_tableau_rule tab tab'
   \<and> tab \<in> reach concept_tableau_rule (initial_tableau ab)
   }"
apply (rule  wf_tableau_potential_ord [THEN wf_subset])
apply clarsimp
apply (frule finite_in_reach_concept_tableau_rule)
apply (frule concept_tableau_rule_applic_nontrivial)

apply (case_tac "contains_clash (abox tab')")

apply (subgoal_tac "tableau_potential tab' = {#}") 
    prefer 2 apply (simp add: tableau_potential_def)
apply (subgoal_tac "tableau_potential tab \<noteq> {#}") 
    prefer 2 apply (rule tableau_potential_clash_free_nontrivial, assumption+)
apply (simp add: tableau_potential_def tableau_potential_ord_def mult_empty_less)

apply (rule tableau_potential_decreases_using_potential_ord_reach, assumption+)
done



lemma "wf {(tab', tab). 
        \<not> contains_clash (abox tab)
        \<and> concept_tableau_rule tab tab'
        \<and> tab \<in> reach concept_tableau_rule (initial_tableau ab) }"
apply (rule wf_tableau_using_potential_ord_reach [THEN wf_inv_image [THEN wf_subset, where f1=tableau_potential]])
apply (fastforce simp add: inv_image_def)
done


(*

apply (subgoal_tac "{(tab', tab). concept_tableau_rule tab tab' \<and> \<not> contains_clash (abox tab)} \<subseteq> 
  (inv_image 
  {(pot', pot). 
     \<exists> tab tab'. pot = tableau_potential tab \<and> pot' = tableau_potential tab' 
     \<and> concept_tableau_rule tab tab' \<and> \<not> contains_clash (abox tab)} 
     tableau_potential)")

apply (rule wf_subset)
prefer 2 apply assumption
apply (rule wf_inv_image)
apply (rule wf_tableau_potential)

apply (fastforce simp add: inv_image_def)
*)


end
