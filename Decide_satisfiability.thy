(*<*)
theory Decide_satisfiability  imports ALC_CompletenessProofs New_Var 
begin
(*>*)

section {* Model construction *}

lemma not_satisfiable1: " f \<in> ab \<Longrightarrow> \<forall>i:: ('d, 'nr, 'nc, 'ni) Interp. \<not> interp_form f i 
  \<Longrightarrow> \<not> satisfiable TYPE('d) ab"
by (fastforce simp add: satisfiable_def)

lemma not_satisfiable2: "f1 \<in> ab \<and> f2 \<in> ab 
\<Longrightarrow> \<forall>i:: ('d, 'nr, 'nc, 'ni) Interp. well_formed_interp i  \<longrightarrow> interp_form f1 i = (\<not> interp_form f2 i) 
\<Longrightarrow> \<not> satisfiable TYPE('d) ab"
by (fastforce simp add: satisfiable_def)


lemma  interp_form_FactFm_lt_Suc:
"well_formed_interp i \<Longrightarrow> 
  interp_form (FactFm (Inst x ([<] (Suc n) r c))) i = 
  card_lt {y. (interp_i i x, y) \<in> interp_r i r \<and> y \<in> interp_concept c i} (Suc n)"
by ( clarsimp simp add: card_lt_Range_rel_restrict)

lemma classic_numb: "
interp_form  (FactFm (Inst x ([<] (Suc n) r c))) i \<Longrightarrow>
well_formed_interp i \<Longrightarrow> 
   (finite {y. (interp_i i x, y) \<in> interp_r i r \<and> y \<in> interp_concept c i} \<and>
     card {y. (interp_i i x, y) \<in> interp_r i r \<and> y \<in> interp_concept c i} < Suc n)"
     by (simp only: card_lt_def interp_form_FactFm_lt_Suc)


lemma contains_atmost_clash_not_satsfiable[simp]: 
"contains_atmost_clash ab \<Longrightarrow> \<not> satisfiable TYPE('d) ab"
  apply (clarsimp simp add: contains_atmost_clash_def)
  apply (clarsimp simp add: satisfiable_def)

  apply (subgoal_tac " \<forall>z z2. z\<in> S \<and> z2\<in> S \<and> z \<noteq> z2 
         \<longrightarrow> interp_i i z \<noteq> interp_i i z2 ")
     prefer 2 apply (fastforce simp add:  mutually_uneq_def) (* Note: takes time *)

 apply (subgoal_tac "inj_on (interp_i i) S")
     prefer 2  apply (simp add: inj_on_def) apply blast

  apply (subgoal_tac "interp_i i ` S \<subseteq> 
                    (Range  (rel_restrict (interp_r i r) {interp_i i x} (interp_concept c i)))")
     prefer 2
     apply (clarsimp simp add: image_def R_succs_def)
     apply (rename_tac x r c n S i y)
     apply (subgoal_tac "interp_form (FactFm (AtomR True r x y)) i") prefer 2 apply blast
     apply (subgoal_tac "interp_form (FactFm (Inst y c)) i") prefer 2 apply blast
     apply (fastforce simp add: rel_restrict_def) 

  apply (frule_tac x="FactFm (Inst x ([<] n r c))" in bspec, assumption)
  apply (simp add: card_lt_def)
  apply (subgoal_tac "card( (interp_i i) `  S) \<le> card (Range
          (rel_restrict (interp_r i r) {interp_i i x}
            (interp_concept c i)))")
     prefer 2 apply (blast intro: card_mono) 
  apply (subgoal_tac "card (interp_i i ` S) = card S")
         prefer 2 apply (simp only: card_image)
  apply arith
done

lemma contains_clash_not_satisfiable: "contains_clash ab \<Longrightarrow> \<not> satisfiable TYPE('d) ab"
  apply (simp add: contains_clash_def)
  apply (elim disjE exE)
  apply (simp_all add: not_satisfiable1 not_satisfiable2)
done

lemma  satisfiable_not_contains_clash: "satisfiable TYPE('d) ab \<Longrightarrow> \<not> contains_clash ab "
  by (fastforce simp add: contains_clash_not_satisfiable)
  

lemma saturated_alc_rule: 
   "saturated_abox ab alc_rule = (Ball set_alc_rules (saturated_abox ab))"
by (fastforce simp add: saturated_abox_def alc_rule_def set_alc_rules_def alternative_rule_of_set_def)

lemma saturated_and: 
"saturated_abox ab alc_rule \<Longrightarrow> FactFm (Inst x (ConjC c1 c2)) \<in> ab 
\<Longrightarrow> FactFm (Inst x c1) \<in> ab \<and> FactFm (Inst x c2) \<in> ab"
apply (drule_tac saturated_abox_alc_ruleD [where r=conjc_rule]) apply (simp add: set_alc_rules_def)
 apply (clarsimp simp add: saturated_abox_def 
   conjc_rule_def ex_rule_closure_def conjc_rule_indiv.simps conjc_applicable.simps)
 apply( drule spec)+ 
 apply (drule_tac mp)
 apply fastforce
 apply blast
done


lemma saturated_or: "saturated_abox ab alc_rule \<Longrightarrow> FactFm (Inst x (DisjC c1 c2)) \<in> ab 
\<Longrightarrow> FactFm (Inst x c1) \<in> ab \<or> FactFm (Inst x c2) \<in> ab"
apply (drule_tac saturated_abox_alc_ruleD [where r=disjc_rule]) apply (simp add: set_alc_rules_def) 
 apply (clarsimp simp add: saturated_abox_def 
   disjc_rule_def ex_rule_closure_def disjc_rule_indiv.simps  disjc_applicable.simps)
  apply(drule spec)+ 
  apply (drule_tac mp)
  apply fastforce
  apply blast
done


lemma  saturated_all:
"FactFm (Inst x (AllC r c)) \<in> ab \<Longrightarrow>
    saturated_abox ab alc_rule \<Longrightarrow> 
    \<forall>y. FactFm (AtomR True r x y) \<in> ab \<longrightarrow> FactFm (Inst y c) \<in> ab"
apply (drule_tac saturated_abox_alc_ruleD [where r=allc_rule]) apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def 
    allc_rule_def ex_rule_closure_def allc_rule_indiv.simps  allc_applicable.simps)
  apply (drule_tac x="{f . (\<exists> y. (f = (FactFm (Inst y c))) \<and> FactFm (AtomR True r x y) \<in> ab)} \<union> ab" in  spec)
  apply fastforce
  done

definition gen_next_varname :: " ('nr, 'nc, ('ni::new_var_set_class)) abox \<Rightarrow> 'ni \<Rightarrow> 'ni" where
  "gen_next_varname ab vn = (new_var_set (fv_abox ab) vn)"

definition gen_next_incr_varname :: " ('nr, 'nc, ('ni::new_var_set_incr_class)) abox \<Rightarrow> 'ni \<Rightarrow> 'ni" where
  "gen_next_incr_varname ab vn = (new_var_set_incr (fv_abox ab) vn)"
    
definition gen_set_varname :: "nat\<Rightarrow> ('nr, 'nc, ('ni::new_var_set_class)) abox \<Rightarrow> 'ni \<Rightarrow> 'ni set" where
  "gen_set_varname n ab vn = (new_vars_set n (fv_abox ab) vn)"

definition gen_set_incr_varname :: 
     "nat\<Rightarrow> ('nr, 'nc, ('ni::new_var_set_incr_class)) abox \<Rightarrow> 'ni \<Rightarrow> 'ni set" where
  "gen_set_incr_varname n ab vn = (new_vars_set_incr n (fv_abox ab) vn)"


lemma gen_next_varname_notin_fv_ab [simp]: "finite ab \<Longrightarrow> gen_next_varname ab vn \<notin> fv_abox ab"
  apply (simp add: gen_next_varname_def)
  apply (rule new_var_gen_set)
  apply simp
 done

lemma gen_next_incr_varname_notin_fv_ab [simp]: 
  "finite ab \<Longrightarrow> gen_next_incr_varname ab vn \<notin> fv_abox ab"
  apply (simp add: gen_next_incr_varname_def)
  apply (subgoal_tac "\<forall> v\<in> fv_abox ab. v < new_var_set_incr (fv_abox ab) vn")
  apply fast
  apply clarsimp
  apply (rule new_var_gen_set_incr)
  apply simp
 done

lemma new_vars_set_notin_set: "finite S \<Longrightarrow> new_vars_set n S x \<inter> S = {}"
  apply (induct n arbitrary: S)
  apply simp
  apply (simp add: gen_set_varname_def)
  apply (clarsimp simp add: Let_def)
  apply (intro conjI)
  apply (metis new_var_gen_set)
by (metis finite_insert inf_commute insert_disjoint(2))

lemma new_vars_set_incr_all_greater:
   "finite S \<Longrightarrow> \<forall> s\<in> S. \<forall> v \<in> new_vars_set_incr n S x. s < v"
  apply (induct n arbitrary: S)
  apply (auto simp add: Let_def intro: new_var_gen_set_incr)
done

lemma new_vars_set_incr_notin_set: "finite S \<Longrightarrow> new_vars_set_incr n S x \<inter> S = {}"
by (auto dest: new_vars_set_incr_all_greater [of S n x])

lemma card_new_vars_set: "finite S \<Longrightarrow> card (new_vars_set n S x) = n"
  apply (induct n arbitrary: S)
  apply simp
  apply (clarsimp simp add: Let_def)
by (metis card_Suc_eq  disjoint_insert(1) finite.insertI new_vars_set_notin_set new_vars_set.simps(1))

lemma card_new_vars_set_incr: "finite S \<Longrightarrow> card (new_vars_set_incr n S x) = n"
  apply (induct n arbitrary: S)
  apply simp
  apply (clarsimp simp add: Let_def)
by (metis card_Suc_eq  disjoint_insert(1) finite.insertI 
  new_vars_set_incr_notin_set new_vars_set_incr.simps(1))

lemma  gen_set_varname_notin_fv_abox: "finite ab \<Longrightarrow>  gen_set_varname n ab x \<inter> fv_abox ab = {}"
  by (simp add: gen_set_varname_def new_vars_set_notin_set)

lemma gen_set_incr_varname_notin_fv_abox: "finite ab \<Longrightarrow>  
        gen_set_incr_varname n ab x \<inter> fv_abox ab = {}"
  by (simp add: gen_set_incr_varname_def new_vars_set_incr_notin_set)

lemma card_gen_set_varname [simp]:  "finite ab \<Longrightarrow> card (gen_set_varname n ab x) = n"
  by (simp add: gen_set_varname_def card_new_vars_set)

lemma card_gen_incr_set_varname [simp]:  "finite ab \<Longrightarrow> card (gen_set_incr_varname n ab x) = n"
  by (simp add: gen_set_incr_varname_def card_new_vars_set_incr)

lemma fresh_set_gen_set_varname [simp]: "finite ab \<Longrightarrow>fresh_set (gen_set_varname n  ab x) ab"
by (simp add: fresh_set_def  gen_set_varname_notin_fv_abox)

(*
declare [[show_types = true ]]
declare [[show_sorts = true ]]
*)
lemma fresh_set_gen_set_varname_incr [simp]: 
   "finite ab \<Longrightarrow> fresh_set_incr (gen_set_incr_varname n  ab x) ab"
  apply (simp add: fresh_set_incr_def  gen_set_incr_varname_def)
  apply (rule new_vars_set_incr_all_greater)
  apply simp
done

lemma finite_gen_set_varname [simp]: "finite ab \<Longrightarrow>  finite (gen_set_varname n ab x)"
apply (case_tac n)
apply (simp add: gen_set_varname_def)
apply (rule card_ge_0_finite)
apply simp
done

lemma finite_gen_set_incr_varname [simp]: "finite ab \<Longrightarrow>  finite (gen_set_incr_varname n ab x)"
apply (case_tac n)
apply (simp add: gen_set_incr_varname_def)
apply (rule card_ge_0_finite)
apply simp
done

lemma saturated_some:
  "finite ab \<Longrightarrow> 
   FactFm (Inst (x) (SomeC r c)) \<in> ab \<Longrightarrow>
   saturated_abox ab alc_rule \<Longrightarrow>  
   \<exists> z ::'ni::new_var_set_incr_class  . FactFm (AtomR True r x z) \<in> ab \<and> FactFm (Inst z c) \<in> ab"
apply (drule_tac saturated_abox_alc_ruleD [where r=somec_rule]) apply (simp add: set_alc_rules_def)
    apply (simp add: saturated_abox_def
      somec_rule_def ex_rule_closure_def somec_rule_indiv.simps somec_applicable.simps)
    apply (drule_tac x="insert (FactFm (AtomR True r x (gen_next_incr_varname ab x))) 
                            (insert (FactFm (Inst (gen_next_incr_varname ab x) c)) ab)" in spec)
    apply (drule_tac x="gen_next_incr_varname ab x" in spec)
    apply (drule spec)+ apply (drule mp) apply assumption
    apply simp
done

(* TODO: also might require saturation by rule eq_compl, 
   see lemma saturated_eq_compl_rule_neq_complete below *)
lemma saturated_eq : "FactFm (Eq True x y) \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> x = y"
apply (drule_tac saturated_abox_alc_ruleD [where r=eq_rule]) apply (simp add: set_alc_rules_def)
apply (clarsimp simp add: saturated_abox_def 
    eq_rule_def ex_rule_closure_def eq_rule_indiv.simps  eq_applicable.simps)
apply blast
done

lemma saturated_conj : "ConjFm f1 f2 \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> f1 \<in> ab \<and> f2 \<in> ab "
apply (drule_tac saturated_abox_alc_ruleD [where r=conjfm_rule]) apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def 
    conjfm_rule_def ex_rule_closure_def conjfm_rule_indiv.simps conjfm_applicable.simps)
  apply blast
done

lemma saturated_disj : "DisjFm f1 f2 \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> f1 \<in> ab \<or> f2 \<in> ab "
apply (drule_tac saturated_abox_alc_ruleD [where r=disjfm_rule]) apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def
    disjfm_rule_def ex_rule_closure_def disjfm_rule_indiv.simps disjfm_applicable.simps)
  apply blast
done

lemma finite_abox_finite_inst: "finite ab \<Longrightarrow> finite {z. FactFm (Inst z c) \<in> ab}"
  apply (induct  ab rule:finite.induct, simp_all)
  apply (rename_tac A a)
  apply (case_tac a, simp_all)
  apply clarsimp
  apply (rename_tac A fact)
by (case_tac fact, simp_all)
 
lemma finite_abox_finite_role_fact: "finite ab \<Longrightarrow> finite {z. FactFm (AtomR True nr x z) \<in> ab}"
  apply (induct  ab rule:finite.induct, simp_all)
    apply (rename_tac A a)
  apply (case_tac a, simp_all)
  apply clarsimp
  apply (rename_tac A fact)
by (case_tac fact, simp_all)

lemma finite_abox_finite_R_succs: "finite ab \<Longrightarrow> finite (R_succs r c ab x)"
  by (clarsimp simp add:  finite_abox_finite_inst R_succs_def)

lemma order_linordered_set: "1 < card (S :: ('a::linorder ) set) \<Longrightarrow> \<exists> (y1::'a::linorder) \<in> S. \<exists> y2 \<in> S. y1 < y2"
apply (subgoal_tac "\<exists> s1. s1 \<in> S") apply clarify
apply (subgoal_tac "\<exists> s2. s2 \<in> (S - {s1})") apply (elim exE)
apply (case_tac "s1 < s2")
apply (intro bexI) apply assumption apply blast apply blast
apply (subgoal_tac "s2 < s1")
apply (intro bexI) apply assumption apply blast apply blast
apply (metis member_remove not_less_iff_gr_or_eq remove_def)
apply (metis One_nat_def all_not_in_conv card.insert_remove card_empty card_infinite insert_absorb less_one not_less_iff_gr_or_eq)
apply (metis all_not_in_conv card_empty not_less0)
done

(* The following proof is for the numrestrc_lt_rule_orig variant

lemma saturated_lt_rule: "saturated_abox ab alc_rule \<Longrightarrow> finite ab \<Longrightarrow>
  f \<in> ab \<Longrightarrow>
  f = FactFm (Inst x ([<] n r c)) \<Longrightarrow>
  \<not> (\<exists> S. card S = n  \<and>  1 < n \<and> 
  (\<forall>(y::'c::linorder)\<in>S. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab))"
  apply (drule_tac saturated_abox_alc_ruleD [where r=numrestrc_lt_rule_orig]) apply (simp add: set_alc_rules_def)

  apply (clarsimp simp add: saturated_abox_def numrestrc_lt_rule_orig_def ex_rule_closure_def
    numrestrc_lt_rule_indiv.simps) 

  apply (case_tac "numrestrc_lt_applicable (S, (FactFm (Inst x ([<] n r c)))) ab")
  apply (subgoal_tac "\<exists> y1 \<in> S. \<exists> y2 \<in> S. y1 < y2")
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
  apply (rename_tac S y1 y2)
  apply (drule_tac x="(rename_in_abox ab [ISubst y2 y1])" in  spec)
  apply (drule_tac x=S in spec)
  apply (drule mp, assumption)
  apply (elim disjE)
  apply (drule_tac x=x in spec)
  apply (drule_tac x=r in spec)
  apply (drule_tac x=c in spec)
  apply blast
  apply (drule_tac x=y1 in spec) apply (drule mp, assumption)
  apply (drule_tac x=y2 in spec) apply simp
  
  apply (clarsimp simp add: numrestrc_lt_applicable.simps rename_in_abox_def)
  apply (rule order_linordered_set) apply simp
  
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
done
*)

lemma saturated_lt_rule: "saturated_abox ab alc_rule \<Longrightarrow> finite ab \<Longrightarrow>
  f \<in> ab \<Longrightarrow>
  f = FactFm (Inst x ([<] n r c)) \<Longrightarrow>
  \<not> (\<exists> S. card S = n  \<and>  1 < n \<and> 
  (\<forall>(y::'c::linorder)\<in>S. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab))"
  apply (drule_tac saturated_abox_alc_ruleD [where r=numrestrc_lt_rule]) apply (simp add: set_alc_rules_def)
  apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def numrestrc_lt_rule_def ex_rule_closure_def
    numrestrc_lt_rule_indiv.simps) 
  
  apply (case_tac "numrestrc_lt_applicable (S, (FactFm (Inst x ([<] n r c)))) ab")
  apply (subgoal_tac "\<exists> y1 \<in> S. \<exists> y2 \<in> S. y1 < y2")
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
  apply (rename_tac S y1 y2)
  apply (drule_tac x="rename_in_abox ab [ISubst y2 y1]" in  spec)
  apply (drule_tac x=f in spec) apply simp
  apply (subgoal_tac "(\<forall>ca. c \<noteq> ca) = False") prefer 2 apply blast
  apply simp
  apply (drule_tac x=S in spec) apply simp

  apply (drule_tac x=y1 in spec) apply (drule mp, assumption)
  apply (drule_tac x=y2 in spec) apply simp
  
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
  apply (rule order_linordered_set) apply simp
  
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
done


(*
lemma  saturated_lt_rule: "saturated_abox ab alc_rule \<Longrightarrow> finite ab \<Longrightarrow>
  f \<in> ab \<Longrightarrow>
  f = FactFm (Inst x ([<] n r c)) \<Longrightarrow>
  \<not> (\<exists> S. card S = n  \<and>  1 < n \<and> 
  (\<forall>(y::'c::linorder)\<in>S. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab))"
  apply (drule_tac saturated_abox_alc_ruleD [where r=numrestrc_lt_rule]) apply (simp add: set_alc_rules_def)
  apply simp
  apply (clarsimp simp add: saturated_abox_def numrestrc_lt_rule_def ex_rule_closure_def
    numrestrc_lt_rule_indiv.simps) 
  
  apply (case_tac "numrestrc_lt_applicable (S, (FactFm (Inst x ([<] n r c)))) ab")
  apply (subgoal_tac "\<exists> y1 \<in> S. \<exists> y2 \<in> S. y1 < y2")
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
  apply (rename_tac S y1 y2)
  apply (drule_tac x="insert (FactFm (Eq True y1 y2)) ab" in  spec)
  apply (drule_tac x=S in spec)
  apply (drule mp, assumption)
  apply (elim disjE)
  apply (drule_tac x=x in spec)
  apply (drule_tac x=r in spec)
  apply (drule_tac x=c in spec)
  apply blast
  apply (drule_tac x=y1 in spec) apply (drule mp, assumption)
  apply (drule_tac x=y2 in spec) apply simp
  
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
  apply (rule order_linordered_set) apply simp
  
  apply (clarsimp simp add: numrestrc_lt_applicable.simps)
done
*)

lemma saturated_eq_compl_rule_neq_complete: 
   "saturated_abox ab eq_compl_rule \<Longrightarrow> 
   saturated_abox ab eq_rule \<Longrightarrow> 
   x \<in> fv_abox ab \<Longrightarrow> neq_complete x ab"

apply (simp add: neq_complete_def)
apply (intro impI allI)
apply (rename_tac z1 z2)

apply (case_tac "FactFm (Eq True z1 z2) \<in> ab")
apply (fastforce simp add: saturated_abox_def 
  eq_rule_def ex_rule_closure_def eq_rule_indiv.simps eq_applicable.simps)

apply (case_tac "FactFm (Eq True z2 z1) \<in> ab")
apply (fastforce simp add: saturated_abox_def 
  eq_rule_def ex_rule_closure_def eq_rule_indiv.simps eq_applicable.simps)

apply (case_tac "z1 < z2")
apply (fastforce simp add: saturated_abox_def eq_compl_rule.simps ex_bool_eq)+
done


lemma  saturated_ge_rule: "saturated_abox ab alc_rule \<Longrightarrow> finite ab \<Longrightarrow>
  f \<in> ab \<Longrightarrow>
  f = FactFm (Inst (x::'c::new_var_set_incr_class) ([\<ge>] n r c)) \<Longrightarrow>
  (\<exists> S. finite S \<and> card S = n \<and>
  (\<forall>z\<in>S. FactFm (AtomR True r x z) \<in> ab \<and> FactFm (Inst z c) \<in> ab \<and>
         (FactFm (AtomR True r x z), f) \<in> satis_induct_order_level \<and>
         (FactFm (Inst z c), f) \<in> satis_induct_order_level ) \<and>
  (\<forall>z1\<in>S. \<forall>z2\<in>S.  z1 \<noteq> z2 \<longrightarrow> FactFm (Eq False z1 z2) \<in> ab \<or> FactFm (Eq False z2 z1) \<in> ab))"

apply (subgoal_tac "neq_complete x ab")
  prefer 2 
  apply (frule_tac saturated_abox_alc_ruleD [where r=eq_rule]) apply (simp add: set_alc_rules_def)
  apply (drule_tac saturated_abox_alc_ruleD [where r=eq_compl_rule]) apply (simp add: set_alc_rules_def)
  apply (subgoal_tac "x \<in> fv_abox ab") prefer 2 apply (fastforce dest: fv_form_fv_abox)
  apply (fast intro: saturated_eq_compl_rule_neq_complete)

apply (drule_tac saturated_abox_alc_ruleD [where r=numrestrc_ge_rule]) apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def numrestrc_ge_rule_def ex_rule_closure_def
    numrestrc_ge_rule_indiv.simps) 
  apply (drule_tac x= "numrestrc_ge_rule_facts c r x (gen_set_incr_varname n ab x) \<union> ab" in spec)
  apply (drule_tac x=x in spec)
  apply (drule mp, assumption)
  apply (drule_tac x=n in spec)
  apply (drule_tac x=r in spec)
  apply (drule_tac x=c in spec)
  apply (case_tac "numrestrc_ge_applicable (FactFm (Inst x ([\<ge>] n r c))) ab")

  (* case applicable *)
  apply simp
  apply (drule_tac x="gen_set_incr_varname n ab x" in spec)
  apply simp

  (* case not applicable *)
  apply (simp add: numrestrc_ge_applicable.simps numrestrc_ge_blocked_def)
  apply (elim exE conjE)
  apply (intro exI conjI)
  apply assumption+
  apply (clarsimp simp add: satis_induct_order_level_def) apply arith
done

lemma saturated_choose_rule: "saturated_abox ab alc_rule \<Longrightarrow> finite ab \<Longrightarrow>
  f \<in> ab \<Longrightarrow>
  f = FactFm (Inst x ([<] n r c)) \<Longrightarrow> 
  \<forall> y. FactFm (AtomR True r x y) \<in> ab  \<longrightarrow>
  (FactFm (Inst y c) \<in> ab \<or>  FactFm (Inst y (neg_norm_concept False c)) \<in> ab)"
apply (frule_tac saturated_abox_alc_ruleD [where r=eq_rule]) apply (simp add: set_alc_rules_def)
apply (frule_tac saturated_abox_alc_ruleD [where r=eq_compl_rule]) apply (simp add: set_alc_rules_def)
apply (drule_tac saturated_abox_alc_ruleD [where r=choose_rule]) apply (simp add: set_alc_rules_def)
apply (intro allI impI)
apply (subgoal_tac "neq_complete x ab") 
  prefer 2
  apply (rule saturated_eq_compl_rule_neq_complete, assumption+)
  apply (fastforce dest: fv_form_fv_abox) 
apply (clarsimp simp add: saturated_abox_def 
       choose_rule_def ex_rule_closure_def choose_rule_indiv.simps)
apply blast
done

(* almost the same result as above, but proved with the choose_stable_rule;
   In first condition, replace choose_stable_rule by alc_rule
   And there is an additional precondition corresponding to a non-clash condition
   *)
lemma saturated_choose_stable_rule: "saturated_abox ab choose_stable_rule \<Longrightarrow> finite ab \<Longrightarrow>
  f \<in> ab \<Longrightarrow> \<not> contains_contr_eq ab \<Longrightarrow>
  f = FactFm (Inst x ([<] n r c)) \<Longrightarrow> 
  \<forall> y. FactFm (AtomR True r x y) \<in> ab  \<longrightarrow>
  (FactFm (Inst y c) \<in> ab \<or>  FactFm (Inst y (neg_norm_concept False c)) \<in> ab)"
(* TODO: activate as soon as the rule is included in set_alc_rules_def *)
(* apply (drule_tac saturated_abox_alc_ruleD [where r=choose_stable_rule]) 
  apply (simp add: set_alc_rules_def) *) 
  apply (clarsimp simp add: saturated_abox_def 
    choose_stable_rule_def ex_rule_closure_def 
    choose_stable_rule_indiv.simps )
  apply blast
done


lemma saturated_subst :" FactFm (Inst x (SubstC c sb)) \<in> ab 
  \<Longrightarrow> saturated_abox ab alc_rule  
  \<Longrightarrow>  (push_subst_form ( FactFm (Inst x (SubstC c sb))) []) \<in> ab "
apply (drule_tac saturated_abox_alc_ruleD [where r=substc_rule]) apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def 
    substc_rule_def ex_rule_closure_def substc_rule_indiv.simps substc_applicable.simps)
  apply (drule spec)
  apply (drule_tac x= " FactFm (Inst x (SubstC c sb))" in spec)
  apply (drule mp)
  apply fastforce
  apply clarsimp
  apply blast
done

lemma saturated_substfm :" SubstFm fm subst \<in>  ab 
  \<Longrightarrow> saturated_abox ab alc_rule  
  \<Longrightarrow> push_subst_form (SubstFm fm subst)  [] \<in> ab "
apply (drule_tac saturated_abox_alc_ruleD [where r=substfm_rule]) apply (simp add: set_alc_rules_def)
  apply (clarsimp simp add: saturated_abox_def
    substfm_rule_def ex_rule_closure_def
    substfm_rule_indiv.simps substfm_applicable.simps simp del: push_subst_form.simps)
  apply (drule_tac x= "insert (push_subst_form (SubstFm fm subst) []) ab" in spec)
  apply (drule_tac x= " SubstFm fm subst " in spec)
  apply (simp del: push_subst_form.simps)
done

lemma saturated_empty_rule [simp]: "saturated_abox AB empty_rule"
  by (simp add: saturated_abox_def empty_rule_def)

lemma saturated_alternative_rule [simp]: "saturated_abox AB (alternative_rule r1 r2) =
  (saturated_abox AB r1 \<and> saturated_abox AB r2)"
  by (fastforce simp add: saturated_abox_def alternative_rule_def)

lemma saturated_alternative_rule_of_set [simp]:
  "saturated_abox AB (alternative_rule_of_set rls) = (Ball rls (saturated_abox AB))"
  by (fastforce simp add: saturated_abox_def alternative_rule_of_set_def)

(* -------------------------------------------------------------------------------*)
subsection {* Canonical interpretation *}
(* -------------------------------------------------------------------------------*)

definition  domain_interp ::"  ('nr,'nc,'ni) abox \<Rightarrow> 'ni set" where  
  "domain_interp ab = (if fv_abox ab = {} then {undefined} else fv_abox ab)"

fun interp_atomic_concept :: "('nr, 'nc, 'ni) abox \<Rightarrow>   'nc \<Rightarrow> 'ni set" where
  "interp_atomic_concept ab c =  ({x. (FactFm (Inst x (AtomC True c))) \<in> ab })"

fun interp_atomic_role :: "('nr, 'nc, 'ni) abox \<Rightarrow>'nr \<Rightarrow> ('ni * 'ni) set" where 
  "interp_atomic_role ab r =  ({(x,y). FactFm (AtomR True r x y) \<in> ab})"
  
definition interp_canon_indiv :: "'ni set \<Rightarrow> 'ni \<Rightarrow> 'ni" where
 "interp_canon_indiv d x = (if x \<in> d then x else SOME y. y \<in> d)"

definition  canon_interp :: "('nr, 'nc, 'ni) abox  \<Rightarrow> ('ni, 'nr, 'nc, 'ni) Interp" where
"canon_interp ab =
  \<lparr> interp_d = domain_interp ab, 
    interp_c = interp_atomic_concept ab, 
    interp_r = interp_atomic_role  ab, 
    interp_i = interp_canon_indiv (domain_interp ab) \<rparr>"

lemma interp_canon_indiv_nonempty: "d \<noteq> {} \<Longrightarrow> interp_canon_indiv d x \<in> d"
by (clarsimp simp add: interp_canon_indiv_def) (force intro: someI)


lemma well_formed_interp_canon_interp [simp]: 
  "well_formed_interp (canon_interp ab)"
apply (simp add: well_formed_interp_def canon_interp_def domain_interp_def)
apply (intro conjI)
apply (fastforce simp add: fv_abox_def domain_interp_def interp_canon_indiv_def)
apply clarify
apply (intro conjI)
apply (fastforce simp add: domain_interp_def fv_abox_def)
apply (clarsimp simp add: domain_interp_def fv_abox_def) apply (intro conjI) apply fastforce apply fastforce
apply (clarsimp simp add: interp_canon_indiv_nonempty)
done

    
(*** Proofs about canonical interpretation *)


lemma in_domain_interp [simp]:
  "f \<in> ab \<Longrightarrow> x \<in> fv_form f \<Longrightarrow> x \<in> (domain_interp ab)"
by (fastforce simp add: domain_interp_def fv_abox_def)

lemma interp_d_canon_interp [simp]:
  "f \<in> ab \<Longrightarrow> x \<in> fv_form f \<Longrightarrow> x \<in> interp_d (canon_interp ab)"
by (simp add: canon_interp_def)

lemma interp_canon_indiv_domain_interp_same [simp]:
  "f \<in> ab \<Longrightarrow> x \<in> fv_form f \<Longrightarrow> interp_canon_indiv (domain_interp ab) x = x"
by (fastforce simp add: interp_canon_indiv_def fv_abox_def)

lemma interp_i_canon_interp [simp]: 
  "f \<in> ab \<Longrightarrow> x \<in> fv_form f \<Longrightarrow> interp_i (canon_interp ab) x = x"
  by (clarsimp simp add: canon_interp_def)

lemma interp_r_canon_interp_FactFm:
  "(( x,  y) \<in> interp_r (canon_interp  ab) r) = (FactFm (AtomR True r x y) \<in> ab)"
   by  ( clarsimp  simp add: canon_interp_def inj_eq)

lemma  interp_c_canon_interp_FactFm :
  " (x \<in> interp_c (canon_interp ab) c) = (FactFm (Inst x (AtomC True c)) \<in> ab)"
 by ( clarsimp  simp add: canon_interp_def inj_eq image_def)


lemma canon_interp_satis_true_atom:
"FactFm (Inst x (AtomC True c)) \<in> ab \<Longrightarrow>
    \<not> contains_clash ab \<Longrightarrow> interp_fact (Inst x (AtomC True c)) (canon_interp  ab)"
 by (clarsimp simp add: contains_clash_def canon_interp_def)
 
lemma canon_interp_satis_false_atom:
"
    FactFm (Inst x (AtomC False c)) \<in> ab \<Longrightarrow>
    \<not> contains_clash ab \<Longrightarrow> interp_fact (Inst x (AtomC False c)) (canon_interp  ab)"
by  (clarsimp simp add: canon_interp_def   contains_clash_def image_def inj_eq)

lemma canon_interp_satis_atom:
"FactFm (Inst x (AtomC bool c)) \<in> ab \<Longrightarrow>
  \<not> contains_clash ab \<Longrightarrow> interp_fact (Inst x (AtomC bool c)) (canon_interp  ab)"
by (metis (poly_guards_query) canon_interp_satis_false_atom canon_interp_satis_true_atom)

lemma canon_interp_sat_true_rel :
   "FactFm (AtomR True r x y) \<in> ab  \<Longrightarrow> \<not> contains_contr_role ab  
   \<Longrightarrow> interp_fact (AtomR True r x y) (canon_interp ab)"
   by (clarsimp simp add: canon_interp_def image_def)

lemma canon_interp_sat_false_rel:
  "FactFm (AtomR False r x y) \<in> ab \<Longrightarrow> \<not> contains_contr_role ab 
  \<Longrightarrow> interp_fact (AtomR False r x y) (canon_interp  ab)"
by (clarsimp simp add: inj_eq  canon_interp_def  image_def )

lemma canon_interp_sat_rel:
  "FactFm (AtomR bool r x y) \<in> ab \<Longrightarrow> \<not> contains_contr_role ab \<Longrightarrow> interp_fact (AtomR bool r x y) (canon_interp ab)"
by (metis (poly_guards_query) canon_interp_sat_false_rel canon_interp_sat_true_rel)


lemma canon_interp_satis_Top :
  "FactFm (Inst x Top) \<in> ab \<Longrightarrow> interp_fact (Inst x Top) (canon_interp  ab)"
  by simp

lemma canon_interp_satis_bottom :
  "\<not> contains_clash ab \<Longrightarrow> FactFm (Inst x Bottom) \<in> ab \<Longrightarrow> interp_fact (Inst x Bottom) (canon_interp  ab)"
  by (clarsimp simp add: contains_clash_def)


definition "satis_induct_order == measures [(\<lambda>f. (subst_height_form f [])), height_form]"

lemma wf_satis_induct_order: "wf satis_induct_order"
by (simp add: satis_induct_order_def)


lemma FactFm_ConjC_satis_induct_order_level:
  "FactFm (Inst x (ConjC c1 c2)) \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> 
  FactFm (Inst x c1) \<in> ab \<and> FactFm (Inst x c2) \<in> ab \<and> 
   (FactFm (Inst x c1), FactFm (Inst x (ConjC c1 c2))) \<in> satis_induct_order_level \<and> 
   (FactFm (Inst x c2), FactFm (Inst x (ConjC c1 c2))) \<in> satis_induct_order_level"
apply (drule saturated_and)
apply assumption
apply clarsimp+
apply (simp add: satis_induct_order_level_def)
apply arith
done


lemma FactFm_DisjC_satis_induct_order_level:
  "FactFm (Inst x (DisjC c1 c2)) \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> 
  (FactFm (Inst x c1) \<in> ab \<or> FactFm (Inst x c2) \<in> ab) \<and> 
   (FactFm (Inst x c1), FactFm (Inst x (DisjC c1 c2))) \<in> satis_induct_order_level \<and> 
   (FactFm (Inst x c2), FactFm (Inst x (DisjC c1 c2))) \<in> satis_induct_order_level"
   apply (drule saturated_or)
   apply assumption
   apply clarsimp+
   apply (simp add: satis_induct_order_level_def)
   apply arith
done

lemma FactFm_AllC_satis_induct_order_level:
"FactFm (Inst x (AllC r c)) \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> 
  \<forall>y.( FactFm (AtomR True r x y) \<in> ab \<longrightarrow> FactFm (Inst y c) \<in> ab) \<and>( 
   (FactFm (AtomR True r x y), FactFm (Inst x (AllC r c))) \<in> satis_induct_order_level \<and> 
   ( FactFm (Inst y c), FactFm (Inst x (AllC r c)) ) \<in> satis_induct_order_level)"
apply (drule saturated_all) apply assumption
apply clarsimp+
apply (simp add: satis_induct_order_level_def)
apply arith
done

lemma  saturated_numrestrc_lt_1_for_choose:
"FactFm (Inst x ([<] 1 r c)) \<in> ab \<Longrightarrow>
    saturated_abox ab alc_rule \<Longrightarrow> 
    \<forall>y. FactFm (AtomR True r x y) \<in> ab 
    \<longrightarrow> FactFm (Inst y c) \<in> ab \<or> FactFm (Inst y (neg_norm_concept False c)) \<in> ab" 
  apply (subgoal_tac "saturated_abox ab choose_rule") prefer 2 apply (simp add: saturated_alc_rule set_alc_rules_def)
  apply (intro allI impI)
  apply (subgoal_tac "neq_complete x ab") 
        prefer 2 
        apply (rule saturated_eq_compl_rule_neq_complete)
        apply (simp add: alc_rule_def set_alc_rules_def)+
        apply (fastforce dest: fv_form_fv_abox)
  apply (clarsimp simp add: saturated_abox_def 
    choose_rule_def ex_rule_closure_def choose_rule_indiv.simps  choose_applicable.simps)
  apply (drule spec)
  apply (drule_tac x="{FactFm (Inst y c)} \<union> ab" in  spec)
  apply fastforce
  done

  
lemma FactFm_NumRestrC_lt_1_satis_induct_order_level_for_choose:
"FactFm (Inst x ([<] 1 r c)) \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> 
  \<forall>y.( FactFm (AtomR True r x y) \<in> ab 
     \<longrightarrow> FactFm (Inst y c) \<in> ab \<or> FactFm (Inst y (neg_norm_concept False c)) \<in> ab) \<and>( 
   (FactFm (AtomR True r x y), FactFm (Inst x ([<] 1 r c))) \<in> satis_induct_order_level \<and> 
   ( FactFm (Inst y (neg_norm_concept False c)), FactFm (Inst x ([<] 1 r c))) \<in> satis_induct_order_level)"
apply (drule saturated_numrestrc_lt_1_for_choose) apply assumption
apply clarsimp+
apply (simp add: satis_induct_order_level_def)
apply (insert height_concept_neg_norm_concept [of False c])
apply (insert subst_height_concept_neg_norm_concept [of False c])
apply arith
done


lemma FactFm_SomeC_satis_induct_order_level:
"finite ab \<Longrightarrow>FactFm (Inst (x:: 'ni ::new_var_set_incr_class) (SomeC r c)) \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow>
  \<exists> y. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab \<and> 
   (FactFm (AtomR True r x y), FactFm (Inst x (SomeC r c))) \<in> satis_induct_order_level \<and> 
   (FactFm (Inst y c), FactFm (Inst x (SomeC r c)) ) \<in> satis_induct_order_level"
 apply (drule_tac   saturated_some) apply assumption+
 apply (clarsimp simp add: satis_induct_order_level_def)
  apply blast
done


lemma ConjFm_satis_induct_order_level:
  "ConjFm f1 f2 \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> f1 \<in> ab \<and> f2 \<in> ab \<and>
   (f1, ConjFm f1 f2) \<in> satis_induct_order_level \<and> (f2, ConjFm f1 f2) \<in> satis_induct_order_level"
apply (drule saturated_conj)
apply assumption
apply (simp add: satis_induct_order_level_def)
apply arith
done

lemma DisjFm_satis_induct_order_level:
  "DisjFm f1 f2 \<in> ab \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> (f1 \<in> ab \<or> f2 \<in> ab) \<and>
   (f1, DisjFm f1 f2) \<in> satis_induct_order_level \<and> (f2, DisjFm f1 f2) \<in> satis_induct_order_level"
apply (drule saturated_disj)
apply assumption
apply (simp add: satis_induct_order_level_def)
apply arith
done

lemma FactFm_SubstC_satis_induct_order_level:
  "f \<in> ab \<Longrightarrow> f = FactFm (Inst x (SubstC c sb))  \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow> 
  push_subst_form f [] \<in> ab \<and> (push_subst_form f [], f) \<in> satis_induct_order_level"
apply (simp only:)
apply (frule saturated_subst) apply assumption
apply (rule conjI)
apply assumption
apply (simp del: push_subst_form.simps subst_height_form.simps add: satis_induct_order_level_def)
apply (rule disjI1)
apply (subgoal_tac "(push_subst_form (FactFm (Inst x (SubstC c sb))) []) 
      = (push_subst_form (FactFm (Inst x c)) [sb])")
apply (simp only:)
apply (rule order.strict_trans2)
apply (rule subst_height_form_push_subst_form_le) 
apply simp+
done


lemma SubstFm_satis_induct_order_level:
  "f \<in> ab \<Longrightarrow> f = SubstFm fm sb  \<Longrightarrow> saturated_abox ab alc_rule \<Longrightarrow>  
  push_subst_form f [] \<in> ab \<and> (push_subst_form f [], f) \<in> satis_induct_order_level"
apply (simp only:)
apply (frule saturated_substfm) apply assumption
apply (rule conjI)
apply assumption
apply (simp del: push_subst_form.simps subst_height_form.simps add: satis_induct_order_level_def)
apply (rule disjI1)
apply (subgoal_tac "(push_subst_form (SubstFm fm sb) []) = (push_subst_form fm [sb])")
apply (simp only:)
apply (rule order.strict_trans2)
apply (rule subst_height_form_push_subst_form_le) 
apply simp+
done

(* TODO (possibly): proof without the "saturated" precondition of 
lemma SubstFm_satis_induct_order_level, which is more useful for termination proofs *)

lemma SubstFm_satis_induct_order_level2:
  "f = SubstFm fm sb  \<Longrightarrow> 
  (push_subst_form f [], f) \<in> satis_induct_order_level"
apply (simp only:)
apply (simp del: push_subst_form.simps subst_height_form.simps add: satis_induct_order_level_def)
apply (rule disjI1)
apply (subgoal_tac "(push_subst_form (SubstFm fm sb) []) = (push_subst_form fm [sb])")
apply (simp only:)
apply (rule order.strict_trans2)
apply (rule subst_height_form_push_subst_form_le) 
apply simp+
done

lemma d0 [simp]: "inj i \<Longrightarrow> Suc n \<le> card a \<Longrightarrow> Suc n \<le> card (i ` a) "
by (metis card_image subset_UNIV subset_inj_on)
lemma d1 [simp]: "Suc n \<le> card A \<Longrightarrow> \<exists> a. a \<in> A "
by (metis Suc_le_D card_eq_SucD insertI1)


lemma inv_image_in_set: "inj i \<Longrightarrow> y \<in> i ` S \<Longrightarrow> inv i y \<in> S"
by auto

lemma finite_rel_restrict: "finite R \<Longrightarrow>
finite (rel_restrict R A B)"
by (simp add: rel_restrict_def)

lemma finite_Range_canon_interp:
"finite ab \<Longrightarrow> finite (Range (rel_restrict (interp_r (canon_interp  ab) r) IX CI))"
apply (rule finite_Range)
apply (rule finite_rel_restrict)
apply (simp add: canon_interp_def)

apply (subgoal_tac "finite {f \<in> ab. (\<exists> x y. f = FactFm (AtomR True r x y))}")
apply (subgoal_tac "finite {(x, y). FactFm (AtomR True r x y) \<in> ab} = finite {f \<in> ab. (\<exists> x y. f = FactFm (AtomR True r x y))}") 
prefer 2
apply (rule bij_betw_finite [where f = "\<lambda> (x, y). FactFm (AtomR True r x y)"])
defer
apply simp
apply (erule rev_finite_subset) apply blast
apply (auto simp add: bij_betw_def image_def inj_on_def)
done

definition "range_rel_restr_interp  ab x r cc = 
    (Range
       (rel_restrict (interp_r (canon_interp  ab) r)
         { x}
         (interp_concept cc (canon_interp  ab))))"

lemma interp_atomic_concept_fv_abox [rule_format]:
  "\<forall>  c. interp_atomic_concept  ab c \<subseteq>  (fv_abox ab)"
by (fastforce simp add: fv_abox_def image_def)

lemma interp_atomic_role_fv_abox:
  "interp_atomic_role  ab r \<subseteq> ( (fv_abox ab)) \<times> ( (fv_abox ab))"
by (fastforce simp add: fv_abox_def image_def)

lemma interp_r_canon_interp_fv_abox:
  "interp_r (canon_interp  ab) r \<subseteq> ((fv_abox ab)) \<times> ( (fv_abox ab))"
by (simp add: canon_interp_def interp_atomic_role_fv_abox del: interp_atomic_role.simps)

lemma range_rel_restr_interp_fv_abox:
 "range_rel_restr_interp  ab x r cc \<subseteq> (fv_abox ab)"
apply (simp add: range_rel_restr_interp_def rel_restrict_def)
apply (insert interp_r_canon_interp_fv_abox [of  ab r])
apply blast
done

lemma in_range_rel_restr_interp:
"(y \<in> range_rel_restr_interp ab x r c) =
(y \<in> (interp_concept c (canon_interp  ab)) \<and> 
 (x, y) \<in>  (interp_r (canon_interp  ab) r))"

by (auto simp add: range_rel_restr_interp_def rel_restrict_def)

definition "x_r_c_successor_forms ab x r c = 
      {f. \<exists> y. f = FactFm (Inst y c) \<and> f \<in> ab \<and> FactFm (AtomR True r x y) \<in> ab}"
      
definition "x_r_c_successors ab x r c = 
      {y. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab}"

definition "inhabitant_of_concept f = (case f of  FactFm (Inst y c) \<Rightarrow> y | _ \<Rightarrow> undefined)"

lemma x_r_c_successor_forms_x_r_c_successors:
  "x_r_c_successor_forms ab x r c = (\<lambda> y. FactFm (Inst y c)) ` x_r_c_successors ab x r c"
by (auto simp add: x_r_c_successor_forms_def x_r_c_successors_def image_def)

lemma x_r_c_successors_x_r_c_successor_forms:
  "x_r_c_successors ab x r c = inhabitant_of_concept ` x_r_c_successor_forms ab x r c"
by (auto simp add: x_r_c_successor_forms_def x_r_c_successors_def 
  image_def inhabitant_of_concept_def)

lemma card_x_r_c_successor_forms_x_r_c_successors:
  "card (x_r_c_successor_forms ab x r c) = card (x_r_c_successors ab x r c)"
apply (simp add: x_r_c_successor_forms_x_r_c_successors card_image)
apply (rule card_image)
apply (simp add: inj_on_def)
done

lemma range_rel_restr_interp_x_r_c_successors1: "
    \<forall>y. (y, FactFm (Inst x ([<] n r c))) \<in> satis_induct_order_level \<longrightarrow>
        y \<in> ab \<longrightarrow> interp_form y (canon_interp  ab) \<Longrightarrow>
    \<forall>y. FactFm (AtomR True r x y) \<in> ab \<longrightarrow>
           FactFm (Inst y c) \<in> ab \<or>
           FactFm (Inst y (neg_norm_concept False c)) \<in> ab \<Longrightarrow>
        (range_rel_restr_interp  ab x r c) \<subseteq> ( (x_r_c_successors ab x r c))"
apply (simp add: x_r_c_successors_x_r_c_successor_forms)
apply (clarsimp simp add: in_range_rel_restr_interp)
apply (rename_tac y)
apply (simp only:interp_r_canon_interp_FactFm) 

apply (drule spec, drule mp, assumption)
apply (simp (no_asm_simp) add: x_r_c_successor_forms_def image_def)
apply (erule disjE)

(* case FactFm (Inst y c) \<in> ab *)
apply (intro exI conjI)
 apply (rule refl)
apply assumption+ 
apply (simp add: inhabitant_of_concept_def)

(* case FactFm (Inst y (neg_norm_concept False c)) \<in> ab *)
apply (subgoal_tac "(FactFm (Inst y (neg_norm_concept False c)), FactFm (Inst x ([<] n r c)))
              \<in> satis_induct_order_level")
prefer 2 apply (simp add: satis_induct_order_level_def) 
     apply (insert height_concept_neg_norm_concept [of False c])
     apply (insert subst_height_concept_neg_norm_concept [of False c]) apply arith

apply (subgoal_tac "interp_form (FactFm (Inst y (neg_norm_concept False c))) (canon_interp ab)")
  prefer 2 apply blast
apply simp
done

lemma range_rel_restr_interp_x_r_c_successors2: "\<forall>y. (y, FactFm (Inst x ([<] n r c))) \<in> satis_induct_order_level \<longrightarrow>
        y \<in> ab \<longrightarrow> interp_form y (canon_interp  ab) \<Longrightarrow>
( (x_r_c_successors ab x r c)) \<subseteq> (range_rel_restr_interp  ab x r c)"
apply (simp add: x_r_c_successors_x_r_c_successor_forms)
apply (simp add: x_r_c_successor_forms_def image_def)
apply (clarsimp simp add: inhabitant_of_concept_def in_range_rel_restr_interp)
apply (subgoal_tac "(FactFm (Inst y c), FactFm (Inst x ([<] n r c))) \<in> satis_induct_order_level")
  prefer 2 apply (simp add: satis_induct_order_level_def)
apply (subgoal_tac "(FactFm (AtomR True r x y), FactFm (Inst x ([<] n r c))) \<in> satis_induct_order_level")
  prefer 2 apply (simp add: satis_induct_order_level_def) apply arith
apply (subgoal_tac "interp_form (FactFm (Inst y c)) (canon_interp  ab)") prefer 2 apply blast
apply (subgoal_tac "interp_form (FactFm (AtomR True r x y)) (canon_interp  ab)") prefer 2 apply blast
apply simp
done


lemma range_rel_restr_interp_x_r_c_successors: "
    \<forall>y. (y, FactFm (Inst x ([<] n r c))) \<in> satis_induct_order_level \<longrightarrow>
        y \<in> ab \<longrightarrow> interp_form y (canon_interp  ab) \<Longrightarrow>
    \<forall>y. FactFm (AtomR True r x y) \<in> ab \<longrightarrow>
           FactFm (Inst y c) \<in> ab \<or>
           FactFm (Inst y (neg_norm_concept False c)) \<in> ab \<Longrightarrow>
        (range_rel_restr_interp  ab x r c) = ( (x_r_c_successors ab x r c))"
apply (rule subset_antisym)
apply (erule range_rel_restr_interp_x_r_c_successors1, assumption+)
apply (rule range_rel_restr_interp_x_r_c_successors2, assumption+)
done

lemma interp_concept_lt_rule_canon_interp: "
       finite ab \<Longrightarrow>
       \<not> contains_clash ab \<Longrightarrow>
       is_neg_norm_abox ab \<Longrightarrow>
       \<forall>y. (y, FactFm (Inst x ([<] n r c)))
           \<in> satis_induct_order_level \<longrightarrow>
           y \<in> ab \<longrightarrow> interp_form y (canon_interp  ab) \<Longrightarrow>
       \<forall>y. FactFm (AtomR True r x y) \<in> ab \<longrightarrow>
           FactFm (Inst y c) \<in> ab \<or>
           FactFm (Inst y (neg_norm_concept False c)) \<in> ab \<Longrightarrow>
       FactFm (Inst x ([<] n r c)) \<in> ab \<Longrightarrow>
       \<forall>S. card S = n \<longrightarrow>
           (\<exists>y\<in>S. FactFm (AtomR True r x y) \<in> ab \<longrightarrow>
                   FactFm (Inst y c) \<notin> ab) \<Longrightarrow>
        x \<in> interp_concept ([<] n r c) (canon_interp  ab)"

   apply (clarsimp simp add: card_lt_def)
   apply (rule conjI)
   apply (erule finite_Range_canon_interp)
   
   apply (fold range_rel_restr_interp_def)
   apply (case_tac "card (x_r_c_successor_forms ab x r c) < n")

   (* case < *)
   apply (subgoal_tac "card (x_r_c_successors ab x r c) = card ( (x_r_c_successors ab x r c))")
      prefer 2 apply (rule sym) apply (fast intro: card_image subset_inj_on)
   apply (subgoal_tac "(range_rel_restr_interp  ab x r c) = ( (x_r_c_successors ab x r c))")
      prefer 2 apply (erule range_rel_restr_interp_x_r_c_successors, assumption+)
   apply (simp add: card_x_r_c_successor_forms_x_r_c_successors)
   
   (* case \<ge>  : argument: contradiction with \<forall> S. card S = n ... *)
   apply (subgoal_tac "\<exists> Si \<subseteq> (x_r_c_successors ab x r c). card Si = n")
      prefer 2 apply (rule finite_ge_card_eq_card) 
      apply (simp add: card_x_r_c_successor_forms_x_r_c_successors)
   apply clarify
   apply (drule_tac x = Si in spec)
   apply clarsimp
   apply (fastforce simp add: x_r_c_successors_def)
done

lemma canon_interp_satisfies_concept: "
      finite ab\<Longrightarrow>
       \<not> contains_clash ab \<Longrightarrow>  is_neg_norm_abox ab \<Longrightarrow> 
       saturated_abox ab alc_rule  \<Longrightarrow> 
       \<forall>y. (y, FactFm (Inst x c)) \<in> satis_induct_order_level \<longrightarrow> y \<in> ab \<longrightarrow> interp_form y (canon_interp  ab) \<Longrightarrow>
       FactFm (Inst (x::'ni::new_var_set_incr_class) c) \<in> ab 
       \<Longrightarrow> interp_i (canon_interp  ab) x \<in> interp_concept c (canon_interp  ab)"
apply (case_tac c)
(* Top *)
apply simp
(* Bottom *)
apply (clarsimp simp add: contains_clash_def)

(* AtomC *)
apply clarsimp
apply (rename_tac bool nc)
apply (case_tac bool)
apply (clarsimp simp add: canon_interp_def)
apply (clarsimp simp add: canon_interp_def inj_eq contains_clash_def)
(* NegC *)
apply (fastforce simp add: is_neg_norm_abox_def)

(* BinopC *)
apply clarsimp
apply (rename_tac bop c1 c2)
apply (case_tac bop)

(* subcase Conj *)
apply clarsimp
apply (drule FactFm_ConjC_satis_induct_order_level) apply assumption
apply fastforce

(* subcase Disj *)
apply clarsimp
apply (drule FactFm_DisjC_satis_induct_order_level) apply assumption
apply fastforce

(* NumRestrC *)
apply (rename_tac numres_ord n nr concept)
apply (case_tac numres_ord)
(* -- subcase Lt *)
apply (clarsimp simp del: interp_concept.simps)
apply (rename_tac n r cc)


apply (case_tac "n = 0")
(* case n = 0 *)
apply (simp add: contains_clash_def)

apply (case_tac "n = 1")
(* case n = 1 *)
apply (simp only:)
apply (simp (no_asm_simp) only: interp_concept_NumRestrC_AllC well_formed_interp_canon_interp)
apply (simp (no_asm_simp) add: interp_concept_AllC del: interp_concept.simps)
apply (frule FactFm_NumRestrC_lt_1_satis_induct_order_level_for_choose) apply assumption
apply clarsimp
apply (simp add: interp_r_canon_interp_FactFm)

apply (rename_tac r c1 y)
apply (drule_tac x= "y" in spec)
apply clarsimp
apply (frule_tac x= "FactFm (Inst y (neg_norm_concept False c1))" in spec)  
  
apply clarsimp
apply (frule_tac x= "FactFm (Inst y c1)" in spec)
apply clarsimp

apply (subgoal_tac "contains_atmost_clash ab") 
apply (simp add: contains_clash_def)
apply (simp only: contains_atmost_clash_def)
apply (intro exI) apply (rule conjI) apply assumption
apply (rule_tac x="{y}" in exI) 
apply (simp add: mutually_uneq_def R_succs_def)

(* case n > 1 *)
apply (frule saturated_choose_rule) apply assumption+ apply (rule refl)
apply (drule saturated_lt_rule) apply assumption+ apply (rule refl) 
apply (clarsimp simp del: interp_concept.simps)

apply (blast intro: interp_concept_lt_rule_canon_interp)

(* -- subcase Ge *)
apply (clarsimp simp del: interp_concept.simps)
apply (drule saturated_ge_rule) apply assumption+ apply (rule refl) 
apply (elim exE conjE)
apply (rule Numrestrc_Ge_interp_concept_impl)
apply simp
apply (rule_tac x = "S" in exI)
apply fastforce

(* SubstC *)
apply (clarsimp simp del: interp_form.simps)
apply (frule FactFm_SubstC_satis_induct_order_level) apply (rule refl) apply assumption+
apply clarify
apply (rename_tac cn sb)
apply (drule spec, drule mp, assumption, drule mp, assumption)
apply (simp del: push_subst_form.simps)

(*SomeC*)

apply (simp add: interp_concept_SomeC del:interp_concept.simps)
apply (frule FactFm_SomeC_satis_induct_order_level) apply assumption+
apply fastforce

(*AllC  *)

apply ( simp add:interp_concept_AllC del:interp_concept.simps)
apply (frule FactFm_AllC_satis_induct_order_level) apply assumption
apply clarsimp
apply (simp add: interp_r_canon_interp_FactFm) 
apply (rename_tac r c1 zi)
apply (drule_tac  x= "zi" in spec)
apply clarsimp
apply fastforce

done

lemma canon_interp_satisfies_fact: "
      finite  (ab::('b, 'c, 'a ::new_var_set_incr_class) form set) \<Longrightarrow>
       \<not> contains_clash ab \<Longrightarrow>  is_neg_norm_abox ab \<Longrightarrow> 
       saturated_abox ab alc_rule   \<Longrightarrow> 
      \<forall>y. (y, FactFm fact1) \<in> satis_induct_order_level \<longrightarrow> y \<in> ab \<longrightarrow> interp_form y (canon_interp  ab) \<Longrightarrow>
       FactFm fact1 \<in> ab \<longrightarrow> interp_fact fact1 (canon_interp  ab)"
apply (case_tac fact1)
apply (clarsimp simp only: interp_fact.simps)

apply (rule_tac ab = ab in canon_interp_satisfies_concept) apply assumption apply blast apply assumption +

apply (clarsimp simp only:)
apply (erule canon_interp_sat_rel) 

apply (simp add: contains_clash_def)
apply clarsimp
apply (rename_tac bool ni1 ni2)
apply (case_tac bool, clarsimp)
apply (metis (full_types) saturated_eq)
apply (clarsimp simp add:inj_eq contains_clash_def)
done

(* The lemma can be understood as a non-blocking condition: 
   if none of the rules is applicable, it is not because a rule gets stuck, but
   because the tableau contains a clash or is satisfiable.
*)
lemma canon_interp_satisfies_form [rule_format]: "
      finite  (ab::('b, 'c, 'a ::new_var_set_incr_class) form set) \<Longrightarrow>
      \<not> contains_clash ab \<Longrightarrow>  
      is_neg_norm_abox ab \<Longrightarrow> 
      saturated_abox ab alc_rule  \<Longrightarrow> 
      f \<in> ab \<longrightarrow> interp_form f (canon_interp  ab)"
apply (induct f rule: wf_induct)
apply (rule wf_satis_induct_order_level)
apply (rename_tac f)
apply simp
apply (case_tac f)

(* ConstFm *)
apply clarsimp
apply (rename_tac b)
apply (case_tac b)
apply simp
apply (simp add: contains_clash_def)

(* FactFm *)
     apply (simp only: interp_form.simps)

apply (rule canon_interp_satisfies_fact) apply assumption+

(* NegFm *)
apply (fastforce simp add: is_neg_norm_abox_def)

(* BinopFm *)
apply clarsimp
apply (rename_tac bop f1 f2)
apply (case_tac bop)

(* subcase Conj *)
apply clarsimp
apply (fast dest: ConjFm_satis_induct_order_level) 

(* subcase Disj *)
apply clarsimp
apply (fast dest: DisjFm_satis_induct_order_level)

(* SubstFm *)
apply (clarsimp simp del: interp_form.simps)
apply (drule SubstFm_satis_induct_order_level) apply (rule refl) apply assumption+
apply (clarsimp simp del: push_subst_form.simps interp_form.simps)
apply (drule spec, drule mp, assumption)
apply (simp del: push_subst_form.simps interp_form.simps)
done
 
lemma not_contains_clash_sati: "
     \<not> contains_clash (ab:: ('nr, 'nc, 'ni::new_var_set_incr_class) abox) \<Longrightarrow>  
     finite ab  \<Longrightarrow>
     is_neg_norm_abox ab \<Longrightarrow> 
     saturated_abox ab alc_rule  \<Longrightarrow> 
     satisfiable  TYPE('ni) ab"
apply (simp only: satisfiable_def)
apply (rule_tac x = "canon_interp  (ab::('nr, 'nc, 'ni::new_var_set_incr_class) abox)"  in exI)
by (clarsimp simp add: canon_interp_satisfies_form)

(*<*)
end
(*>*)
