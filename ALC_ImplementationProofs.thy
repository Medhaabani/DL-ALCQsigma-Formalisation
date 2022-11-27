theory ALC_ImplementationProofs imports (* ALC_Implementation *) 
   ALC_PrInfrastruc ALC_CompletenessProofs Decide_satisfiability

begin


type_synonym ('nr, 'nc, 'ni) abox_impl =  "(('nr, 'nc, 'ni) form) list"

type_synonym ('nr, 'nc, 'ni) rule_impl =  "('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox_impl list"

type_synonym ('nr, 'nc, 'ni) abox_abstraction ="('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox"

type_synonym ('nr, 'nc, 'ni) rule_abstraction ="('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) rule"

     
definition completeness_pres_rule_impl::
   "('nr,'nc,'ni) abox_abstraction \<Rightarrow>('nr,'nc,'ni) rule \<Rightarrow> ('nr,'nc,'ni) rule_impl \<Rightarrow> bool" where
  "completeness_pres_rule_impl aabstr r r_impl =
  (\<forall> abi.  (r_impl abi \<noteq> []) \<longrightarrow>
           (\<not> saturated_abox (aabstr abi) r) \<and> 
               (Collect (r (aabstr abi))) \<subseteq> aabstr ` (set (r_impl abi)))"

lemma completeness_pres_rule_impl_preserves_complete_neg:
"complete TYPE('d) r
\<Longrightarrow> completeness_pres_rule_impl aabstr r r_impl 
\<Longrightarrow> (r_impl ab_i) \<noteq> []
\<Longrightarrow> \<forall> ab2 \<in> aabstr ` (set (r_impl ab_i)). \<not> (satisfiable TYPE('d) ab2)
\<Longrightarrow> \<not> satisfiable TYPE('d) (aabstr ab_i)"
by (fastforce simp add: completeness_pres_rule_impl_def
     split: if_split_asm
     dest: complete_unsatisfiable)+

     (*
definition completeness_pres_rule_impl_ra::
   "('nr,'nc,'ni) abox_abstraction\<Rightarrow>('nr,'nc,'ni) rule_abstraction \<Rightarrow> ('nr,'nc,'ni) rule_impl \<Rightarrow> bool" where
  "completeness_pres_rule_impl_ra aabstr rabstr r_impl =
  (\<forall> abi. (Collect (rabstr r_impl (aabstr abi))) \<subseteq> aabstr ` (set (r_impl abi)))"


lemma completeness_pres_rule_impl_preserves_complete_neg_ra:
"complete (rabstr r_impl) 
\<Longrightarrow> \<not> saturated_abox (aabstr ab1) (rabstr r_impl) 
\<Longrightarrow> completeness_pres_rule_impl_ra aabstr rabstr r_impl 
\<Longrightarrow> \<forall> ab2 \<in> aabstr ` (set (r_impl ab1)). \<not> (satisfiable ab2)
\<Longrightarrow> \<not> satisfiable (aabstr ab1)"
by (erule complete_unsatisfiable, assumption)
   (fastforce simp add: completeness_pres_rule_impl_ra_def)


lemma completeness_pres_rule_impl_preserves_complete_ra:
"complete (rabstr r_impl) 
\<Longrightarrow> \<not> saturated_abox (aabstr ab1) (rabstr r_impl) 
\<Longrightarrow> completeness_pres_rule_impl_ra aabstr rabstr r_impl 
\<Longrightarrow> satisfiable (aabstr ab1)
\<Longrightarrow> \<exists> ab2 \<in> aabstr ` (set (r_impl ab1)). (satisfiable ab2)"
by (blast dest: completeness_pres_rule_impl_preserves_complete_neg_ra)
*)
 
fun check_trace :: 
  "(('nr, 'nc, 'ni) rule_rep \<Rightarrow> ('nr, 'nc, 'ni) rule_impl) \<Rightarrow> 
   ('nr, 'nc, 'ni) prooftrace \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> bool" where
"check_trace repinter (Trace rrep trs) abi = 
 list_all2 (check_trace repinter) trs (repinter rrep abi)"


  (* ----------------------------------------------------------------------  *)

definition conjc_appcond_impl :: 
  "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> bool" where
  "conjc_appcond_impl f ab_i= ((f \<in> set ab_i) \<and>
    (case f of 
    (FactFm (Inst x (ConjC c1 c2)) ) \<Rightarrow> 
        \<not> (FactFm (Inst x c1) \<in> set ab_i \<and> FactFm (Inst x c2) \<in> set ab_i)
    | _ \<Rightarrow> False))"
  

lemma conjc_appcond_impl_applicable: 
   "conjc_appcond_impl f ab_i = conjc_applicable f (set ab_i)"
by (auto simp add: conjc_appcond_impl_def conjc_applicable.simps
    split: form.split_asm fact.split_asm concept.split_asm binop.split_asm)

fun conjc_action_impl :: 
    "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox_impl list" where
  "conjc_action_impl (FactFm (Inst x (ConjC c1 c2))) ab_i = 
            [[FactFm (Inst x c1), FactFm (Inst x c2)] @ ab_i]"
 | "conjc_action_impl _ ab_i = []"

fun conjc_rule_indiv_impl :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule_impl" where
  "conjc_rule_indiv_impl f ab_i = 
  (if conjc_appcond_impl f ab_i then conjc_action_impl f ab_i else [])"

lemma completeness_pres_rule_impl_conjc_rule [simp]:
  "completeness_pres_rule_impl set (conjc_rule_indiv f) (conjc_rule_indiv_impl f)"
apply (simp add: completeness_pres_rule_impl_def) 
apply (simp add: conjc_appcond_impl_applicable)
apply (intro allI conjI impI)
apply (clarsimp simp add: saturated_abox_def conjc_rule_indiv.simps conjc_applicable.simps)
apply (fastforce simp add: conjc_applicable.simps conjc_rule_indiv.simps)
done

fun exec_rule_rep :: "('nr, 'nc, 'ni) rule_rep \<Rightarrow> ('nr, 'nc, 'ni) rule_impl" where
  "exec_rule_rep Clash_rep = (\<lambda> ab_i. [])"
| "exec_rule_rep (ConjCRule_rep f) = conjc_rule_indiv_impl f"

(* For later use with more detailed clash conditions
fun accept_trace_leaf :: "('nr, 'nc, 'ni) clash_rep \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow>  bool" where 
  "accept_trace_leaf (Cl_bottom x) ab_i =  (FactFm (Inst x Bottom) \<in> set ab_i)"
| "accept_trace_leaf (Cl_contr_concept x a) ab_i =  (FactFm (Inst x (AtomC True a)) \<in> set ab_i \<and> 
                                                     FactFm (Inst x (AtomC False a)) \<in> set ab_i)"
*)

definition accept_trace_leaf :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow>  bool" where 
 "accept_trace_leaf ab_i = 
    (contains_bottom_list ab_i \<or> 
     contains_contr_concept_list ab_i \<or>
     contains_contr_role_list ab_i \<or>
     contains_contr_eq_list ab_i \<or>
     contains_falsefm_list ab_i \<or>
     contains_numrestrc_clash_list ab_i)"

fun accept_trace :: "('nr, 'nc, 'ni) prooftrace \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow>  bool" where
  "accept_trace (Trace rr []) ab_i =
     (case rr of 
        Clash_rep  \<Rightarrow> accept_trace_leaf ab_i 
       | _ \<Rightarrow> False)"
| "accept_trace (Trace rr trcs) ab_i = list_all2 accept_trace trcs (exec_rule_rep rr ab_i)"

fun inner_rule_reps :: "('nr, 'nc, 'ni) prooftrace \<Rightarrow> ('nr, 'nc, 'ni) rule_rep set" where
  "inner_rule_reps (Trace rr [])  = {}"
| "inner_rule_reps (Trace rr trcs) = insert rr (\<Union> (inner_rule_reps ` set trcs))"

definition refines_abox :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
"refines_abox abi ab = (ab = (set abi))"


definition "unsatisfiable t ab = (\<not> (satisfiable t ab))"

lemma accept_trace_leaf_unsatisfiable: 
"accept_trace_leaf ab_i \<Longrightarrow> refines_abox ab_i ab \<longrightarrow> unsatisfiable t ab"
apply (clarsimp simp add: refines_abox_def)
apply (clarsimp simp add: unsatisfiable_def satisfiable_def)
sorry

(* TODO: rename *)
lemma in_set_zipE_modif :"
length xs = length ys \<Longrightarrow>
(\<forall> (x, y) \<in> set (zip xs ys). R x y) \<longrightarrow>  
(\<forall> x \<in> set xs. \<forall> y \<in> set ys . R x y \<longrightarrow> P x y) \<longrightarrow>
( \<forall> (x, y) \<in> set (zip xs ys). P x y)"
by (erule list_induct2) (auto split: prod.split_asm)

(* TODO: rename *)
lemma in_set_zipE_modif2 :"
length xs = length ys \<Longrightarrow>
( \<forall> (x, y) \<in> set (zip xs ys). P y) \<longrightarrow> (\<forall> y \<in> set ys. P y)"
by (erule list_induct2) (auto split: prod.split_asm)

lemma preserve_unsatisfiable_for_complete:
"complete TYPE('d) r \<Longrightarrow> 
 completeness_pres_rule_impl set r (exec_rule_rep rr) \<Longrightarrow>
 \<forall>abr\<in>set (exec_rule_rep rr ab_i). unsatisfiable TYPE('d) (set abr) \<Longrightarrow>
 0 < length (exec_rule_rep rr ab_i) \<Longrightarrow>
 unsatisfiable TYPE('d) (set ab_i)"
apply (drule completeness_pres_rule_impl_preserves_complete_neg [where ab_i=ab_i])
apply assumption
apply (clarsimp simp add: unsatisfiable_def)+
done

lemma ex_completeness_pres_rule_impl:
"0 < length (exec_rule_rep rr ab_i) \<Longrightarrow> 
 \<exists> r. completeness_pres_rule_impl set r (exec_rule_rep rr) \<and> complete TYPE('d) r" 
apply (case_tac rr)
(* Clash_rep *)
apply simp

(* AndRule_rep *)
apply simp
apply (intro exI conjI)
apply (rule completeness_pres_rule_impl_conjc_rule)
apply (rule conjc_rule_indiv_complete)

(* OrRule_rep *)
sorry

lemma preserve_unsatisfiable:
"0 < length (exec_rule_rep rr ab_i) \<Longrightarrow>
 \<forall>abr\<in>set (exec_rule_rep rr ab_i). unsatisfiable TYPE('d) (set abr) \<Longrightarrow>
 unsatisfiable TYPE('d) (set ab_i)"
apply (frule ex_completeness_pres_rule_impl)
apply clarify
apply (rule preserve_unsatisfiable_for_complete)
apply assumption+
apply simp
done

lemma accept_trace_unsatisfiable_step: "
       (\<forall> x \<in> set trcs.
           \<forall> y \<in> set (exec_rule_rep rr ab_i).
           accept_trace x y \<longrightarrow>
                unsatisfiable TYPE('d) (set y)) \<Longrightarrow>
       (length trcs) = length (exec_rule_rep rr ab_i) \<Longrightarrow>
       length trcs > 0 \<Longrightarrow>
       \<forall>(tr, abr)\<in>set (zip trcs (exec_rule_rep rr ab_i)). accept_trace tr abr \<Longrightarrow>
       unsatisfiable TYPE('d) (set ab_i)"
       apply (subgoal_tac " \<forall>(tr, abr)\<in>set (zip trcs (exec_rule_rep rr ab_i)). unsatisfiable TYPE('d) (set abr)")
       prefer 2 
       apply (blast dest: in_set_zipE_modif [where R=accept_trace and P = "\<lambda> x y. unsatisfiable TYPE('d) (set y)"])
       apply (subgoal_tac "\<forall> abr \<in> set (exec_rule_rep rr ab_i). unsatisfiable TYPE('d)(set abr)")
       prefer 2
       apply (drule in_set_zipE_modif2) apply (drule mp, assumption+)
       apply (rule preserve_unsatisfiable)
       prefer 2
       apply assumption
       apply simp
done
       
lemma accept_trace_unsatisfiable: 
"accept_trace trc ab_i \<Longrightarrow> \<forall> ab. (refines_abox ab_i ab \<longrightarrow> unsatisfiable TYPE('d) ab)"
apply (induct rule: accept_trace.induct)
apply (case_tac rr)
apply (simp add: accept_trace_leaf_unsatisfiable)
apply simp_all
apply clarsimp
apply (simp add: list_all2_iff  split add: prod.split_asm)
apply (clarsimp simp add: refines_abox_def)
apply (rule accept_trace_unsatisfiable_step)
prefer 4 apply blast
prefer 2 apply simp
apply fastforce
apply auto
done

(* -------------------------------------------------------------------------------*)
(* Implementation of canonical interpretation *)
(* -------------------------------------------------------------------------------*)

definition  fv_abox_impl_list ::"  ('nr,'nc,'ni) abox_impl \<Rightarrow> 'ni list" where
   "fv_abox_impl_list ab_i = list_Union (map fv_form_list ab_i)"
   

definition  abox_impl_concept_list ::"  ('nr,'nc,'ni) abox_impl \<Rightarrow> 'nc list" where
   "abox_impl_concept_list ab_i = 
   remdups (map concept_of_atomic_fact (filter (is_atomic_concept_fact True) ab_i))"

definition  abox_impl_role_list ::"  ('nr,'nc,'ni) abox_impl \<Rightarrow> 'nr list" where
   "abox_impl_role_list ab_i = 
   remdups (map role_of_atomic_fact (filter (is_atomic_role_fact True) ab_i))"   

fun group_by_funct :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> ('b \<Rightarrow> 'a list)" where
    "group_by_funct f [] = (\<lambda> b. [])"
  | "group_by_funct f (x # xs) = 
      (let g = (group_by_funct f xs) in g((f x) := List.insert x (g (f x))))"

lemma group_by_funct_Collect [simp]: "set (group_by_funct f xs b) = {x \<in> set xs. f x = b}"
apply (induct xs)
apply simp
apply (simp add: Let_def)
apply fastforce
done

definition interp_atomic_concept_impl :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> 'nc \<Rightarrow> 'ni list" where
  "interp_atomic_concept_impl ab_i =  
     (map inst_of_Inst_fact) \<circ> 
     (group_by_funct concept_of_atomic_fact (List.filter (is_atomic_concept_fact True) ab_i))"



definition interp_atomic_role_impl :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> 'nr \<Rightarrow> ('ni * 'ni) list" where
  "interp_atomic_role_impl ab_i =  
     (map insts_of_atomic_role) \<circ> 
     (group_by_funct role_of_atomic_fact (List.filter (is_atomic_role_fact True) ab_i))"

definition interp_atomic_inst_conc_impl :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> 'ni \<Rightarrow> (bool * 'nc) list" where
  "interp_atomic_inst_conc_impl ab_i =  
     (map concept_of_atomic_fact_signed) \<circ> 
     (group_by_funct inst_of_Inst_fact
      ((List.filter (is_atomic_concept_fact True) ab_i) @ (List.filter (is_atomic_concept_fact False) ab_i))
)"

lemma fv_abox_impl_list_fv_abox [simp]:
  "set (fv_abox_impl_list ab_i) = fv_abox (set ab_i)"
by (simp add: fv_abox_impl_list_def fv_abox_def)


lemma interp_atomic_concept_impl_interp_atomic_concept [simp]: 
  "set \<circ> (interp_atomic_concept_impl ab_i) =  interp_atomic_concept (set ab_i)"
by (simp add: fun_eq_iff image_def interp_atomic_concept_impl_def)
   (auto simp add: is_atomic_concept_fact_def inst_of_Inst_fact_def concept_of_atomic_fact_def
         split add: form.split_asm fact.split_asm concept.split_asm)

lemma interp_atomic_role_impl_interp_atomic_role [simp]:
 "set \<circ> (interp_atomic_role_impl ab_i) =  interp_atomic_role (set ab_i)"
by (simp add: fun_eq_iff image_def interp_atomic_role_impl_def)
   (auto simp add: is_atomic_role_fact_def insts_of_atomic_role_def role_of_atomic_fact_def
         split add: form.split_asm fact.split_asm concept.split_asm)

record ('nr, 'nc, 'ni) Interp_impl =
  interp_impl_i :: "'ni list" 
  interp_impl_c :: "'nc list" 
  interp_impl_r :: "'nr list" 
  interp_impl_c_i :: "('nc \<Rightarrow> 'ni list)"
  interp_impl_r_i :: "('nr  \<Rightarrow> ('ni  * 'ni) list)"
  interp_impl_i_c :: "('ni \<Rightarrow> (bool *'nc) list)"

definition  canon_interp_impl :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) Interp_impl" where
"canon_interp_impl ab_i =
  \<lparr> interp_impl_i = fv_abox_impl_list ab_i, 
    interp_impl_c = abox_impl_concept_list ab_i,
    interp_impl_r = abox_impl_role_list ab_i,
    interp_impl_c_i = interp_atomic_concept_impl ab_i,
    interp_impl_r_i = interp_atomic_role_impl ab_i,
    interp_impl_i_c = interp_atomic_inst_conc_impl ab_i
    \<rparr>"

lemma distinct_group_by_funct [rule_format,simp]: "distinct (group_by_funct f xs b)"
by (induct xs) (auto simp add: Let_def)
      
lemma distinct_fv_abox_impl_list [simp]: "distinct (fv_abox_impl_list ab_i)"
by (simp add: fv_abox_impl_list_def)

lemma distinct_abox_impl_concept_list [simp]: "distinct (abox_impl_concept_list ab_i)"
by (simp add: abox_impl_concept_list_def)

lemma distinct_abox_impl_role_list [simp]: "distinct (abox_impl_role_list ab_i)"
by (simp add: abox_impl_role_list_def)

lemma distinct_interp_atomic_concept_impl [simp]: "distinct (interp_atomic_concept_impl ab_i c)"
apply (simp add: interp_atomic_concept_impl_def)
apply (simp add: distinct_map)
apply (clarsimp simp add: inj_on_def inst_of_Inst_fact_def is_atomic_concept_fact_def 
  concept_of_atomic_fact_def split add: form.split_asm fact.split_asm concept.split_asm)+
done

lemma distinct_interp_atomic_role_impl [simp]:  "distinct (interp_atomic_role_impl ab_i c)"
apply (simp add: interp_atomic_role_impl_def)
apply (simp add: distinct_map)
apply (clarsimp simp add: inj_on_def insts_of_atomic_role_def is_atomic_role_fact_def 
  role_of_atomic_fact_def split add: form.split_asm fact.split_asm concept.split_asm)+
done

lemma distinct_interp_atomic_inst_conc_impl [simp]: "distinct (interp_atomic_inst_conc_impl ab_i c)"
apply (simp add: interp_atomic_inst_conc_impl_def)
apply (simp add: distinct_map)
apply (clarsimp simp add: inj_on_def concept_of_atomic_fact_signed_def is_atomic_concept_fact_def
  inst_of_Inst_fact_def split add: form.split_asm fact.split_asm concept.split_asm)+
done

definition interp_impl_abstraction :: "('nr, 'nc, 'ni) Interp_impl \<Rightarrow> ('ni, 'nr, 'nc, 'ni) Interp" where
"interp_impl_abstraction ii = 
  \<lparr> interp_d = (if set (interp_impl_i ii) = {}  then {undefined} else set (interp_impl_i ii)),
    interp_c = set \<circ> (interp_impl_c_i ii),
    interp_r = set \<circ> (interp_impl_r_i ii),
    interp_i = (if set (interp_impl_i ii) = {} 
                then (\<lambda> x. undefined)  
                else interp_canon_indiv (set (interp_impl_i ii)))  \<rparr>"
    
lemma interp_impl_abstraction_canon_interp_impl [simp]:
  "interp_impl_abstraction (canon_interp_impl ab_i) = canon_interp (set ab_i)"
apply (simp add: interp_impl_abstraction_def canon_interp_impl_def canon_interp_def)
apply (simp add: domain_interp_def interp_canon_indiv_def)
apply (simp add: fun_eq_iff interp_canon_indiv_def)
done

end

