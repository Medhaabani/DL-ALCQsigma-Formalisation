(* CURRENTLY NOT USED *)

(* theory ALC_Implementation  imports SoundnessProofs CompletenessProofs TerminationProofs Aux *)
theory ALC_Implementation  imports ALC_PrInfrastruc 
(* MultisetAux *) 


begin

  (* ---------------------------------------------------------------------- *)
  (* ABOX *)
  (* ---------------------------------------------------------------------- *)


type_synonym ('nr, 'nc, 'ni) abox_impl =  "(('nr, 'nc, 'ni) form) list"

type_synonym ('nr, 'nc, 'ni) rule_impl =  "('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox_impl list"

type_synonym ('nr, 'nc, 'ni) tableau_impl  = "('nr, 'nc, 'ni) abox_impl list"

type_synonym ('nr, 'nc, 'ni) appcond ="('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool"

type_synonym ('nr, 'nc, 'ni) action = "('nr, 'nc, 'ni) abox_impl * ('nr, 'nc, 'ni) form * ('nr, 'nc, 'ni) abox_impl
                                                                 \<Rightarrow>('nr, 'nc, 'ni) abox_impl list"

datatype ('nr, 'nc, 'ni) srule = Rule "('nr, 'nc, 'ni) appcond * ('nr, 'nc, 'ni) action"




(******* rules implementation ******)
primrec
  split_appcond  :: 
  "(('nr, 'nc, 'ni) appcond) 
  \<Rightarrow> ('nr, 'nc, 'ni) abox_impl
  \<Rightarrow> ('nr, 'nc, 'ni) abox_impl
  \<Rightarrow> ('nr, 'nc, 'ni) abox_impl
  \<Rightarrow> ((('nr, 'nc, 'ni) abox_impl * ('nr, 'nc, 'ni) form * ('nr, 'nc, 'ni) abox_impl) list)" where

  "split_appcond appc prefix [] ab = []"
| "split_appcond appc prefix (ft#suffix) ab = 
    (if (appc ab ft)
    then (prefix, ft, suffix) #
         (split_appcond appc (prefix @ [ft]) suffix ab)    
    else (split_appcond appc (prefix @ [ft]) suffix ab))"


  (* TODO: This introduces a high branching factor. Should be avoided for permutable rules. *)

fun apply_srule :: "('nr, 'nc, 'ni) srule \<Rightarrow> ('nr, 'nc, 'ni) rule_impl" where 
  "apply_srule (Rule(appc, act)) ab_i =
  concat (map act (split_appcond appc [] ab_i ab_i))"

(*************      And rule     **************)

fun is_x_c_inst :: "'ni \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool" where 
  "is_x_c_inst x c f =  (f = FactFm (Inst x c))"

fun appcond_and :: "('nr, 'nc, 'ni) appcond" where
  "appcond_and ab_i (FactFm (Inst x (ConjC c1 c2))) = 
  (\<not>((list_ex (is_x_c_inst x c1) ab_i) \<and> (list_ex (is_x_c_inst x c2) ab_i)))"
  |"appcond_and ab_i  _  = False"

fun action_and :: "('nr, 'nc, 'ni) action" where
  "action_and (prefix, FactFm (Inst x (ConjC c1 c2)), suffix) = 
            [[FactFm (Inst x c1), FactFm (Inst x c2)] @ prefix @ [FactFm (Inst x (ConjC c1 c2))] @ suffix]"
          | "action_and _  = []"

definition and_srule :: "('nr, 'nc, 'ni) srule" where 
  "and_srule == Rule (appcond_and, action_and)"

definition conjc_rule_impl ::"('nr, 'nc, 'ni) rule_impl" where
  "conjc_rule_impl \<equiv> apply_srule and_srule"

  (* Test, can be deleted *)
lemma "conjc_rule_impl 
  [(FactFm (Inst x (ConjC (AtomC True 1) (AtomC True 2)))), (FactFm (Inst x (ConjC (AtomC True 3) (AtomC True 4))))] = X"
apply (simp add: conjc_rule_impl_def and_srule_def)
sorry


(*************      Or rule     **************)

fun appcond_or :: "('nr, 'nc, 'ni) appcond" where
    "appcond_or ab_i (FactFm (Inst x (DisjC c1 c2))) = 
      ((\<not> (list_ex (is_x_c_inst x c1) ab_i )) \<and> \<not> (list_ex (is_x_c_inst x c2) ab_i))"
    |"appcond_or ab_i  _  = False"

fun action_or_left:: "('nr, 'nc, 'ni) action" where
  "action_or_left (prefix, FactFm (Inst x (DisjC c1 c2)), suffix) = 
  [[FactFm (Inst x c1)] @ prefix @ [FactFm (Inst x (DisjC c1 c2))] @ suffix]"
  | "action_or_left _  = []"

fun action_or_right:: "('nr, 'nc, 'ni) action" where
  "action_or_right (prefix, FactFm (Inst x (DisjC c1 c2)), suffix) = 
    [[FactFm (Inst x c2)] @ prefix @ [FactFm (Inst x (DisjC c1 c2))] @ suffix]"
  | "action_or_right _  = []"

fun action_or:: "('nr, 'nc, 'ni) action" where
  "action_or (prefix, FactFm (Inst x (DisjC c1 c2)), suffix) = 
    [[FactFm (Inst x c1)] @ prefix @ [FactFm (Inst x (DisjC c1 c2))] @ suffix,
     [FactFm (Inst x c2)] @ prefix @ [FactFm (Inst x (DisjC c1 c2))] @ suffix]"
  | "action_or  _  = []"

definition or_srule_left ::"('nr, 'nc, 'ni) srule"  where
  "or_srule_left == Rule (appcond_or, action_or_left)"

definition disjc_rule_left_impl ::"('nr, 'nc, 'ni) rule_impl"  where
  "disjc_rule_left_impl == apply_srule or_srule_left"

definition or_srule_right ::"('nr, 'nc, 'ni) srule"  where
  "or_srule_right == Rule (appcond_or, action_or_right)"

definition disjc_rule_right_impl ::"('nr, 'nc, 'ni) rule_impl"  where
  "disjc_rule_right_impl == apply_srule or_srule_right"

definition or_srule ::"('nr, 'nc, 'ni) srule"  where
  "or_srule == Rule (appcond_or, action_or)"

definition disjc_rule_impl ::"('nr, 'nc, 'ni) rule_impl"  where
  "disjc_rule_impl == apply_srule or_srule"


(*************      All rule     **************)

fun is_x_r_rel :: "'ni \<Rightarrow> 'ni \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool"
  where 
  "is_x_r_rel x  y r  f =  (f = FactFm (AtomR True r x y))"

(* TODO: Still needed?
fun is_related_all ::" 'ni \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) fact \<Rightarrow> bool "
  where
   "is_related_all x r c ab_i (AtomR True  r' x' y) = 
       ((x = x'  \<and> r = r') \<and> (\<not>  (list_ex  (is_x_c_inst y c) ab_i)))"
 | "is_related_all x r c ab_i _ = False "
*)

  (* TODO: remove (list_ex (is_x_r_rel x y r) ab_i) *)
fun is_related_all_test ::" 'ni \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) concept 
  \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool"  where
   "is_related_all_test x r c ab_i (FactFm (AtomR sign  r' x' y)) = 
       (sign \<and> r' = r \<and> x' = x  \<and> (list_ex (is_x_r_rel x y r) ab_i) \<and> (\<not>  (list_ex  (is_x_c_inst y c) ab_i)))"
 | "is_related_all_test  x r c ab_i _ = False "



(* TODO: Still needed?
lemma is_related_all_rew:
  "is_related_all x r c ab_i f = (\<exists>y. f = AtomR True r x y \<and> \<not> list_ex (is_x_c_inst y c) ab_i)"
  apply  (case_tac f)
  apply (fastforce simp add: list_ex_is_x_c_inst)+
  apply clarsimp
  apply (metis (full_types) is_related_all.simps(1) is_related_all.simps(3))
  apply clarsimp
  done
*)

fun appcond_all :: "('nr, 'nc, 'ni) appcond" where
    "appcond_all ab_i (FactFm (Inst x (AllC r c))) = list_ex (is_related_all_test x r c ab_i) ab_i"
    |"appcond_all ab_i  _  = False"


    (* --------------------------------------------------  *)


(* TODO: Still needed? *)
fun sel_rel_y :: "'nr \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> 'ni option" where 
  "sel_rel_y r x (FactFm (AtomR True r' x' y)) = (if r=r' \<and>  x=x' then Some y else None)"
| "sel_rel_y r x _ = None"

(* TODO: Still needed? *)
fun sel_rel_y2 :: "'nr \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> 'ni option" where 
  "sel_rel_y2 r x  = (\<lambda> f.
  (case f of 
  (FactFm (AtomR True r' x' y )) \<Rightarrow> (if ((r = r') \<and> (x = x')) then Some y else None)
  | _ \<Rightarrow> None))"

(* TODO: Still needed? *)
fun sel_inst_y :: "('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> 'ni option" where 
  "sel_inst_y c (FactFm (Inst y c')) = (if (c = c') then Some y else None)"
  | "sel_inst_y c _ = None"
    
fun trans_rel_inst :: "('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) form" where
  "trans_rel_inst c (FactFm (AtomR True r x y)) = FactFm (Inst y c)"
| "trans_rel_inst c f = f"


fun action_all :: "('nr, 'nc, 'ni) action" where
  "action_all (prefix, FactFm (Inst x (AllC r c)) , suffix) = 
  ( 
  let ab_orig = (prefix @ [FactFm (Inst x (AllC r c))] @ suffix) in
  let related = ( filter (is_related_all_test x r c ab_orig) ab_orig) in
  let new_fact = (map (trans_rel_inst c) related) in
  list_distrib new_fact ab_orig)"
  | "action_all  _  = []"

definition all_srule ::"('nr, 'nc, 'ni) srule" where
  "all_srule == Rule (appcond_all, action_all)"

definition allc_rule_impl ::"('nr, 'nc, 'ni) rule_impl" where
  "allc_rule_impl == apply_srule all_srule"


 
  (*************      Some rule     **************)


  (* TODO: still needed ?

fun  occurs_ni_in_fact ::  "'ni \<Rightarrow> ('nr, 'nc, 'ni) fact \<Rightarrow> bool" where   
  " occurs_ni_in_fact x (Inst z  c)        =  (x = z) "
  | " occurs_ni_in_fact x (AtomR sign r ni1 ni2)  =  (x = ni1 \<or> x =ni2) "
  | " occurs_ni_in_fact x (Eq  sign  ni1 ni2)  =  (x = ni1 \<or> x =ni2) "

fun occurs_ni_in_abox :: " 'ni \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where 
  "occurs_ni_in_abox x ab = (\<exists> f \<in> ab. (occurs_ni_in_fact x f)) "
 
fun not_occurs_ni_in_abox :: " 'ni \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where 
  "not_occurs_ni_in_abox  x ab = (\<forall>f \<in> ab. \<not> (occurs_ni_in_fact x f)) "

fun set_ni_in_abox1 :: "('nr, 'nc, 'ni) abox \<Rightarrow> 'ni set" where 
  "set_ni_in_abox1 AB = {x. occurs_ni_in_abox x AB}"

fun set_ni_notin_abox :: "('nr, 'nc, 'ni) abox \<Rightarrow> 'ni set" where 
  "set_ni_notin_abox AB = - set_ni_in_abox1 AB"
*)

fun is_related_some_neg ::
  "'ni \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool"
  where
   "is_related_some_neg x r c ab_i (FactFm (AtomR True r' x' y)) = 
      (x=x' \<and> r=r' \<and> list_ex (is_x_r_rel x y r) ab_i \<and> list_ex (is_x_c_inst y c) ab_i)"
 | "is_related_some_neg  x r c ab_i _ = False "


fun appcond_some :: "('nr, 'nc, 'ni) appcond" where
  "appcond_some ab_i (FactFm (Inst x (SomeC r c ))) = 
  (\<not> list_ex (is_related_some_neg  x r c ab_i) ab_i) "
  |"appcond_some ab_i  _  = False"


(*
fun list_ni_abox_imp ::"('nr, 'nc, 'ni) fact list \<Rightarrow> 'ni list" where 
   "list_ni_abox_imp [] = []"
  | "list_ni_abox_imp (xl#xs) = 
       (case xl of 
       AtomR sign r x y \<Rightarrow>  list_union [x] (list_union [y] (list_ni_abox_imp xs))
     | Inst x c \<Rightarrow>  list_union [x] (list_ni_abox_imp xs)
     | Eq sign x y  \<Rightarrow> list_union [x] (list_union [y] (list_ni_abox_imp xs)))"
*)

fun fv_abox_impl :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> 'ni set" where
  "fv_abox_impl abi = List.foldr (\<lambda> f r. (fv_form f) \<union> r) abi {}"
 
(* Broken after use of the type classes in New_Var.thy *)
(* new_var_set now takes two arguments, the second one being a suggested name *)
(*
definition gen_not_occurs_ni_in_abox :: "('nr, 'nc, ('ni::new_var_set_class)) abox_impl \<Rightarrow> 'ni" where
  "gen_not_occurs_ni_in_abox ab \<equiv> (new_var_set (fv_abox_impl ab))"


fun action_some :: 
  "((('nr, 'nc, ('ni::new_var_set_class)) abox_impl) \<Rightarrow> 'ni) \<Rightarrow> ('nr, 'nc, 'ni) action" where
  "action_some gen (prefix, FactFm (Inst x (SomeC r c)), suffix) = 
  (let ab_org = (prefix @ [FactFm (Inst x (SomeC r c))] @ suffix) in
  let genvar = gen ab_org in
  [[ FactFm (Inst genvar c), FactFm (AtomR True r x genvar)] @ ab_org])"
  | "action_some  gen _  = []"


definition some_srule ::"('nr, 'nc, ('ni::{new_var_set_class})) srule" where
  "some_srule == Rule (appcond_some, action_some gen_not_occurs_ni_in_abox)"

definition somec_rule_impl ::"('nr, 'nc, ('ni::{new_var_set_class})) rule_impl" where
  "somec_rule_impl == apply_srule some_srule"
*)
(*
definition some_srule_gen ::
  "((('nr, 'nc, 'ni) abox_impl) \<Rightarrow> 'ni) \<Rightarrow> ('nr, 'nc, 'ni::alloc) srule" where
  "some_srule_gen gen == Rule (appcond_some, action_some gen)"

definition somec_rule_gen ::
  "((('nr, 'nc, 'ni) abox_impl) \<Rightarrow> 'ni) \<Rightarrow> ('nr, 'nc, 'ni::alloc) rule_impl" where
  "somec_rule_gen gen == apply_srule (some_srule_gen gen)"
*)


 
  (*************      Subst rule     **************)

fun appcond_subst :: "('nr, 'nc, 'ni) appcond" where
    "appcond_subst ab_i (FactFm (Inst x (SubstC c sb)))  = 
                  (\<not> (neg_norm_form True (push_subst_form (FactFm (Inst x (SubstC c sb))) [])) \<in> set ab_i)"
  | "appcond_subst ab_i  _  = False"


fun action_subst :: "('nr, 'nc, 'ni) action" where
    "action_subst (prefix, (FactFm (Inst x (SubstC c sb))), suffix) = 
     [[neg_norm_form True (push_subst_form (FactFm (Inst x (SubstC c sb))) [])]  
            @ prefix @ [(FactFm (Inst x (SubstC c sb)))] @ suffix]"
  | "action_subst _  = []"

definition subst_srule :: "('nr, 'nc, 'ni) srule" where 
  "subst_srule == Rule (appcond_subst, action_subst)"

definition substc_rule_impl ::"('nr, 'nc, 'ni) rule_impl" where
  "substc_rule_impl \<equiv> apply_srule subst_srule"


  (*************      Eq rule     **************)


fun appcond_eq :: "('nr, 'nc, 'ni) appcond" where
    "appcond_eq ab_i (FactFm (Eq True x y)) = (x \<noteq> y)"
  | "appcond_eq ab_i  _  = False"


fun action_eq :: "('nr, 'nc, 'ni) action" where
    "action_eq (prefix, (FactFm (Eq True x y)), suffix) = 
              [map (\<lambda> f. rename_in_form f [(x, y)]) (prefix @ [(FactFm (Eq True x y))] @ suffix)]"
  | "action_eq _  = []"

definition eq_srule :: "('nr, 'nc, 'ni) srule" where 
  "eq_srule == Rule (appcond_eq, action_eq)"

definition eq_rule_impl ::"('nr, 'nc, 'ni) rule_impl" where
  "eq_rule_impl \<equiv> apply_srule eq_srule"


  (*************      Conj rule     **************)


fun appcond_conj :: "('nr, 'nc, 'ni) appcond" where
  "appcond_conj ab_i (ConjFm f1 f2) =  (\<not> (f1 \<in> set ab_i \<and> f2 \<in> set ab_i))"
  |"appcond_conj ab_i  _  = False"


fun action_conj :: "('nr, 'nc, 'ni) action" where
    "action_conj (prefix, (ConjFm f1 f2), suffix) = 
              [[f1, f2] @ prefix @ [ConjFm f1 f2] @ suffix]"
  | "action_conj _  = []"

definition conj_srule :: "('nr, 'nc, 'ni) srule" where 
  "conj_srule == Rule (appcond_conj, action_conj)"

definition conjfm_rule_impl ::"('nr, 'nc, 'ni) rule_impl" where
  "conjfm_rule_impl \<equiv> apply_srule conj_srule"


  (*************      Disjrule     **************)


fun appcond_disj :: "('nr, 'nc, 'ni) appcond" where
    "appcond_disj ab_i (DisjFm f1 f2) = (f1 \<notin> set ab_i \<and> f2 \<notin> set ab_i)"
  | "appcond_disj ab_i  _  = False"

fun action_disj:: "('nr, 'nc, 'ni) action" where
    "action_disj (prefix, (DisjFm f1 f2), suffix) = 
    [[f1] @ prefix @ [(DisjFm f1 f2)] @ suffix,
     [f2] @ prefix @ [(DisjFm f1 f2)] @ suffix]"
  | "action_disj  _  = []"
 
definition disj_srule :: "('nr, 'nc, 'ni) srule" where 
  "disj_srule == Rule (appcond_disj, action_disj)"

definition disjfm_rule_impl ::"('nr, 'nc, 'ni) rule_impl" where
  "disjfm_rule_impl \<equiv> apply_srule disj_srule"


  (*************      Rule combinators     **************)


fun empty_rule_impl :: "('nr, 'nc, 'ni) rule_impl"
  where "empty_rule_impl a = []"

fun compose_rule_appl ::
  "('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) rule_impl"
  where "compose_rule_appl r1 r2 = (\<lambda> ab. concat (map r2 (r1 ab)))"

fun alternative_rule_impl ::
  "('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) rule_impl" where
  "alternative_rule_impl r1 r2 = (\<lambda> ab. (list_union (r1 ab) (r2 ab)))"

fun  alternative_rule_list_impl :: 
  "('nr, 'nc, 'ni) rule_impl list  \<Rightarrow> ('nr, 'nc, 'ni) rule_impl" where 
    "alternative_rule_list_impl [] = empty_rule_impl"
  | "alternative_rule_list_impl (r#rs) = (alternative_rule_impl r (alternative_rule_list_impl rs))"

(*
definition list_alc_rules_impl_gen ::
  "((('nr, 'nc, 'ni) abox_impl) \<Rightarrow> 'ni) \<Rightarrow> ('nr, 'nc, 'ni::new_var_set_class var) rule_impl list" where
 "list_alc_rules_impl_gen gen ==  [conjc_rule, disjc_rule, allc_rule, somec_rule]"


definition  alc_rule_impl_gen :: 
  "((('nr, 'nc, 'ni) abox_impl) \<Rightarrow> 'ni) \<Rightarrow> ('nr, 'nc, 'ni::alloc) rule_impl"
  where 
  "alc_rule_impl_gen gen = disjfm_rule_list_impl (list_alc_rules_impl_gen gen)"

definition list_alc_rules_impl :: "('nr,'nc,'ni::{alloc,linorder})rule_impl list " 
  where
  "list_alc_rules_impl == list_alc_rules_impl_gen gen_not_occurs_ni_in_abox"
*)
(*
definition  alc_rule_impl ::  "('nr, 'nc, ('ni::{new_var_set_class})) rule_impl"  where 
  "alc_rule_impl = alternative_rule_list_impl 
         [conjc_rule_impl, disjc_rule_impl, allc_rule_impl, somec_rule_impl, 
          substc_rule_impl, eq_rule_impl,  conjfm_rule_impl, disjfm_rule_impl]"
*)

fun is_reducible_abox ::
  "('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> bool" where
  "is_reducible_abox rule ab = (rule ab \<noteq> [])"

  (* TODO: still needed ? *)
fun is_reducible_tableau_impl ::
  "('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) tableau_impl \<Rightarrow> bool"  where
  "is_reducible_tableau_impl rule = list_ex (is_reducible_abox rule)"

  (* TODO: still needed ? *)
fun apply_rule_tableau_impl ::
  "('nr, 'nc, 'ni) rule_impl \<Rightarrow> ('nr, 'nc, 'ni) tableau_impl \<Rightarrow> ('nr, 'nc, 'ni) tableau_impl"  where
  "apply_rule_tableau_impl rule tab = concat (map rule tab)"

  (* TODO: still needed ? 
definition new_var_set:: "'a::{linorder,new_var_set_class} set \<Rightarrow> 'a" 
  where "new_var_set A = new_var (sorted_list_of_set A)"


definition  genterm :: "('nr, 'nc, 'ni::{new_var_set_class,linorder}) abox \<Rightarrow> 'ni" where 
  "genterm ab = new_var_set (set_ni_in_abox1 ab)"
*)


    (* ----------------------------------------------------------------------  *)
    (* Clashs *)

fun is_bot_inst :: "('nr, 'nc, 'ni) form \<Rightarrow> bool"
  where
    "is_bot_inst (FactFm (Inst x Bottom)) = True"
  | "is_bot_inst _  = False"

fun contains_bottom_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool" where  
  "contains_bottom_impl ab = (list_ex is_bot_inst ab)"

fun is_neg_inst :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool" where
    "is_neg_inst (FactFm (Inst x (AtomC sign a))) f = (f = (FactFm (Inst x (AtomC (\<not> sign) a))))"
  | "is_neg_inst _ f = False"

fun contains_contr_concept_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool" where  
  "contains_contr_concept_impl ab = (list_ex  (\<lambda> x. (list_ex (is_neg_inst x) ab)) ab)"

fun is_neg_rel :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> bool"  where
    "is_neg_rel (FactFm (AtomR sign r x y)) f = (f = (FactFm (AtomR (\<not> sign) r x y)))"
  | "is_neg_rel  _ f = False"

fun contains_contr_role_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool" where  
  "contains_contr_role_impl ab = (list_ex  (\<lambda> x. (list_ex (is_neg_rel x) ab)) ab)"

fun is_ineq_inst :: "('nr, 'nc, 'ni) form \<Rightarrow> bool"
  where
    "is_ineq_inst (FactFm (Eq False x y)) = (x = y)"
  | "is_ineq_inst _  = False"

fun contains_contr_eq_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool" where  
  "contains_contr_eq_impl ab = (list_ex is_ineq_inst ab)"

fun contains_falsefm_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool" where  
  "contains_falsefm_impl ab = (FalseFm \<in> set ab)"

definition contains_clash_impl :: "('ni,'nr,'nc) abox_impl \<Rightarrow> bool" where  
  "contains_clash_impl ab = 
    (contains_bottom_impl ab \<or> 
     contains_contr_concept_impl ab \<or>
     contains_contr_role_impl ab \<or>
     contains_contr_eq_impl ab \<or>
     contains_falsefm_impl ab)"
 


(**************************)

(*
definition comp11 ::"'ni \<Rightarrow> ('nr,'nc,'ni)concept \<Rightarrow>'nr \<Rightarrow> ('nr,'nc,'ni)abox \<Rightarrow> nat"
  where
  "comp11 x c r Ab \<equiv> card( (set_y_xry_in_abox x r Ab) -(set_y_c_in_abox  c Ab)) "

definition  comp12 ::" 'ni \<Rightarrow> 'nr \<Rightarrow> ('nr,'nc,'ni)abox \<Rightarrow> nat "
  where
  "comp12 x r ab = card (set_some x r ab)"

definition meas_comp:: "('nr,'nc,'ni) abox \<Rightarrow> ('nr,'nc,'ni) fact \<Rightarrow> nat*nat" 
  where
  "meas_comp ab fct =
  (case fct of 
        Inst x c \<Rightarrow> (case c of
            (ConjC c1 c2) \<Rightarrow> if conjc_applicable ab fct then (sizeC c, 0) else (0,0)
           | (DisjC c1 c2)  \<Rightarrow> if disjc_applicable ab fct then (sizeC c, 0) else (0,0)
           | (SomeC r c1) \<Rightarrow> if somec_applicable ab fct then (sizeC c, 0) else (0,0)
           | (AllC r c1)  \<Rightarrow> (sizeC c , (comp11 x c1 r ab) + (comp12 x r ab))
           |_ \<Rightarrow>(0,0)
         )
        | _ \<Rightarrow> (0,0)
       )"


definition multiset_of_abox :: "('nr,'nc,'ni)abox \<Rightarrow> (nat * nat) multiset" 
  where
  "multiset_of_abox ab \<equiv> setsum (single \<circ> (meas_comp ab)) ab"

definition measure_abox_order ::
  "(('nr, 'nc, 'ni) abox * ('nr, 'nc, 'ni) abox) set" where
  "measure_abox_order \<equiv> 
  inv_image (mult pair_less) multiset_of_abox"



definition measure_abox_impl_order ::
  "(('nr, 'nc, 'ni) abox_impl * ('nr, 'nc, 'ni) abox_impl) set" where
  "measure_abox_impl_order \<equiv> inv_image measure_abox_order set"


lemma wf_measure_abox_impl_order: "wf measure_abox_impl_order"
  by (unfold measure_abox_impl_order_def)
(intro wf_inv_image wf_measure_abox_order)
*)

(*
lemma All_dfs_dom: "All dfs_dom"
sorry
*)
section "Extraction of prover"
text{* dfs*}

  (* TODO: The last line was: else abx # dfs abxs. 
  But the runtimes were too long. Thus, currently, only one model is generated.
 *)
 (*
function dfs :: "('nr, 'nc, ('ni::{new_var_set_class})) tableau_impl \<Rightarrow> ('nr, 'nc, 'ni) tableau_impl"
  where
    "dfs [] = []"
  | "dfs (abx # abxs) = 
  (if (contains_clash_impl abx)
  then dfs abxs
  else if (is_reducible_abox alc_rule_impl abx)
         then dfs ((alc_rule_impl abx) @ abxs)
         else [abx])" 
  by pat_completeness auto

termination
by (rule All_dfs_dom)
*)
(*
  apply (relation "mult1_list measure_abox_impl_order")
  apply (intro wf_mult1_list wf_measure_abox_impl_order)
  apply (rule mult1_list_hd)
  apply (rule mult1_list_hd_replace) apply (erule alc_rule_impl_measure_abox_impl_order)
  apply (rule mult1_list_hd)
  done
*)

end



