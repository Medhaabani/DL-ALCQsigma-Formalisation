(* CURRENTLY NOT USED *)

theory ProofTrace imports ALC_SoundnessProofs (* ALC_CompletenessProofs *) ALC_Implementation

begin
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* TODO: all the following included from theory ALC_Completeness *)

definition saturated_abox :: "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> bool" where
  "saturated_abox ab1 r \<equiv> \<forall> ab2. \<not> r ab1 ab2"


  (* Apply rule to abox if possible, otherwise keep abox *)
definition conserv_appl :: "('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> ('ni,'nr,'nc) abox set" where
 "conserv_appl ab1 r = (if saturated_abox ab1 r then {ab1} else  {ab2. r ab1 ab2})" 
  
 
definition apply_tableau_rule1 :: "('ni,'nr,'nc) rule \<Rightarrow> ('ni,'nr,'nc) abox \<Rightarrow> ('ni,'nr,'nc) tableau \<Rightarrow> ('ni,'nr,'nc) tableau" where
 "apply_tableau_rule1 r ab tb = (tb - {ab}) \<union> {ab2. r ab ab2}" 
  
definition apply_tableau_rule :: "('ni,'nr,'nc) tableau \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> ('ni,'nr,'nc) tableau" where
 "apply_tableau_rule tb r = (\<Union> ab \<in> tb. conserv_appl ab r)"
  
 (* saturated: application of a rule yields no new tableau *)
definition saturated_tableau :: "('ni,'nr,'nc) tableau \<Rightarrow> ('ni,'nr,'nc) rule \<Rightarrow> bool" where
  "saturated_tableau tb r \<equiv> (apply_tableau_rule tb r = tb)"

  (* complete means: no loss of models *)
definition complete ::"('nr, 'nc, 'ni) rule \<Rightarrow> bool" where 
  "complete r \<equiv> \<forall> a1. satisfiable a1 \<longrightarrow> \<not> (saturated_abox a1 r) \<longrightarrow>  (\<exists> a2. r a1 a2 \<and> satisfiable a2)"

  (* TODO: end all  included from theory ALC_Completeness *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(*--------------------------------------------------------------------------*)
(* Experiments with rules *)

type_synonym ('nr, 'nc, 'ni) indiv_rule = "('nr,'nc,'ni) form \<Rightarrow> ('nr,'nc,'ni) rule" 


inductive  conjc_rule_indiv :: "('nr, 'nc, 'ni) indiv_rule" where
  mk_conjc_rule_indiv: "\<lbrakk>f = FactFm (Inst x (ConjC c1 c2)); f \<in> ab1;
  ab2 = {FactFm (Inst x c2), FactFm (Inst x c1)} \<union> ab1\<rbrakk> \<Longrightarrow> conjc_rule_indiv f ab1 ab2" 

inductive_cases conjc_rule_indiv_cases[elim!]: "conjc_rule_indiv f ab1 ab2"

  
definition conjc_rule_tcond :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
"conjc_rule_tcond f ab = (\<exists> x c1 c2. FactFm (Inst x (ConjC c1 c2)) = f \<and> f \<in> ab \<and>
  \<not> (FactFm (Inst x c1) \<in> ab \<and> FactFm (Inst x c2) \<in> ab))"
  
 
inductive  conjc_rule_indiv_termin :: "('nr, 'nc, 'ni) indiv_rule" where
  mk_conjc_rule_indiv_termin: "\<lbrakk>f = FactFm (Inst x (ConjC c1 c2)); f \<in> ab1;
  \<not> (FactFm (Inst x c1) \<in> ab1 \<and> FactFm (Inst x c2) \<in> ab1);
  ab2 = {FactFm (Inst x c2), FactFm (Inst x c1)} \<union> ab1\<rbrakk> \<Longrightarrow> conjc_rule_indiv_termin f ab1 ab2" 
  
inductive_cases conjc_rule_indiv_termin_cases[elim!]: "conjc_rule_indiv_termin f ab1 ab2"

  
lemma conjc_rule_indiv_rewr: "conjc_rule_indiv f ab1 ab2 =
(\<exists> x c1 c2. 
f = FactFm (Inst x (ConjC c1 c2))  \<and> f \<in> ab1 \<and>
  ab2 = {FactFm (Inst x c2), FactFm (Inst x c1)} \<union> ab1)"
  apply (rule iffI)
apply (erule conjc_rule_indiv_cases) apply fastforce
apply clarsimp
apply (fastforce intro: mk_conjc_rule_indiv)
done
  
definition terminating_indiv_rule  :: 
"('nr, 'nc, 'ni) indiv_rule \<Rightarrow> 
(('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool) \<Rightarrow>
('nr, 'nc, 'ni) indiv_rule" where
"terminating_indiv_rule indiv_r tcond = (\<lambda> f ab1 ab2. (tcond f ab1) \<and> indiv_r f ab1 ab2)"

lemma schlong: "conjc_rule_indiv_termin = (terminating_indiv_rule conjc_rule_indiv conjc_rule_tcond)"
apply (clarsimp simp add: fun_eq_iff)
apply (rename_tac f ab1 ab2)
apply (rule iffI)

apply (clarsimp simp add: terminating_indiv_rule_def)
apply (simp add: conjc_rule_tcond_def)
apply (rule mk_conjc_rule_indiv)
apply (rule refl)
apply assumption+
apply simp

apply (clarsimp simp add: terminating_indiv_rule_def conjc_rule_indiv_rewr)

apply (rule mk_conjc_rule_indiv_termin)
apply fastforce+
apply  (simp add: conjc_rule_tcond_def)+
done

definition general_rule ::
  "('nr, 'nc, 'ni) indiv_rule \<Rightarrow>  ('nr, 'nc, 'ni) rule" where
"general_rule indiv_r = (\<lambda> ab1 ab2. (\<exists> f. indiv_r f ab1 ab2))"

definition "conjc_rule_new = (general_rule (terminating_indiv_rule conjc_rule_indiv conjc_rule_tcond))"
  
lemma "conjc_rule b1 b2 \<Longrightarrow>  (general_rule conjc_rule_indiv_termin) b1 b2"
apply (simp add:conjc_rule_def)
apply (erule conjc_rule_indiv_cases)
apply (erule conjc_applicable_cases)
apply (simp add: general_rule_def)
apply (rule exI)
apply (fastforce mintro: mk_conjc_rule_indiv_termin)
done

lemma "(general_rule conjc_rule_indiv_termin) b1 b2 \<Longrightarrow> conjc_rule b1 b2 "
apply (clarsimp simp add: general_rule_def)
apply (rule mk_conjc_rule)
apply (fastforce intro: App_conjc_blck)+
done

definition  sound_indiv :: "('nr, 'nc, 'ni) indiv_rule \<Rightarrow> bool" where 
  "sound_indiv indiv_r \<equiv> \<forall> f A1 A2. indiv_r f A1 A2 \<longrightarrow> satisfiable A2 \<longrightarrow> satisfiable A1"
  
lemma sound_indiv_conjc_rule_indiv: "sound_indiv conjc_rule_indiv"
by (fastforce simp add: sound_indiv_def satisfiable_def)

lemma sound_conjc_rule_indiv: "sound (conjc_rule_indiv f)"
by (fastforce simp add: sound_def satisfiable_def)


lemma conjc_rule_complete [simp]: "complete conjc_rule" 
  apply (clarsimp simp add: complete_def saturated_abox_def)
   apply  (fastforce elim: conjc_rule_cases simp add: satisfiable_def)
done

lemma complete_conjc_rule_indiv: "complete (conjc_rule_indiv f)"
  apply (simp add: complete_def saturated_abox_def)
  apply (clarsimp del: conjc_rule_indiv_cases)
  apply (intro conjI exI)
  apply assumption
  apply  (fastforce simp add: satisfiable_def)
done

(*
apply 




lemma conjc_rule_indiv_sound [simp]: "sound (conjc_rule_indiv f)"
  by (fastforce elim: conjc_rule_indiv_cases simp add: sound_def satisfiable_def)
  
lemma conjc_rule_indiv_complete: "complete (conjc_rule_indiv f)"
  apply simp
  apply (clarsimp simp add: complete_def saturated_abox_def)
  apply  (fastforce elim: conjc_rule_indiv_cases simp add: satisfiable_def)
done
*)

inductive conjc_rule2 :: "('nr, 'nc, 'ni) rule" where 
mk_conjc_rule2 : "conjc_rule_indiv f ab1 ab2 \<Longrightarrow> conjc_rule2 ab1 ab2"

inductive_cases conjc_rule2_cases: "conjc_rule2 ab1 ab2"

(* The other direction does not hold, because conjc_rule2 does not have a blocking condition *)
lemma "conjc_rule ab1 ab2 \<Longrightarrow> conjc_rule2 ab1 ab2"
apply (erule conjc_rule_cases)
apply (erule conjc_applicable_cases)
apply (rule mk_conjc_rule2)
apply (rule mk_conjc_rule_indiv)
apply (rule refl)
apply assumption
apply simp
done

(*--------------------------------------------------------------------------*)

datatype ('nr, 'nc, 'ni) rule_rep =
     Clash_rep
   | AndRule_rep "('nr, 'nc, 'ni) form"
   | OrRule_rep "('nr, 'nc, 'ni) form"
   | ConjRule_rep "('nr, 'nc, 'ni) form"
   | DisjRule_rep "('nr, 'nc, 'ni) form"

datatype ('nr, 'nc, 'ni) trace = 
  Trace "(('nr, 'nc, 'ni) rule_rep)" "(('nr, 'nc, 'ni) trace list)"

definition refines_abox :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
"refines_abox abi ab = (ab = (set abi))"


fun impl_action_and :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) abox_impl list" where
  "impl_action_and (FactFm (Inst x (ConjC c1 c2))) ab_i = 
            [[FactFm (Inst x c1), FactFm (Inst x c2)] @ ab_i]"
 | "impl_action_and _ ab_i = []"

fun and_appcond_form ::  "('nr, 'nc, 'ni) form \<Rightarrow> bool" where
  "and_appcond_form (FactFm (Inst x (ConjC c1 c2)) ) = True" 
 |"and_appcond_form _ = False"
 
lemma and_appcond_form_charact: "(and_appcond_form f) = (\<exists> x c1 c2. f = (FactFm (Inst x (ConjC c1 c2)) ))"
apply (rule iffI)
apply (erule and_appcond_form.elims)
apply clarsimp+
done
 
definition "and_appcond_impl f ab_i = ((f \<in> set ab_i) \<and> and_appcond_form f)"

fun exec_rule_rep :: "('nr, 'nc, 'ni) rule_rep \<Rightarrow> ('nr, 'nc, 'ni) rule_impl" where
  "exec_rule_rep (AndRule_rep f) ab_i = 
     (if and_appcond_impl f ab_i
      then impl_action_and f ab_i
      else [])"

consts accept_trace_leaf :: "('nr, 'nc, 'ni) abox_impl \<Rightarrow> ('nr, 'nc, 'ni) rule_rep \<Rightarrow> bool" 



fun accept_trace :: "('nr, 'nc, 'ni) trace \<Rightarrow> ('nr, 'nc, 'ni) abox_impl \<Rightarrow>  bool" where
  "accept_trace (Trace rr []) ab_i = accept_trace_leaf ab_i rr"
| "accept_trace (Trace rr trcs) ab_i = list_all2 accept_trace trcs (exec_rule_rep rr ab_i)"

thm accept_trace.induct

      
(*----------------------------------------------------------*)
   (* Simulation of rules and rule representations*)
definition rule_sim_rule_rep :: "('nr, 'nc, 'ni) rule_rep \<Rightarrow> ('nr, 'nc, 'ni) rule \<Rightarrow> bool" where
"rule_sim_rule_rep rrep rl = 
(\<forall> ab_i ab. (refines_abox ab_i ab) \<longrightarrow> 
   (\<forall> ab_i' \<in> set (exec_rule_rep rrep ab_i). (\<exists> ab'. (rl ab ab') \<and> (refines_abox ab_i' ab'))))" 

lemma "rule_sim_rule_rep (AndRule_rep f) (conjc_rule_indiv f)"
apply (clarsimp simp add: rule_sim_rule_rep_def and_appcond_impl_def)
apply (clarsimp simp add: and_appcond_form_charact)
apply (clarsimp simp add: refines_abox_def)
apply (fast intro: mk_conjc_rule_indiv)
done

definition rule_rep_sim_rule :: "('nr, 'nc, 'ni) rule_rep \<Rightarrow> ('nr, 'nc, 'ni) rule \<Rightarrow> bool" where
"rule_rep_sim_rule rrep rl = 
(\<forall> ab_i ab. (refines_abox ab_i ab) \<longrightarrow> 
   (\<forall> ab'. (rl ab ab') \<longrightarrow> (\<exists> ab_i' \<in> set (exec_rule_rep rrep ab_i). (refines_abox ab_i' ab'))))" 
   
lemma "rule_rep_sim_rule (AndRule_rep f) (conjc_rule_indiv f)"
apply (clarsimp simp add: rule_rep_sim_rule_def and_appcond_impl_def)
apply (fastforce simp add: refines_abox_def)
done

(*----------------------------------------------------------*)


(*=================================================================*)
(* All the rest: Can be deleted *)

lemma and_appcond_conjc_applicable: "conjc_applicable ab f \<Longrightarrow> and_appcond f ab"
by (clarsimp simp add: conjc_applicable_simp and_appcond_def)

(* This direction does not hold (missing blocking condition) *)
lemma and_appcond_conjc_applicable: "and_appcond f ab \<Longrightarrow> conjc_applicable ab f"
oops
(*
apply (clarsimp simp add: conjc_applicable_simp and_appcond_def)
apply (case_tac f) apply simp_all
apply (case_tac fact) apply simp_all
apply (case_tac concept) apply simp_all
apply (case_tac binop) apply simp_all
apply clarsimp
done
*)

fun and_effect ::  "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> ('nr, 'nc, 'ni) abox list" where
  "and_effect (FactFm (Inst x (ConjC c1 c2))) ab = 
     [{FactFm (Inst x c2), FactFm (Inst x c1)} \<union> ab]"  
 |"and_effect _ ab = [ab]"

lemma "and_appcond ((FactFm (Inst x (ConjC c1 c2)))) ab \<Longrightarrow> 
    (and_effect (FactFm (Inst x (ConjC c1 c2))) ab) = [{FactFm (Inst x c2), FactFm (Inst x c1)} \<union> ab]"
    by (clarsimp simp add: and_appcond_conjc_applicable conjc_applicable_simp)

definition 
 "lift_appcond_and_effect appc eff ab = 
     (if appc ab then eff ab else [ab])"
     
fun rule_rep_interp::  "('nr, 'nc, 'ni) rule_rep  \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> ('nr, 'nc, 'ni) abox list" where
  "rule_rep_interp (AndRule_rep f) = lift_appcond_and_effect (and_appcond f) (and_effect f)"  

definition complete_expansion :: "('nr, 'nc, 'ni) abox \<Rightarrow> ('nr, 'nc, 'ni) abox list \<Rightarrow> bool" where 
  "complete_expansion ab abxs = 
     (satisfiable ab \<longrightarrow> (\<exists> ab' \<in> set abxs. satisfiable ab'))"
  
lemma complete_rule_complete_expansion:
  "complete r \<Longrightarrow> \<not> saturated_abox ab r \<Longrightarrow> set abxs = Collect (r ab) \<Longrightarrow> complete_expansion ab abxs"
by (clarsimp simp add: complete_def complete_expansion_def)
(*
apply (drule_tac x=ab1 in spec)
apply simp
apply (case_tac "saturated_abox ab1 r")
apply clarsimp
apply (simp add: saturated_abox_def)
apply clarsimp
*)

lemma complete_expansion_same [simp]: "complete_expansion ab [ab]"
by (simp add: complete_expansion_def)

(*
lemma complete_expansion_not_appc:
  "\<not> (appc ab) \<Longrightarrow> complete_expansion ab (lift_appcond_and_effect appc eff ab)"
by (simp add: lift_appcond_and_effect_def)
*)

lemma complete_expansion_lift:
   "complete r \<Longrightarrow> 
    (appc ab \<Longrightarrow> \<not> saturated_abox ab r) \<Longrightarrow>
    (appc ab \<Longrightarrow> set (eff ab) = {ab'. r ab ab'}) \<Longrightarrow>
    complete_expansion ab (lift_appcond_and_effect appc eff ab)"
by (clarsimp simp add: lift_appcond_and_effect_def)
   (fast intro: complete_rule_complete_expansion)

   
lemma complete_rule_complete_expansion2:
  "complete r \<Longrightarrow> \<not> saturated_abox ab r \<Longrightarrow> 
  Collect (r ab) \<subseteq> set abxs  \<Longrightarrow> complete_expansion ab abxs"
by (fastforce simp add: complete_def complete_expansion_def)

   
lemma complete_expansion_lift2:
   "complete r \<Longrightarrow> 
    (appc ab \<Longrightarrow> \<not> saturated_abox ab r) \<Longrightarrow>
    (appc ab \<Longrightarrow> Collect (r ab) \<subseteq> set (eff ab)) \<Longrightarrow> 
    complete_expansion ab (lift_appcond_and_effect appc eff ab)"
by (clarsimp simp add: lift_appcond_and_effect_def) (fast intro: complete_rule_complete_expansion2)


lemma foobar: "conjc_applicable ab (FactFm (Inst x (ConjC c1 c2))) \<Longrightarrow> 
       {{FactFm (Inst x c2), FactFm (Inst x c1)} \<union> ab} \<subseteq> Collect (conjc_rule ab)"
apply (frule mk_conjc_rule)
apply (rule refl)
apply (simp add: set_eq_subset)
done

lemma complete_expansion_and:
  "complete_expansion ab (lift_appcond_and_effect (and_appcond f) (and_effect f) ab)"
apply (rule complete_expansion_lift)
apply (rule conjc_rule_indiv_complete [where f=f])
apply (simp add: and_appcond_conjc_applicable conjc_applicable_simp)
apply (simp add: saturated_abox_def)
apply clarsimp
apply (intro exI mk_conjc_rule_indiv)
apply simp+

apply (simp add: and_appcond_conjc_applicable)
apply (clarsimp simp add: conjc_applicable_simp)
apply (simp add: conjc_rule_indiv.simps)
done


lemma "complete_expansion ab (rule_rep_interp rr ab)"
apply (case_tac rr)
apply (simp only: rule_rep_interp.simps complete_expansion_and)
done

end

