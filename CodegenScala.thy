(*<*)
theory CodegenScala imports Hoare ALC_Checker Finite_Set
  SubstProofs (* TODO: SubstProofs temporary, for code extraction *) 
  (*ProofTrace*)
  ALC_PrInfrastruc ALC_ImplementationProofs PredicateLogic
  "~~/src/HOL/Library/Code_Target_Numeral" String

  (* "~~/src/HOL/Library/Efficient_Nat"   
  library does not seem to exist any more*)
begin
(*>*)

code_printing
  code_module "pack" \<rightharpoonup> (Scala) {*package isa*}
code_reserved Scala pack

definition init_tableau_triple :: 
"(String.literal, String.literal, String.literal) form \<Rightarrow>
(String.literal, String.literal, String.literal) stmt \<Rightarrow>
(String.literal, String.literal, String.literal) form \<Rightarrow>
(String.literal, String.literal, String.literal) form list" where
 "init_tableau_triple pre c post =
  (let vcs = extract_vcs (qform_of_form pre) c (qform_of_form post) in
   let neg_prenex_f = (neg_norm_form False (free_prenex_form_list_string vcs)) in 
   [neg_prenex_f])" 

definition is_inactive_string :: 
  "(String.literal, String.literal, String.literal) proofbranch \<Rightarrow> bool" where
"is_inactive_string br = is_inactive br"

fun failed_subproof :: 
   "('a, 'b, 'c) prooftrace \<Rightarrow> ('a, 'b, 'c) trace_constr list \<Rightarrow> ('a, 'b, 'c) trace_constr list option" where
  "failed_subproof current [] = Some [CTrace current]"
| "failed_subproof current ((ITrace subtrs  n rr) # traces) = 
    (if 1 + length subtrs = n 
    then failed_subproof (Trace rr (List.rev (current#subtrs))) traces
    else Some ((ITrace (current#subtrs) n rr)#traces))"
| "failed_subproof current _ = None"


   (*
code_identifier
   (*code_module Nat \<rightharpoonup> (Scala) NatC *)
   type_constructor nat \<rightharpoonup> (Scala) natc 

   and
   
*)

(*

code_printing
constant Nat  \<rightharpoonup> (Scala) "natc" 
  type_constructor nat \<rightharpoonup> (Scala) "nat" 
  | 
*)

  
export_code vc neg_norm_form free_prenex_form_list_string list_union fv_form_list fv_qform_list 
  rename_in_form push_subst_form remdups neg_norm_concept
  ConstFm BinopC Conj QBinopFm SDiff Free Nat QAll RSubst Lt Inst Skip
  integer_of_nat nat_of_integer qform_of_form wp_dl extract_vcs
  equal_class.equal ord_class.less_eq new_var_list_class_class.new_var_list
  (*and_effect and_appcond*)
  fresh_string_literal
  Branch Inactive_form all_forms Clash_rep TablUnsatisf Trace CTrace AppRes
  classify_new apply_permanent apply_splitting apply_linear contains_clash_branch is_inactive
  apply_rules_pt init_tableau_triple failed_subproof
  (* the following for testing only, can be removed *)
  numrestrc_lt_applicable_vars_branch choose_applicable_vars_branch
  is_inactive_string (* interp_form *)
  canon_interp_impl 
  interp_impl_i interp_impl_c interp_impl_r interp_impl_c_i interp_impl_r_i interp_impl_i_c
  PlQuantifFm (* qform_to_plform*)
  PlConstFm nth
  in Scala 
  module_name VerifCondition file "VerifCondition.scala"

(*<*)
end
(*>*)
