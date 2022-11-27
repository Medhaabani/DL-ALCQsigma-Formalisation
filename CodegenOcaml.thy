(*<*)
theory CodegenOcaml imports Hoare ALC_Checker Finite_Set
  SubstProofs (* TODO: SubstProofs temporary, for code extraction *) 
  (*ProofTrace*)
  ALC_PrInfrastruc
  "~~/src/HOL/Library/Code_Target_Numeral" String

  (* "~~/src/HOL/Library/Efficient_Nat"   
  library does not seem to exist any more*)
begin
(*>*)

export_code vc neg_norm_form free_prenex_form_list_string list_union fv_form_list fv_qform_list 
  push_isubst_form push_subst_form remdups neg_norm_concept
  ConstFm BinopC Conj QBinopFm SDiff Free Nat QAll RSubst Lt Inst Skip
  integer_of_nat nat_of_integer qform_of_form wp_dl extract_vcs
  equal_class.equal ord_class.less_eq new_var_list_class_class.new_var_list
  (*and_effect and_appcond*)
  fresh_string_literal
  Branch Inactive_form all_forms Clash_rep TablUnsatisf Trace CTrace AppRes
  classify_new apply_permanent apply_splitting apply_linear contains_clash_branch is_inactive
  apply_rules_pt
  (* the following for testing only, can be removed *)
  numrestrc_lt_applicable_vars choose_applicable_vars
  in OCaml 
  module_name VerifCondition file "../Transfo_DL_ocaml/Ocaml/verif_condition.ml"

(*<*)
end
(*>*)
