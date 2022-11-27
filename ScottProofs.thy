theory ScottProofs imports PredicateLogic
begin

(* To be completed and deeply modified after correcting PredicateLogic *)


(* ######################### WELL-FORMED FO² FOMULAS ######################### *)

(* For now, no formulas with Free() variables are allowed. *)

(* Check if every bound variable (De Bruijn index) corresponds to a previous quantifier,
   and if every bound variable is build with the Bound() constructor. *)
fun well_formed_bound_vars :: "('nR, 'ni) plform \<Rightarrow> nat \<Rightarrow> 'ni set \<Rightarrow> bool" where
    "well_formed_bound_vars (PlConstFm b) _ _ = True"
  | "well_formed_bound_vars (PlRel b r []) _ _ = True"
  | "well_formed_bound_vars (PlRel b r ((Bound h)#t) ) n bv = ( (h\<le>n) \<and> (well_formed_bound_vars (PlRel b r t) n bv) )"
(*| "well_formed_bound_vars (PlRel b r ((Free h)#t)) n bv = ((h\<notin>bv) \<and> (well_formed_bound_vars (PlRel b r t) n bv))" *)
  | "well_formed_bound_vars (PlRel b r ((Free h)#t)) n bv = False"
  | "well_formed_bound_vars (PlNegFm f) n bv = (well_formed_bound_vars f n bv)"
  | "well_formed_bound_vars (PlBinopFm _ f g) n bv = ((well_formed_bound_vars f n bv) \<and> (well_formed_bound_vars g n bv))"
  | "well_formed_bound_vars (PlQuantifFm _ x f) n bv = (well_formed_bound_vars f (n+1) (insert x bv))"

(* Check if a formula only uses two variables. *)
fun two_variables :: "('nR, 'ni) plform \<Rightarrow> 'ni set \<Rightarrow> bool" where
(*  "two_variables (PlConstFm _) fv = ((card fv) \<le> 2)" *)
(*| "two_variables (PlRel _ _ []) fv = ((card fv) \<le> 2)" *)
    "two_variables (PlConstFm _) fv = ((card fv) \<le> 0)"
  | "two_variables (PlRel _ _ []) fv = ((card fv) \<le> 0)"
(******************************  T H I S  L I N E   I S  W R O N G !  ****************************)
  | "two_variables (PlRel b r ((Bound h)#t)) fv = ((h<2) \<and> (two_variables (PlRel b r t) fv))"
(**************************************************^^^^^******************************************)
(*| "two_variables (PlRel b r ((Free h)#t)) fv = (two_variables (PlRel b r t) (insert h fv))" *)
  | "two_variables (PlRel b r ((Free h)#t)) fv = False"
  | "two_variables (PlNegFm f) fv = (two_variables f fv)"
  | "two_variables (PlBinopFm _ f g) fv = ((two_variables f fv) \<and> (two_variables g fv))"
  | "two_variables (PlQuantifFm _ x f) fv = (two_variables f fv)"

fun well_formed_FO2_formula :: "('nR, 'ni) plform \<Rightarrow> bool" where
"well_formed_FO2_formula \<phi> = (
    well_formed_bound_vars \<phi> 0 {}
  \<and> two_variables \<phi> {}
)"

abbreviation wfFO2 where "wfFO2 \<equiv> well_formed_FO2_formula"

fun two_variables_fv_list :: "nat list \<Rightarrow> bool" where
    " two_variables_fv_list [] = True "
  | " two_variables_fv_list (0#l) = two_variables_fv_list l "
  | " two_variables_fv_list ((Suc 0)#l) = two_variables_fv_list l "
  | " two_variables_fv_list _ = False "



(********** PlImplFm ***********)

lemma [simp] :
"wfFO2 (PlImplFm f g) = (wfFO2 f \<and> wfFO2 g)"
   by fastforce


(*********** pl_to_pl_form ***********)

lemma [simp] :
"\<forall>n s r b. (well_formed_bound_vars (PlRel b r v) n s \<longrightarrow> well_formed_bound_vars (PlRel b (Orig r) v) n s)"
  apply(induct_tac v, auto) 
  apply(case_tac a, auto)
  done
lemma [simp] :
"\<forall>n s. (well_formed_bound_vars \<phi> n s \<longrightarrow> well_formed_bound_vars (pl_to_scott_pl \<phi>) n s)"
  apply(induct_tac \<phi>, auto) done


lemma [simp] :
"\<forall>n s r b. (two_variables (PlRel b r v) s \<longrightarrow> two_variables (PlRel b (Orig r) v) s)"
  apply(induct_tac v, auto)
  apply(case_tac a, auto) 
  done
lemma [simp] :
"\<forall>s. two_variables \<phi> s \<longrightarrow> two_variables (pl_to_scott_pl \<phi>) s"
  apply(induct_tac \<phi>, auto) done


proposition "wfFO2 \<phi> \<longrightarrow> wfFO2 (pl_to_scott_pl \<phi>)"
  apply(auto) done


(*********** scott_preprocessing ***********)

lemma [simp] :
"\<forall>n s. well_formed_bound_vars \<phi> n s \<longrightarrow> well_formed_bound_vars (scott_preprocessing \<phi>) n s"
  apply(induct_tac \<phi>, auto)
  sorry


lemma [simp] :
"\<forall>s. two_variables (scott_preprocessing f) s \<longrightarrow> two_variables (scott_preprocessing g) s
 \<longrightarrow> two_variables (scott_preprocessing (PlBinopFm bop f g)) s"
  apply(case_tac f, auto)
  apply(case_tac g, auto)
  apply(case_tac bop, auto)
  proof -
    fix x51 :: quantif and x52 :: 'a and x53 :: "('b scott_rel, 'a) plform" and s :: "'a set" and x51a :: quantif and x52a :: 'a and x53a :: "('b scott_rel, 'a) plform"
    assume a1: "f = PlQuantifFm x51 x52 x53"
    assume a2: "two_variables (scott_preprocessing (PlQuantifFm x51 x52 x53)) s"
    assume a3: "two_variables (scott_preprocessing (PlQuantifFm x51a x52a x53a)) s"
    assume a4: "g = PlQuantifFm x51a x52a x53a"
    then have f5: "PlQuantifFm QEx x52a x53a = g \<or> x51a = QAll"
      by (metis quantif.exhaust)
    have "PlQuantifFm QEx x52 x53 = f \<or> x51 = QAll"
      using a1 by (metis (full_types) quantif.exhaust)
    then show "two_variables (scott_preprocessing (PlBinopFm Conj (PlQuantifFm x51 x52 x53) (PlQuantifFm x51a x52a x53a))) s"
      using f5 a4 a3 a2 a1 by force
  next
    fix x51 :: quantif and x52 :: 'a and x53 :: "('b scott_rel, 'a) plform" and s :: "'a set" and x51a :: quantif and x52a :: 'a and x53a :: "('b scott_rel, 'a) plform"
    assume a1: "f = PlQuantifFm x51 x52 x53"
    assume a2: "two_variables (scott_preprocessing (PlQuantifFm x51 x52 x53)) s"
    assume a3: "two_variables (scott_preprocessing (PlQuantifFm x51a x52a x53a)) s"
    assume a4: "g = PlQuantifFm x51a x52a x53a"
    then have f5: "PlQuantifFm QAll x52a x53a = g \<or> x51a = QEx"
      by (metis quantif.exhaust)
    have "PlQuantifFm QAll x52 x53 = f \<or> x51 = QEx"
      using a1 by (metis (full_types) quantif.exhaust)
    then show "two_variables (scott_preprocessing (PlBinopFm Disj (PlQuantifFm x51 x52 x53) (PlQuantifFm x51a x52a x53a))) s"
      using f5 a4 a3 a2 a1 by force
  qed
lemma [simp] :
"\<forall>x s. two_variables (scott_preprocessing f) s 
           \<longrightarrow> two_variables (scott_preprocessing (PlQuantifFm Q x f)) s"
  apply(case_tac Q, auto)
  done
lemma [simp] :
"\<forall>s. two_variables \<phi> s \<longrightarrow> two_variables (scott_preprocessing \<phi>) s"
  apply(induct_tac \<phi>, auto)
  done


proposition "wfFO2 \<phi> \<longrightarrow> wfFO2 (scott_preprocessing \<phi>)"
  apply(auto) done


(*********** fv_atomic **********)

proposition "\<forall>b r. (two_variables (PlRel b r v) {}) = (length(fv_atomic (PlRel b r v)) \<le> 2)"
  sorry
(* ! ! ! Correct the fv_atomic function ! ! ! *)


(********** forallize ***********)

proposition [simp] :
"(length fv) \<le> (length bv) \<longrightarrow> (length bv) \<le> 2 \<longrightarrow> two_variables f {}
       \<longrightarrow> two_variables (forallize f bv fv 0) {}"
  apply(case_tac fv, auto)
  apply(case_tac bv, auto)
  apply(case_tac list, auto)
  apply(case_tac lista, auto)
  done


(********** scott_reduction_theta ***********)

lemma [simp] : 
"wfFO2 (scott_reduction_theta_PlConstFm b p)"
  by fastforce


lemma [simp] :
"(length fv) \<le> (length bv) \<longrightarrow> (length bv) \<le> 2 \<longrightarrow> wfFO2 (PlRel b r v) \<longrightarrow> two_variables_fv_list fv
 \<longrightarrow> wfFO2 (scott_reduction_theta_PlRel b r v p bv fv)"
  apply(case_tac fv, simp)
  apply(case_tac bv, simp)
  sorry


lemma [simp] :
"(length fv) \<le> (length bv) \<longrightarrow> (length bv) \<le> 2 \<longrightarrow> two_variables_fv_list fv
 \<longrightarrow> wfFO2 (scott_reduction_theta_PlNegFm p bv fv)"
  apply(case_tac fv, simp)
  apply(case_tac bv, simp)
  sorry


lemma [simp] :
"(length fv ) \<le> (length bv) \<longrightarrow> two_variables_fv_list fv  \<longrightarrow> 
 (length fv') \<le> (length bv) \<longrightarrow> two_variables_fv_list fv' \<longrightarrow> (length bv) \<le> 2 
 \<longrightarrow> wfFO2 (scott_reduction_theta_PlBinopFm bop p bv fv fv')"
  apply(case_tac fv, simp)
  apply(case_tac fv', simp)
  apply(case_tac bv, simp)
  sorry


lemma [simp] :
"(length fv) \<le> (length bv) \<longrightarrow> two_variables_fv_list fv \<longrightarrow> (length bv) \<le> 2 
 \<longrightarrow> wfFO2 (scott_reduction_theta_PlQuantifFm x p bv fv)"
  apply(induct_tac bv, simp)
  apply(case_tac fv, simp)
  sorry



(* ######################### PRESERVATION OF SATISFIABILITY ######################### *)





end