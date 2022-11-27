(*<*)
theory Variables imports AuxilProofs Syntax
begin
(*>*)

(* ---------------------------------------------------------------------- *)
section {* Treatment of variables, in particular bound variables \label{sec:variables} *}

fun is_free :: "'ni var \<Rightarrow> bool" where
    "is_free (Free w) = True"
  | "is_free (Bound k) = False"

fun drop_var :: "nat \<Rightarrow> 'ni var \<Rightarrow> 'ni var" where
    "drop_var n (Free w) = Free w"
  | "drop_var n (Bound k) = (if n \<le> k then Bound (k - 1) else Bound k)"

fun lift_var :: "nat \<Rightarrow> 'v var \<Rightarrow> 'v var" where
   "lift_var n (Free v) = Free v"
 | "lift_var n (Bound k) = (if n \<le> k then Bound (k + 1) else Bound k)"

fun lift_subst :: "nat \<Rightarrow> ('nr, 'nc, 'ni var) subst \<Rightarrow> ('nr, 'nc, 'ni var) subst" where
    "lift_subst n (RSubst r rop (v1, v2)) = RSubst r rop (lift_var n v1, lift_var n v2)"
  | "lift_subst n (CSubst c rop v) = CSubst c rop (lift_var n v)"
  
fun lift_rename :: "nat \<Rightarrow> 'ni var rename \<Rightarrow> 'ni var rename" where  
    "lift_rename n (ISubst v v') = ISubst (lift_var n v) (lift_var n v')"

fun apply_var_subst :: "('a \<Rightarrow> 'b) \<Rightarrow> ('nr, 'nc, 'a) subst \<Rightarrow> ('nr, 'nc, 'b) subst" where
    "apply_var_subst f (RSubst r rop (v1, v2)) = RSubst r rop (f v1, f v2)"
  | "apply_var_subst f (CSubst c rop v) = CSubst c rop (f v)"
  
fun apply_var_rename :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a rename \<Rightarrow> 'b rename" where  
    "apply_var_rename f (ISubst v v') = ISubst (f v) (f v')"

lemma lift_subst_apply_var_subst:
  "lift_subst n s = apply_var_subst (lift_var n) s"
by (case_tac s, auto)

fun lift_concept :: "nat \<Rightarrow> ('nr, 'nc, 'ni var) concept \<Rightarrow> ('nr, 'nc, 'ni var) concept" where
    "lift_concept n Bottom = Bottom"
  | "lift_concept n Top = Top"
  | "lift_concept n (AtomC sign a) = (AtomC sign a)"
  | "lift_concept n (BinopC bop c1 c2) = BinopC bop (lift_concept n c1) (lift_concept n c2)"
  | "lift_concept n (NegC c) = NegC (lift_concept n c)"
  | "lift_concept n (NumRestrC nro nb r c) = (NumRestrC nro nb r (lift_concept n c))" 
  | "lift_concept n (SubstC c sb) = SubstC (lift_concept n c) (lift_subst n sb)"
  | "lift_concept n (SomeC r c) = SomeC r (lift_concept n c)"
  | "lift_concept n (AllC r c) = AllC r (lift_concept n c)"

fun apply_var_concept :: "('a \<Rightarrow> 'b) \<Rightarrow> ('nr, 'nc, 'a ) concept \<Rightarrow> ('nr, 'nc, 'b) concept" where
    "apply_var_concept f Bottom = Bottom"
  | "apply_var_concept f Top = Top"
  | "apply_var_concept f (AtomC sign a) = (AtomC sign a)"
  | "apply_var_concept f (BinopC bop c1 c2) = BinopC bop (apply_var_concept f c1) (apply_var_concept f c2)"
  | "apply_var_concept f (NegC c) = NegC (apply_var_concept f c)"
  | "apply_var_concept f (NumRestrC nro nb r c) = (NumRestrC nro nb r (apply_var_concept f c))" 
  | "apply_var_concept f (SubstC c sb) = SubstC (apply_var_concept f c) (apply_var_subst f sb)"
  | "apply_var_concept f (SomeC r c) = SomeC r (apply_var_concept f c)"
  | "apply_var_concept f (AllC r c) = AllC r (apply_var_concept f c)"

lemma lift_concept_apply_var_concept:
  "lift_concept n s = apply_var_concept (lift_var n) s"
by (induct s, auto simp add: lift_subst_apply_var_subst)

fun lift_fact :: "nat \<Rightarrow> ('nr, 'nc, 'ni var) fact \<Rightarrow> ('nr, 'nc, 'ni var) fact" where
    "lift_fact n (Inst x c) = (Inst (lift_var n x) (lift_concept n c))"
  | "lift_fact n (AtomR sign r x y) = (AtomR sign r (lift_var n x) (lift_var n y))"
  | "lift_fact n (Eq sign x y) = Eq sign (lift_var n x) (lift_var n y)"

fun apply_var_fact :: "('a \<Rightarrow> 'b) \<Rightarrow> ('nr, 'nc, 'a) fact \<Rightarrow> ('nr, 'nc, 'b) fact" where
    "apply_var_fact f (Inst x c) = (Inst (f x) (apply_var_concept f c))"
  | "apply_var_fact f (AtomR sign r x y) = (AtomR sign r (f x) (f y))"
  | "apply_var_fact f (Eq sign x y) = Eq sign (f x) (f y)"


fun apply_var_form :: "('a \<Rightarrow> 'b) \<Rightarrow> ('nr, 'nc, 'a) form \<Rightarrow> ('nr, 'nc, 'b) form" where
    "apply_var_form f (ConstFm cn) = (ConstFm cn)"
  | "apply_var_form f (FactFm fct) = FactFm (apply_var_fact f fct)"
  | "apply_var_form f (NegFm fm) = NegFm (apply_var_form f fm)"
  | "apply_var_form f (BinopFm bop fm1 fm2) = BinopFm bop (apply_var_form f fm1) (apply_var_form f fm2)"
  | "apply_var_form f (SubstFm fm sb) = (SubstFm (apply_var_form f fm) (apply_var_subst f sb))"


lemma lift_fact_apply_var_fact:
  "lift_fact n s = apply_var_fact (lift_var n) s"
by (case_tac s, auto simp add:  lift_concept_apply_var_concept)


fun lift_form :: "nat \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "lift_form n (QConstFm cn) = (QConstFm cn)"
  | "lift_form n (QFactFm fct) = QFactFm (lift_fact n fct)"
  | "lift_form n (QNegFm f) = QNegFm (lift_form n f)"
  | "lift_form n (QBinopFm bop f1 f2) = QBinopFm bop (lift_form n f1) (lift_form n f2)"
  | "lift_form n (QuantifFm q v f) = QuantifFm q v (lift_form (n+1) f)"
  | "lift_form n (QSubstFm f sb) = (QSubstFm (lift_form n f) (lift_subst n sb))"
  | "lift_form n (QRenameFm f sb) = (QRenameFm (lift_form n f) (lift_rename n sb))"

fun shuffle_right :: "binop \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "shuffle_right bop f1 (QuantifFm q v f2) = QuantifFm q v (shuffle_right bop (lift_form 0 f1) f2)"
  | "shuffle_right bop f1 f2 = QBinopFm bop f1 f2"

fun shuffle_left :: "binop \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "shuffle_left bop (QuantifFm q v f1) f2 = QuantifFm q v (shuffle_left bop f1 (lift_form 0 f2))"
  | "shuffle_left bop f1 f2 = shuffle_right bop f1 f2"

fun lift_bound_above_negfm :: "('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "lift_bound_above_negfm (QuantifFm q v f) = QuantifFm (dual_quantif False q) v (lift_bound_above_negfm f)"
  | "lift_bound_above_negfm f = QNegFm f"

fun lift_bound_above_substfm :: 
  "('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni var) subst \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "lift_bound_above_substfm (QuantifFm q v f) sb = QuantifFm q v (lift_bound_above_substfm f (lift_subst 0 sb))"
  | "lift_bound_above_substfm f sb = QSubstFm f sb"

fun lift_bound_above_renamefm :: 
  "('nr, 'nc, 'ni) qform \<Rightarrow> 'ni var rename \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "lift_bound_above_renamefm (QuantifFm q v f) sb = QuantifFm q v (lift_bound_above_renamefm f (lift_rename 0 sb))"
  | "lift_bound_above_renamefm f sb = QRenameFm f sb"

fun lift_bound :: "('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "lift_bound (QConstFm cn) = (QConstFm cn)"
  | "lift_bound (QFactFm fct) = QFactFm fct"
  | "lift_bound (QNegFm f) = lift_bound_above_negfm (lift_bound f)"
  | "lift_bound (QBinopFm bop f1 f2) = shuffle_left bop (lift_bound f1) (lift_bound f2)"
  | "lift_bound (QuantifFm q v f) = QuantifFm q v (lift_bound f)"
  | "lift_bound (QSubstFm f sb)  = (lift_bound_above_substfm (lift_bound f) sb)"
  | "lift_bound (QRenameFm f sb)  = (lift_bound_above_renamefm (lift_bound f) sb)"


definition bind :: "quantif \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
  "bind q v f = QuantifFm q v (QRenameFm (lift_form 0 f) (ISubst (Free v) (Bound 0)))"


definition bind_list:: "quantif \<Rightarrow> 'ni list \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform" where
  "bind_list = List.foldr \<circ> bind"

  (* Free variables *)

fun fv_subst :: "('nr, 'nc, 'ni) subst \<Rightarrow> 'ni set" where
    "fv_subst (RSubst r rop (v1, v2)) = {v1, v2}"
  | "fv_subst (CSubst c rop v) = {v}"

fun fv_rename :: "'ni rename \<Rightarrow> 'ni set" where  
   "fv_rename (ISubst v v') = {v'}"
  
fun fv_subst_list :: "('nr, 'nc, 'ni) subst \<Rightarrow> 'ni list" where
    "fv_subst_list (RSubst r rop (v1, v2)) = List.union [v1] [v2]"
  | "fv_subst_list (CSubst c rop v) = [v]"

fun fv_rename_list :: "'ni rename \<Rightarrow> 'ni list" where  
   "fv_rename_list (ISubst v v') = [v']"
  
lemma set_fv_subst_list [simp]: "set (fv_subst_list sb) = fv_subst sb"
apply (case_tac sb) apply simp_all
apply (rename_tac nr subst_op prod)
apply (case_tac prod) apply simp_all
apply blast
done

lemma set_fv_rename_list [simp]: "set (fv_rename_list sb) = fv_rename sb"
by (case_tac sb)  simp

fun isubst_dom :: "'ni rename \<Rightarrow> 'ni set" where
   "isubst_dom (ISubst v v') = {v}"
  
fun isubst_ran :: "'ni rename \<Rightarrow> 'ni set" where
   "isubst_ran (ISubst v v') = {v'}"
  
fun isubst_dom_list :: "'ni rename \<Rightarrow> 'ni list" where
    "isubst_dom_list (ISubst v v') = [v]"

fun fv_var_isubsts :: "'ni set \<Rightarrow> 'ni rename list \<Rightarrow> 'ni set" where
    "fv_var_isubsts vs [] = vs"
  | "fv_var_isubsts vs ((ISubst x y) # sbsts) = fv_var_isubsts (insert y (vs -{x})) sbsts"

lemma set_isubst_dom_list [simp]: "set (isubst_dom_list sb) = isubst_dom sb"
by (case_tac sb) simp_all

fun fv_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> 'ni set" where
    "fv_concept Bottom = {}"
  | "fv_concept Top = {}"
  | "fv_concept (AtomC sign a) = {}"
  | "fv_concept (BinopC bop c1 c2) = fv_concept c1 \<union> fv_concept c2"
  | "fv_concept (NegC c) = (fv_concept c)"
  | "fv_concept (NumRestrC nro n r c) = fv_concept c"
  | "fv_concept (SubstC c sb) = (fv_concept c) \<union> (fv_subst sb)"
  | "fv_concept (SomeC r c) = (fv_concept c)"
  | "fv_concept (AllC r c) = (fv_concept c)"

fun fv_concept_list :: "('nr, 'nc, 'ni) concept \<Rightarrow> 'ni list" where
    "fv_concept_list Bottom = []"
  | "fv_concept_list Top = []"
  | "fv_concept_list (AtomC sign a) = []"
  | "fv_concept_list (BinopC bop c1 c2) = List.union (fv_concept_list c1)  (fv_concept_list c2)"
  | "fv_concept_list (NegC c) = (fv_concept_list c)"
  | "fv_concept_list (NumRestrC nro n r c) = fv_concept_list c"
  | "fv_concept_list (SubstC c sb) = List.union (fv_concept_list c) (fv_subst_list sb)"
  | "fv_concept_list (SomeC r c) = (fv_concept_list c)"
  | "fv_concept_list (AllC r c) = (fv_concept_list c)"

lemma set_fv_concept_list [simp]: "set (fv_concept_list c) = fv_concept c"
  by (induct c) simp_all

fun fv_fact :: "('nr, 'nc, 'ni) fact \<Rightarrow> 'ni set" where
    "fv_fact (Inst x c) = insert x (fv_concept c)"
  | "fv_fact (AtomR sign r x y) = {x, y}"
  | "fv_fact (Eq sign x y) = {x, y}"


fun fv_fact_list :: "('nr, 'nc, 'ni) fact \<Rightarrow> 'ni list" where
    "fv_fact_list (Inst x c) = List.insert x (fv_concept_list c)"
  | "fv_fact_list (AtomR sign r x y) = List.insert x [y]"
  | "fv_fact_list (Eq sign x y) = List.insert x [y]"

lemma set_fv_fact_list [simp]: "set (fv_fact_list f) = fv_fact f"
  by (induct f) simp_all

fun fv_form :: "('nr, 'nc, 'ni) form \<Rightarrow> 'ni set" where
    "fv_form (ConstFm cn) = {}"
  | "fv_form (FactFm fct) = (fv_fact fct)"
  | "fv_form (NegFm f) = (fv_form f)"
  | "fv_form (BinopFm bop f1 f2) = (fv_form f1) \<union> (fv_form f2)"
  | "fv_form (SubstFm f sb) = (fv_form f) \<union> (fv_subst sb)"


fun fv_form_list :: "('nr, 'nc, 'ni) form \<Rightarrow> 'ni list" where
    "fv_form_list (ConstFm cn) = []"
  | "fv_form_list (FactFm fct) = (fv_fact_list fct)"
  | "fv_form_list (NegFm f) = (fv_form_list f)"
  | "fv_form_list (BinopFm bop f1 f2) = list_union (fv_form_list f1) (fv_form_list f2)"
  | "fv_form_list (SubstFm f sb) = list_union (fv_form_list f) (fv_subst_list sb)"

lemma set_fv_form_list [simp]: "set (fv_form_list f) = fv_form f"
  by (induct f) simp_all

  
fun close_quantif :: "'ni var \<Rightarrow> 'ni var" where
    "close_quantif (Free v) = Free v"
  | "close_quantif (Bound n) = Bound (n - 1)"

fun fv_qform :: "('nr, 'nc, 'ni) qform \<Rightarrow> 'ni var set" where
    "fv_qform (QConstFm cn) = {}"
  | "fv_qform (QFactFm fct) = (fv_fact fct)"
  | "fv_qform (QNegFm f) = (fv_qform f)"
  | "fv_qform (QBinopFm bop f1 f2) = (fv_qform f1) \<union> (fv_qform f2)"
  | "fv_qform (QuantifFm q v f) = close_quantif ` ((fv_qform f) - {Bound 0})"
  | "fv_qform (QSubstFm f sb) = (fv_qform f) \<union> (fv_subst sb)"
  | "fv_qform (QRenameFm f sb) = (case sb of (ISubst v1 v2) \<Rightarrow> ((fv_qform f) - {v1}) \<union> {v2})"

fun fv_qform_list :: "('nr, 'nc, 'ni) qform \<Rightarrow> 'ni var list" where
    "fv_qform_list (QConstFm cn) = []"
  | "fv_qform_list (QFactFm fct) = (fv_fact_list fct)"
  | "fv_qform_list (QNegFm f) = (fv_qform_list f)"
  | "fv_qform_list (QBinopFm bop f1 f2) = list_union (fv_qform_list f1) (fv_qform_list f2)"
  | "fv_qform_list (QuantifFm q v f) = List.map close_quantif (list_remove (fv_qform_list f) [Bound 0])"
  | "fv_qform_list (QSubstFm f sb) = list_union (fv_qform_list f) (fv_subst_list sb)"
  | "fv_qform_list (QRenameFm f sb) = (case sb of (ISubst v1 v2) \<Rightarrow> list_union (list_remove (fv_qform_list f) [v1]) [v2])"

definition "is_closed_qform fm = (\<forall> v \<in> (fv_qform fm). is_free v)"

lemma set_fv_qform_list [simp]: "set (fv_qform_list f) = fv_qform f"
  by (induct f) (auto simp add: rename.split_asm)

fun is_quantif_free :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> bool" where 
    "is_quantif_free (QConstFm cn) = True"
  | "is_quantif_free (QFactFm f) = True"
  | "is_quantif_free (QNegFm f) = (is_quantif_free f)"
  | "is_quantif_free (QBinopFm bop f1 f2) = ((is_quantif_free f1) \<and> (is_quantif_free f2))"
  | "is_quantif_free (QuantifFm q v f) = False"
  | "is_quantif_free (QSubstFm f sb) = (is_quantif_free f)"
  | "is_quantif_free (QRenameFm f sb) = (is_quantif_free f)"

fun is_prenex_form :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> bool" where 
    "is_prenex_form (QConstFm cn) = True"
  | "is_prenex_form (QFactFm f) = True"
  | "is_prenex_form (QNegFm f) = (is_quantif_free f)"
  | "is_prenex_form (QBinopFm bop f1 f2) = ((is_quantif_free f1) \<and> (is_quantif_free f2))"
  | "is_prenex_form (QuantifFm q v f) = is_prenex_form f"
  | "is_prenex_form (QSubstFm f sb) = (is_quantif_free f)"
  | "is_prenex_form (QRenameFm f sb) = (is_quantif_free f)"

fun quantif_depth :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> nat" where 
    "quantif_depth (QConstFm cn) = 0"
  | "quantif_depth (QFactFm f) = 0"
  | "quantif_depth (QNegFm f) = quantif_depth f"
  | "quantif_depth (QBinopFm bop f1 f2) = (max (quantif_depth f1) (quantif_depth f2))"
  | "quantif_depth (QuantifFm q v f) = (quantif_depth f) + 1"
  | "quantif_depth (QSubstFm f sb) = quantif_depth f"
  | "quantif_depth (QRenameFm f sb) = quantif_depth f"
  
fun qform_of_form :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "qform_of_form (ConstFm cn) = (QConstFm cn)"
  | "qform_of_form (FactFm fct) = QFactFm (apply_var_fact Free fct)"
  | "qform_of_form (NegFm f) = QNegFm (qform_of_form f)"
  | "qform_of_form (BinopFm bop f1 f2) = QBinopFm bop (qform_of_form f1) (qform_of_form f2)"
  | "qform_of_form (SubstFm f sb) = (QSubstFm (qform_of_form f) (apply_var_subst Free sb))"

fun name_of_free :: "'ni var \<Rightarrow> 'ni" where
    "name_of_free (Free v) = v"

  (* The qforms passed as argument are supposed to be quantifier-free, 
     without bound variables, and without renames *)
fun form_of_qform :: "('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "form_of_qform (QConstFm cn) = (ConstFm cn)"
  | "form_of_qform (QFactFm fct) = FactFm (apply_var_fact name_of_free fct)"
  | "form_of_qform (QNegFm f) = NegFm (form_of_qform f)"
  | "form_of_qform (QBinopFm bop f1 f2) = BinopFm bop (form_of_qform f1) (form_of_qform f2)"
  | "form_of_qform (QSubstFm f sb) = (SubstFm (form_of_qform f) (apply_var_subst name_of_free sb))"

(*<*)
end
(*>*)
