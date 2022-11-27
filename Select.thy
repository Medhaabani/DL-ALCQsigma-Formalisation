theory Select imports Proglang SubstProofs
begin

(*---------------------------------------------------------------------*)
(* Implementation of select_set functions *)
fun interp_sign_set :: "bool \<Rightarrow> 'a set \<Rightarrow> 'a set" where
 "interp_sign_set sign A = (if sign then A else - A)"

fun select_set_fact :: "'i \<Rightarrow> ('r, 'c, 'i) fact \<Rightarrow> ('d, 'r, 'c, 'i) Interp \<Rightarrow> 'd set" where
  "select_set_fact v (Inst x c) g = 
      (if v = x 
      then (interp_concept c g) 
      else if (interp_i g x) \<in> (interp_concept c g)
      then UNIV
      else {})"
| "select_set_fact v (AtomR sign r x y) g =
      (if (v = x) 
       then (if (v = y) 
             then (interp_sign_set sign {z. (z, z) \<in> interp_r g r}) 
             else (interp_sign_set sign {z. (z, interp_i g y) \<in> interp_r g r})) 
       else (if (v = y) 
       then (interp_sign_set sign {z. (interp_i g x, z) \<in> interp_r g r})
       else (if ((interp_i g x, interp_i g y) \<in> interp_r g r) 
             then (interp_sign_set sign UNIV) 
             else (interp_sign_set sign {}))))"
| "select_set_fact v (Eq sign x y) g = 
      (if (v = x) 
       then (if (v = y) 
             then (interp_sign_set sign UNIV) 
             else (interp_sign_set sign {interp_i g y})) 
       else (if (v = y) 
       then (interp_sign_set sign {interp_i g x})
       else (if (interp_i g x) = (interp_i g y) 
             then (interp_sign_set sign UNIV) 
             else (interp_sign_set sign {}))))"

fun select_set_form :: "'i \<Rightarrow> ('r, 'c, 'i) form \<Rightarrow> ('d, 'r, 'c, 'i) Interp \<Rightarrow> 'd set" where
  "select_set_form v (ConstFm cn) g = (if cn then UNIV else {})"
| "select_set_form v (FactFm f) g = select_set_fact v f g"
| "select_set_form v (NegFm f) g = - (select_set_form v f g)"
| "select_set_form v (BinopFm Conj f1 f2) g =  (select_set_form v f1 g) \<inter> (select_set_form v f2 g)"
| "select_set_form v (BinopFm Disj f1 f2) g =  (select_set_form v f1 g) \<union> (select_set_form v f2 g)"
| "select_set_form v (SubstFm f sb) g = {}" (* irrelevant *)

(*---------------------------------------------------------------------*)
(* Auxiliary defs for proofs *)

fun subst_free_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> bool" where
    "subst_free_concept Bottom = True"
  | "subst_free_concept Top = True"
  | "subst_free_concept (AtomC sign a) = True"
  | "subst_free_concept (BinopC bop c1 c2) = (subst_free_concept c1 \<and> subst_free_concept c2)"
  | "subst_free_concept (NegC c) = (subst_free_concept c)"
  | "subst_free_concept (NumRestrC nro n r c) = (subst_free_concept c)"
  | "subst_free_concept (SubstC c sb) = False"
  | "subst_free_concept (SomeC r c) = (subst_free_concept c)"
  | "subst_free_concept (AllC r c) = (subst_free_concept c)"

fun subst_free_fact :: "('nr, 'nc, 'ni) fact \<Rightarrow> bool" where
    "subst_free_fact (Inst x c) = subst_free_concept c"
  | "subst_free_fact (AtomR sign r x y) = True"
  | "subst_free_fact (Eq sign x y) = True"

fun subst_free_form :: "('nr, 'nc, 'ni) form \<Rightarrow> bool" where
    "subst_free_form (ConstFm cn) = True"
  | "subst_free_form (FactFm fct) = subst_free_fact fct"
  | "subst_free_form (NegFm f) = subst_free_form f"
  | "subst_free_form (BinopFm bop f1 f2) = (subst_free_form f1 \<and> subst_free_form f2)"
  | "subst_free_form (SubstFm f sb) = False"

lemma subst_free_interp_concept [rule_format, simp]:
"subst_free_concept c \<longrightarrow> interp_concept c (interp_i_modif ni vi s) = interp_concept c s" 
by (induct c) auto

lemma interp_select_set_fact [simp, rule_format]: 
  "subst_free_fact f \<longrightarrow>
  (select_set_fact v f g) = {vi. (interp_fact f (interp_i_modif v vi g))}"
apply (induct f)
(* Inst *)
apply clarsimp
(* AtomR *)
apply (clarsimp simp add: interp_i_modif_def)
apply fastforce
(* Eq *)
apply (clarsimp simp add: interp_i_modif_def)
apply fastforce
done

lemma interp_select_set_form [simp]: 
"subst_free_form f \<longrightarrow> 
(select_set_form v f g) = {vi.  (interp_form f (interp_i_modif v vi g))}"
apply (induct f)
apply simp
apply simp
apply clarsimp
apply fastforce
apply (rename_tac binop f1 f2)
apply (case_tac binop)
apply fastforce
apply fastforce
apply simp
done

end
