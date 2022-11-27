(*<*)
theory Semantics imports Variables Auxil Card
begin
(*>*)
section {* Semantics of  $\mathcal{ALCQ}$ \label{sec:semantics} *}

record ('d, 'nr, 'nc, 'ni) Interp =
  interp_d :: "'d set" 
  interp_c :: "'nc \<Rightarrow> 'd set "
  interp_r :: "'nr \<Rightarrow>  ('d  * 'd) set"
  interp_i :: "'ni \<Rightarrow> 'd"



fun interpRO_r :: "subst_op \<Rightarrow> 'nr \<Rightarrow> ('ni * 'ni) \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d * 'd) set" where
    "interpRO_r SDiff r (x, y) i = (interp_r i r) - {(interp_i i x, interp_i i y)}"
  | "interpRO_r SAdd r (x, y) i = insert (interp_i i x, interp_i i y) (interp_r i r)"

fun interpRO_c :: "subst_op \<Rightarrow> 'nc \<Rightarrow> 'ni \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> 'd set" where
    "interpRO_c SDiff c v i = (interp_c i c) - {interp_i i v}"
  | "interpRO_c SAdd  c v i = insert (interp_i i v) (interp_c i c)"

fun interp_numres_ord :: "numres_ord \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
    "interp_numres_ord Lt = card_lt"
  | "interp_numres_ord Ge = card_ge"

definition interp_i_modif :: "'ni \<Rightarrow> 'd \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp" where
  "interp_i_modif x xi i = i\<lparr>interp_i := (interp_i i)(x := xi) \<rparr>"

definition interp_c_modif :: "'nc \<Rightarrow> 'd set \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp" where
  "interp_c_modif c ci i = i\<lparr>interp_c := (interp_c i)(c := ci) \<rparr>"

definition interp_r_modif :: "'nr \<Rightarrow> ('d * 'd) set \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp" where
  "interp_r_modif r ri i = i\<lparr>interp_r := (interp_r i)(r := ri) \<rparr>"
  
fun interp_i_modif_list :: "('ni * 'd) list \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp" where
    "interp_i_modif_list [] i = i"
  | "interp_i_modif_list (m # mods) i = interp_i_modif_list mods (interp_i_modif (fst m) (snd m) i)"

fun interp_subst :: "('nr, 'nc, 'ni) subst \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp"  where
    "interp_subst (RSubst r rop p) i = (interp_r_modif r (interpRO_r rop r p i) i)"
  | "interp_subst (CSubst c rop v) i = (interp_c_modif c (interpRO_c rop c v i) i)"
  
fun interp_rename :: "'ni rename \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp"  where  
    "interp_rename (ISubst v v') i = (interp_i_modif v (interp_i i v') i)"

fun interp_subst_closure :: "('nr, 'nc, 'ni) subst list \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp" where
    "interp_subst_closure [] i = i"
  | "interp_subst_closure (sb # sbsts) i = interp_subst sb (interp_subst_closure sbsts i)"
  
fun interp_rename_closure :: "'ni rename list \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow>  ('d, 'nr, 'nc, 'ni) Interp" where
    "interp_rename_closure [] i = i"
  | "interp_rename_closure (sb # sbsts) i = interp_rename sb (interp_rename_closure sbsts i)"

fun interp_binopC :: "binop \<Rightarrow> 'd set \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "interp_binopC Conj d1 d2 = (d1 \<inter> d2)"
| "interp_binopC Disj d1 d2 = (d1 \<union> d2)"

fun interp_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> 'd set"  where
    "interp_concept Bottom i = {}"
  | "interp_concept Top i = interp_d i"
  | "interp_concept (AtomC sign a) i = (if sign then (interp_c i a) else interp_d i - (interp_c i a))"
  | "interp_concept (BinopC bop c1 c2) i = interp_binopC bop (interp_concept c1 i) (interp_concept c2 i)"
  | "interp_concept (NegC c) i = interp_d i - (interp_concept c i)"
  | "interp_concept (NumRestrC nro n r c) i = 
        {x \<in> interp_d i. interp_numres_ord nro (Range (rel_restrict (interp_r i r) {x} (interp_concept c i))) n}" 
  | "interp_concept (SubstC c sb) i = interp_concept c (interp_subst sb i)"
  | "interp_concept (SomeC r c) i = 
        {x \<in> interp_d i. interp_numres_ord Ge (Range (rel_restrict (interp_r i r) {x} (interp_concept c i))) 1}" 
  | "interp_concept (AllC r c) i = 
        {x \<in> interp_d i. interp_numres_ord Lt (Range (rel_restrict (interp_r i r) {x} (- (interp_concept c i)))) 1}" 


fun interp_fact :: "('nr, 'nc, 'ni) fact \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> bool" where
    "interp_fact (Inst x c) i = ((interp_i i x) \<in> (interp_concept c i))"
  | "interp_fact (AtomR sign r x y) i = 
           (if sign
            then ((interp_i i x, interp_i i y) \<in> (interp_r i r))
            else ((interp_i i x, interp_i i y) \<notin> (interp_r i r)))"
  | "interp_fact (Eq sign x y) i =
           (if sign
            then ((interp_i i x) = (interp_i i y))
            else ((interp_i i x) \<noteq> (interp_i i y)))"

fun interp_binopFm :: "binop \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "interp_binopFm Conj d1 d2 = (d1 \<and> d2)"
| "interp_binopFm Disj d1 d2 = (d1 \<or> d2)"


definition interp_bound :: "'d \<Rightarrow> ('d, 'nr, 'nc, 'ni var) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni var) Interp" where
  "interp_bound xi i = i\<lparr>interp_i :=  ((interp_i i) \<circ> (drop_var 0))(Bound 0 := xi) \<rparr>"

fun interp_form :: "('nr, 'nc, 'ni) form \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> bool" where
    "interp_form (ConstFm cn) i = cn"
  | "interp_form (FactFm f) i = interp_fact f i"
  | "interp_form (NegFm f) i = (\<not> (interp_form f i))"
  | "interp_form (BinopFm bop f1 f2) i = (interp_binopFm bop (interp_form f1 i) (interp_form f2 i))"
  | "interp_form (SubstFm f sb) i = (interp_form f) (interp_subst sb i)"

fun interp_qform :: "('nr, 'nc, 'ni) qform \<Rightarrow> ('d, 'nr, 'nc, 'ni var) Interp \<Rightarrow> bool" where
    "interp_qform (QConstFm cn) i = cn"
  | "interp_qform (QFactFm f) i = interp_fact f i"
  | "interp_qform (QNegFm f) i = (\<not> (interp_qform f i))"
  | "interp_qform (QBinopFm bop f1 f2) i = (interp_binopFm bop (interp_qform f1 i) (interp_qform f2 i))"
  | "interp_qform (QuantifFm QAll v f) i = (\<forall> xi \<in> interp_d i. interp_qform f (interp_bound xi i))"
  | "interp_qform (QuantifFm QEx v f) i = (\<exists> xi \<in> interp_d i. interp_qform f (interp_bound xi i))"
  | "interp_qform (QSubstFm f sb) i = (interp_qform f) (interp_subst sb i)"
  | "interp_qform (QRenameFm f sb) i = (interp_qform f) (interp_rename sb i)"

definition "lift_impl a b = (\<lambda> s. a s \<longrightarrow> b s)"
definition "lift_ite c a b = (\<lambda> s. if c s then a s else b s)"

definition well_formed_interp :: "('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> bool" where
  "well_formed_interp i = 
     (interp_d i \<noteq> {} \<and>
      (\<forall> c. interp_c i c \<subseteq> interp_d i) \<and> 
      (\<forall> r. interp_r i r \<subseteq> (interp_d i \<times> interp_d i)) \<and>
      (\<forall> x. interp_i i x \<in> interp_d i))" 

definition valid_form :: "(('nr, 'nc, 'ni) form) \<Rightarrow> bool" where
  "valid_form f \<equiv> (\<forall> i:: (('d, 'nr, 'nc, 'ni) Interp). well_formed_interp i \<longrightarrow> (interp_form f i))"
definition valid_qform :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> bool" where
  "valid_qform f \<equiv> (\<forall> i::(('d, 'nr, 'nc, 'ni var) Interp). well_formed_interp i \<longrightarrow>(interp_qform f i))"


  (* ------------------------------------------------------------  *)
  (* Update operations *)
  (* ------------------------------------------------------------  *)

  (* state transformers for adding / deleting nodes and edges *)

  (* add / delete a node from a concept *)
definition delete_node :: "'ni \<Rightarrow> 'nc \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp"
where "delete_node v c s = 
  s \<lparr> interp_c := (interp_c s)(c:= (interp_c s c) - {interp_i s v}) \<rparr>"

definition add_node :: "'ni \<Rightarrow> 'nc \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp"
where "add_node v c s = 
  s \<lparr> interp_c := (interp_c s)(c:= insert (interp_i s v) (interp_c s c)) \<rparr>"


  (* add / delete an edge between two nodes *)
definition delete_edge :: "'ni \<Rightarrow> 'nr \<Rightarrow> 'ni \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp"
where "delete_edge v1 r v2 s = 
  s \<lparr> interp_r := (interp_r s)(r:= (interp_r s r) - { (interp_i s v1, interp_i s v2) }) \<rparr>"

definition add_edge :: "'ni \<Rightarrow> 'nr \<Rightarrow> 'ni \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp \<Rightarrow> ('d, 'nr, 'nc, 'ni) Interp"
where "add_edge v1 r v2 s = 
  s \<lparr> interp_r := (interp_r s)(r:= insert (interp_i s v1, interp_i s v2) (interp_r s r)) \<rparr>"


(*<*)
end
(*>*)
