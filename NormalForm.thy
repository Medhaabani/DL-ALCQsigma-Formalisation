(*<*)
theory NormalForm imports Semantics
begin
(*>*)

section {* Normal Forms *}

fun neg_norm_concept :: "bool \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) concept"  where 
    "neg_norm_concept sign Bottom = (if sign then Bottom else Top)"
  | "neg_norm_concept sign Top = (if sign then Top else Bottom)"
  | "neg_norm_concept sign (AtomC asign a) = (AtomC (interp_sign sign asign) a)"
  | "neg_norm_concept sign (BinopC bop c1 c2) = (BinopC (dual_binop sign bop) (neg_norm_concept sign c1) (neg_norm_concept sign c2))"
  | "neg_norm_concept sign (NegC c) = (neg_norm_concept (\<not> sign) c)"
  | "neg_norm_concept sign (NumRestrC nro n r c) = (NumRestrC (dual_numres_ord sign nro) n r (neg_norm_concept True c))"
  | "neg_norm_concept sign (SubstC c sb) = (SubstC (neg_norm_concept sign c) sb)"
  | "neg_norm_concept sign (SomeC r c) = (if sign then (SomeC r (neg_norm_concept sign c)) else (AllC r (neg_norm_concept sign c)))"
  | "neg_norm_concept sign (AllC r c) = (if sign then (AllC r (neg_norm_concept sign c)) else (SomeC r (neg_norm_concept sign c)))"

fun neg_norm_fact :: "bool \<Rightarrow> ('nr, 'nc, 'ni) fact \<Rightarrow> ('nr, 'nc, 'ni) fact"  where 
    "neg_norm_fact sign (Inst x c) = (Inst x (neg_norm_concept sign c))"
  | "neg_norm_fact sign (AtomR sign' r x y) = (AtomR (interp_sign sign sign') r x y)"
  | "neg_norm_fact sign (Eq sign' x y) = (Eq (interp_sign sign sign') x y)"

fun neg_norm_form :: "bool \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) form"  where 
    "neg_norm_form sign (ConstFm cn) = (ConstFm (interp_sign sign cn))"
  | "neg_norm_form sign (FactFm f) = (FactFm (neg_norm_fact sign f))"
  | "neg_norm_form sign (NegFm f) = (neg_norm_form (\<not> sign) f)"
  | "neg_norm_form sign (BinopFm bop f1 f2) = (BinopFm (dual_binop sign bop) (neg_norm_form sign f1) (neg_norm_form sign f2))"
  | "neg_norm_form sign (SubstFm f sb) = (SubstFm (neg_norm_form sign f) sb)"

fun neg_norm_qform :: "bool \<Rightarrow> ('nr, 'nc, 'ni) qform \<Rightarrow> ('nr, 'nc, 'ni) qform"  where 
    "neg_norm_qform sign (QConstFm cn) = (QConstFm (interp_sign sign cn))"
  | "neg_norm_qform sign (QFactFm f) = (QFactFm (neg_norm_fact sign f))"
  | "neg_norm_qform sign (QNegFm f) = (neg_norm_qform (\<not> sign) f)"
  | "neg_norm_qform sign (QBinopFm bop f1 f2) = (QBinopFm (dual_binop sign bop) (neg_norm_qform sign f1) (neg_norm_qform sign f2))"
  | "neg_norm_qform sign (QuantifFm q v f) = (QuantifFm (dual_quantif sign q) v (neg_norm_qform sign f))"
  | "neg_norm_qform sign (QSubstFm f sb) = (QSubstFm (neg_norm_qform sign f) sb)"
  | "neg_norm_qform sign (QRenameFm f sb) = (QRenameFm (neg_norm_qform sign f) sb)"
  
definition nnf_IfThenElseFm :: 
  "(('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form)" where 
  "nnf_IfThenElseFm c a b = neg_norm_form True (IfThenElseFm c a b)"

fun is_neg_norm_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> bool" where
   "is_neg_norm_concept (AtomC sign x) = True"
  |"is_neg_norm_concept Top = True"
  |"is_neg_norm_concept Bottom = True" 
  |"is_neg_norm_concept (NegC c) = False"
  |"is_neg_norm_concept (BinopC bop c1 c2) = (is_neg_norm_concept c1 \<and>  is_neg_norm_concept c2)"
  |"is_neg_norm_concept (NumRestrC nro n r c) = is_neg_norm_concept c"
  |"is_neg_norm_concept (SubstC c sb) = is_neg_norm_concept c"
  |"is_neg_norm_concept (AllC  r c) = is_neg_norm_concept c"
  |"is_neg_norm_concept (SomeC r c) = is_neg_norm_concept c"


fun  is_neg_norm_fact ::"('nr, 'nc, 'ni) fact \<Rightarrow> bool" where
    "is_neg_norm_fact (Inst x c) = is_neg_norm_concept c"
  | "is_neg_norm_fact (AtomR  sign  r x y) = True"
  | "is_neg_norm_fact (Eq sign  x y) = True"
  
fun  is_neg_norm_form ::"('nr, 'nc, 'ni) form \<Rightarrow> bool" where
    "is_neg_norm_form (ConstFm cn) = True"
  | "is_neg_norm_form (FactFm fct)= is_neg_norm_fact fct"
  | "is_neg_norm_form (NegFm f) = False"
  | "is_neg_norm_form (BinopFm bop f1 f2) = (is_neg_norm_form f1 \<and>  is_neg_norm_form f2)"
  | "is_neg_norm_form (SubstFm f sb) =  is_neg_norm_form f"

fun  is_neg_norm_qform ::"('nr, 'nc, 'ni) qform \<Rightarrow> bool" where
    "is_neg_norm_qform (QConstFm cn) = True"
  | "is_neg_norm_qform (QFactFm fct)= is_neg_norm_fact fct"
  | "is_neg_norm_qform (QNegFm f) = False"
  | "is_neg_norm_qform (QBinopFm bop f1 f2) = (is_neg_norm_qform f1 \<and>  is_neg_norm_qform f2)"
  | "is_neg_norm_qform (QuantifFm q v f) = is_neg_norm_qform f"
  | "is_neg_norm_qform (QSubstFm f sb) =  is_neg_norm_qform f"
  
(*<*)
end
(*>*)
