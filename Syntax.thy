(*<*)
theory Syntax imports Main
begin
(*>*)

section {* Syntax of the $\cal ALCQ$ logic *}

datatype subst_op = SDiff | SAdd

datatype ('nr, 'nc, 'ni) subst = 
    RSubst "'nr" subst_op "('ni * 'ni)" 
  | CSubst "'nc" subst_op "'ni" 
  
datatype 'ni rename = ISubst "'ni" "'ni" 

datatype numres_ord = Lt | Ge
datatype binop = Conj | Disj    (*  | Impl *)
datatype quantif = QAll | QEx

fun interp_sign :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "interp_sign sign b = (if sign then b else (\<not> b))"

fun dual_numres_ord :: "bool \<Rightarrow> numres_ord \<Rightarrow> numres_ord" where
    "dual_numres_ord sign Lt = (if sign then Lt else Ge)"
  | "dual_numres_ord sign Ge = (if sign then Ge else Lt)"

  (* the clause for Impl is just for completeness *)
fun dual_binop :: "bool \<Rightarrow> binop \<Rightarrow> binop" where
    "dual_binop sign Conj = (if sign then Conj else Disj)"
  | "dual_binop sign Disj = (if sign then Disj else Conj)"

fun dual_quantif :: "bool \<Rightarrow> quantif \<Rightarrow> quantif" where
    "dual_quantif sign QAll = (if sign then QAll else QEx)"
  | "dual_quantif sign QEx =  (if sign then QEx else QAll)"

datatype ('nr, 'nc, 'ni) concept =
    Top  
  | Bottom
  | AtomC bool 'nc
  | NegC  "(('nr, 'nc, 'ni) concept)"
  | BinopC  binop "(('nr, 'nc, 'ni) concept)" "(('nr, 'nc, 'ni) concept)"
  | NumRestrC "(numres_ord)" "(nat)" "'nr" "(('nr, 'nc, 'ni) concept)"
  | SubstC "(('nr, 'nc, 'ni) concept)" "(('nr, 'nc, 'ni) subst)" (* explicit substitution of a role name by role expr. *)
  | SomeC "'nr" "(('nr, 'nc, 'ni) concept)"
  | AllC "'nr" "(('nr, 'nc, 'ni) concept)"

abbreviation ConjC :: "(('nr, 'nc, 'ni) concept) \<Rightarrow> (('nr, 'nc, 'ni) concept) \<Rightarrow> (('nr, 'nc, 'ni) concept)" where 
  "ConjC c1 c2 == (BinopC Conj c1 c2)"

abbreviation DisjC :: "(('nr, 'nc, 'ni) concept) \<Rightarrow> (('nr, 'nc, 'ni) concept) \<Rightarrow> (('nr, 'nc, 'ni) concept)" where 
  "DisjC c1 c2 == (BinopC Disj c1 c2)"

abbreviation atleast ("([\<ge>] _ _ _)" [60,60,60] 60) where
  "atleast n r c  == (NumRestrC Ge n r c)"

abbreviation atmost_strict ("([<] _ _ _)" [60,60,60] 60) where 
  "atmost_strict n r c  == (NumRestrC Lt n r c)" 

(* TODO: Temporarily as constructors for integration with ALC tableau prover. Remove in the long run.
definition SomeC :: "'nr \<Rightarrow> (('nr, 'nc, 'ni) concept) \<Rightarrow> (('nr, 'nc, 'ni) concept)" where 
  "SomeC r c = (NumRestrC Ge 1 r c)"

definition AllC :: "'nr \<Rightarrow> (('nr, 'nc, 'ni) concept) \<Rightarrow> (('nr, 'nc, 'ni) concept)" where 
  "AllC r c = (NumRestrC Lt 1 r (NegC c))"
*)

datatype ('nr, 'nc, 'ni) fact  = 
    Inst "('ni)" "(('nr, 'nc, 'ni) concept)"
  | AtomR bool  "('nr)" "('ni)" "('ni)"
  | Eq bool "'ni" "'ni"


  (* Formulas without quantification *)
datatype ('nr, 'nc, 'ni) form = 
    ConstFm bool
  | FactFm "(('nr, 'nc, 'ni) fact)"
  | NegFm "(('nr, 'nc, 'ni) form)"
  | BinopFm binop "(('nr, 'nc, 'ni) form)" "(('nr, 'nc, 'ni) form)"
  | SubstFm "(('nr, 'nc, 'ni) form)" "(('nr, 'nc, 'ni) subst)" 

datatype 'v var = 
    Free 'v
  | Bound nat

  -- "Quantified formulas"

datatype ('nr, 'nc, 'ni) qform = 
    QConstFm bool
  | QFactFm "(('nr, 'nc, 'ni var) fact)"
  | QNegFm "(('nr, 'nc, 'ni) qform)"
  | QBinopFm binop "(('nr, 'nc, 'ni) qform)" "(('nr, 'nc, 'ni) qform)"
  | QuantifFm quantif "('ni)" "(('nr, 'nc, 'ni) qform)"
  | QSubstFm "(('nr, 'nc, 'ni) qform)" "(('nr, 'nc, 'ni var) subst)" 
  | QRenameFm "(('nr, 'nc, 'ni) qform)" "('ni var rename)" 

abbreviation TrueFm :: "(('nr, 'nc, 'ni) form)" where 
  "TrueFm == (ConstFm True)"
abbreviation FalseFm :: "(('nr, 'nc, 'ni) form)" where 
  "FalseFm == (ConstFm False)"

abbreviation ConjFm :: "(('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form)" where 
  "ConjFm a b == (BinopFm Conj a b)"
abbreviation DisjFm :: "(('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form)" where 
  "DisjFm a b == (BinopFm Disj a b)"
abbreviation ImplFm :: "(('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form)" where 
  "ImplFm a b == (BinopFm Disj (NegFm a) b)"

definition IfThenElseFm :: 
  "(('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) form)" where 
  "IfThenElseFm c a b = ConjFm (ImplFm c a) (ImplFm (NegFm c) b)"

abbreviation AllFm :: "'ni \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform)" where 
  "AllFm v f == (QuantifFm QAll v f)"
abbreviation ExFm :: "'ni \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform)" where 
  "ExFm v f == (QuantifFm QEx v f)"

abbreviation QConjFm :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform)" where 
  "QConjFm a b == (QBinopFm Conj a b)"
abbreviation QDisjFm :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform)" where 
  "QDisjFm a b == (QBinopFm Disj a b)"
abbreviation QImplFm :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform)" where 
  "QImplFm a b == (QBinopFm Disj (QNegFm a) b)"
definition QIfThenElseFm :: 
  "(('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> (('nr, 'nc, 'ni) qform)" where 
  "QIfThenElseFm c a b = QConjFm (QImplFm c a) (QImplFm (QNegFm c) b)"
abbreviation QTrueFm :: "(('nr, 'nc, 'ni) qform)" where 
  "QTrueFm == (QConstFm True)"
abbreviation QFalseFm :: "(('nr, 'nc, 'ni) qform)" where 
  "QFalseFm == (QConstFm False)"

    (* ----------------------------------------------------------------------  *)
    (* Facts or formulas of a specific shape *)

  -- "Formula f is only universally quantified"
fun is_univ_quantif :: "bool \<Rightarrow> (('nr, 'nc, 'ni) qform) \<Rightarrow> bool" where 
    "is_univ_quantif pos (QConstFm cn) = True"
  | "is_univ_quantif pos (QFactFm f) = True"
  | "is_univ_quantif pos (QNegFm f) = (is_univ_quantif (\<not> pos) f)"
  | "is_univ_quantif pos (QBinopFm bop f1 f2) = ((is_univ_quantif pos f1) \<and> (is_univ_quantif pos f2))"
  | "is_univ_quantif pos (QuantifFm q v f) = ((dual_quantif pos q = QAll) \<and> is_univ_quantif pos f)"
  | "is_univ_quantif pos (QSubstFm f sb) = (is_univ_quantif pos f)"
  | "is_univ_quantif pos (QRenameFm f sb) = (is_univ_quantif pos f)"

fun is_fact :: "('nr, 'nc, 'ni) form \<Rightarrow> bool" where 
  "is_fact fn = (case fn of 
    FactFm f \<Rightarrow> True
  | _ \<Rightarrow> False)"

  (* fn is instance fact with instance in xs *)
fun is_Inst_fact :: "'ni set \<Rightarrow> (('nr, 'nc, 'ni) form) \<Rightarrow> bool" where 
  "is_Inst_fact xs fn = (case fn of 
    FactFm (Inst x c) \<Rightarrow> (x \<in> xs)
  | _ \<Rightarrow> False)"
  
fun is_Eq_fact :: "('nr, 'nc, 'ni) form \<Rightarrow> bool" where 
  "is_Eq_fact fn = (case fn of 
    FactFm (Eq b x y) \<Rightarrow> True
  | _ \<Rightarrow> False)"

definition "is_atomic_concept_fact s fn = (case fn of 
    FactFm (Inst x (AtomC sign a)) \<Rightarrow> (sign \<in> s)
  | _ \<Rightarrow> False)"

definition "is_atomic_role_fact s fn = (case fn of 
    FactFm (AtomR sign r x y) \<Rightarrow> (sign \<in> s)
  | _ \<Rightarrow> False)"

  (* c is number restriction concept with restr relation in nros and relation in rs *)
definition "is_NumRestrC_concept nros rs c = (case c of
    (NumRestrC nro n r c') \<Rightarrow> (nro \<in> nros \<and> r \<in> rs)
  | _ \<Rightarrow> False)"


definition "inst_of_Inst_fact fn = (case fn of 
    FactFm (Inst x c) \<Rightarrow> x)"

fun concept_of_Inst_fact :: "(('nr, 'nc, 'ni) form) \<Rightarrow> ('nr, 'nc, 'ni) concept" where 
 "concept_of_Inst_fact fn = (case fn of 
    FactFm (Inst x c) \<Rightarrow> c)"

definition "insts_of_atomic_role fn = (case fn of 
    FactFm (AtomR sign r x y) \<Rightarrow> (x, y))"

definition "concept_of_atomic_fact fn = (case fn of 
    FactFm (Inst x (AtomC sign a)) \<Rightarrow> a)"

definition "concept_of_atomic_fact_signed fn = (case fn of 
    FactFm (Inst x (AtomC sign a)) \<Rightarrow> (sign, a))"

definition "role_of_atomic_fact fn = (case fn of 
    FactFm (AtomR sign r x y) \<Rightarrow> r)"

definition "concept_of_NumRestrC_concept c = (case c of
    (NumRestrC nro n r c) \<Rightarrow> c)"

fun sub_concepts :: "('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) concept set"  where
    "sub_concepts Bottom = {Bottom}"
  | "sub_concepts Top = {Top}"
  | "sub_concepts (AtomC sign a) = {AtomC sign a}"
  | "sub_concepts (BinopC bop c1 c2) = insert (BinopC bop c1 c2) (sub_concepts c1) \<union> (sub_concepts c2)"
  | "sub_concepts (NegC c)  = insert (NegC c) (sub_concepts c)"
  | "sub_concepts (NumRestrC nro n r c)  = insert (NumRestrC nro n r c) (sub_concepts c)"
  | "sub_concepts (SubstC c sb) = insert (SubstC c sb) (sub_concepts c)"
  | "sub_concepts (SomeC r c) = insert (SomeC r c) (sub_concepts c)"
  | "sub_concepts (AllC r c) = insert (AllC r c) (sub_concepts c)"
 
    (* Positive-negative subconcepts   *)

fun sub_concepts_pn :: "('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) concept set"  where
    "sub_concepts_pn Bottom = {Bottom, Top}"
  | "sub_concepts_pn Top = {Top, Bottom}"
  | "sub_concepts_pn (AtomC sign a) = {AtomC False a, AtomC True a}"
  | "sub_concepts_pn (BinopC bop c1 c2) = 
      (let sc1s =  (sub_concepts_pn c1) in 
       let sc2s =  (sub_concepts_pn c2) in 
       (\<Union> sc1 \<in> sc1s. \<Union> sc2 \<in> sc2s. {BinopC bop sc1 sc2, BinopC  (dual_binop False bop) sc1 sc2} \<union> sc1s \<union> sc2s))" 
  | "sub_concepts_pn (NegC c)  =  (let scs =  (sub_concepts_pn c) in (NegC ` scs) \<union> scs)"
  | "sub_concepts_pn (NumRestrC nro n r c)  = 
        (let scs =  (sub_concepts_pn c) in 
         (NumRestrC nro n r) ` scs \<union> (NumRestrC (dual_numres_ord False nro) n r) ` scs \<union> scs)"
  | "sub_concepts_pn (SubstC c sb) = 
        (let scs =  (sub_concepts_pn c) in (\<lambda> c. (SubstC c sb)) ` scs \<union> scs)"
  | "sub_concepts_pn (SomeC r c) = 
        (let scs =  (sub_concepts_pn c) in (SomeC r) ` scs \<union> (AllC r) ` scs \<union> scs)"
  | "sub_concepts_pn (AllC r c) = 
        (let scs =  (sub_concepts_pn c) in (SomeC r) ` scs \<union> (AllC r) ` scs \<union> scs)"

(*<*)
end
(*>*)


