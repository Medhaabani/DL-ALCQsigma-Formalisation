(*<*)
theory Subst imports Syntax Variables NormalForm
begin
(*>*)

section {* Explicit substitutions  \label{sec:subst} *}


  (* ----------------------------------------------------------------------  *)
subsection {* Moving substitutions further downwards *}
  (* ----------------------------------------------------------------------  *)
  
fun push_rsubst_concept_numrestrc :: 
  "subst_op \<Rightarrow> ('ni * 'ni) \<Rightarrow> 'ni \<Rightarrow> numres_ord \<Rightarrow> nat \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) concept 
    \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_rsubst_concept_numrestrc SAdd (v1, v2) x Lt 0 r c = FalseFm"
  | "push_rsubst_concept_numrestrc SAdd (v1, v2) x Ge 0 r c = TrueFm"
  | "push_rsubst_concept_numrestrc SAdd (v1, v2) x nro (Suc n) r c = 
     (nnf_IfThenElseFm (ConjFm (ConjFm
        (FactFm (Eq True x v1)) 
        (FactFm (Inst v2 (SubstC c (RSubst r SAdd (v1, v2))))))
        (FactFm (AtomR False r v1 v2)))
      (FactFm (Inst x (NumRestrC nro n r (SubstC c (RSubst r SAdd (v1, v2))))))
      (FactFm (Inst x (NumRestrC nro (Suc n) r (SubstC c (RSubst r SAdd (v1, v2)))))))"
  | "push_rsubst_concept_numrestrc SDiff (v1, v2) x nro n r c = 
     (nnf_IfThenElseFm (ConjFm (ConjFm
        (FactFm (Eq True x v1)) 
        (FactFm (Inst v2 (SubstC c (RSubst r SDiff (v1, v2))))))
        (FactFm (AtomR True r v1 v2)))
      (FactFm (Inst x (NumRestrC nro (Suc n) r (SubstC c (RSubst r SDiff (v1, v2))))))
      (FactFm (Inst x (NumRestrC nro n r (SubstC c (RSubst r SDiff (v1, v2)))))))"

fun push_rsubst_concept_somec :: 
  "subst_op \<Rightarrow> ('ni * 'ni) \<Rightarrow> 'ni \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_rsubst_concept_somec SDiff (v1, v2) x r c = 
     (nnf_IfThenElseFm (ConjFm (ConjFm
        (FactFm (Eq True x v1)) 
        (FactFm (Inst v2 (SubstC c (RSubst r SDiff (v1, v2))))))
        (FactFm (AtomR True r v1 v2)))
      (FactFm (Inst x ([\<ge>] (Suc (Suc 0)) r (SubstC c (RSubst r SDiff (v1, v2))))))
      (FactFm (Inst x (SomeC r (SubstC c (RSubst r SDiff (v1, v2)))))))"
  | "push_rsubst_concept_somec SAdd (v1, v2) x r c = 
     (nnf_IfThenElseFm (ConjFm (ConjFm
        (FactFm (Eq True x v1)) 
        (FactFm (Inst v2 (SubstC c (RSubst r SAdd (v1, v2))))))
        (FactFm (AtomR False r v1 v2)))
      TrueFm
      (FactFm (Inst x (SomeC r (SubstC c (RSubst r SAdd (v1, v2)))))))"

fun push_rsubst_concept_allc :: 
  "subst_op \<Rightarrow> ('ni * 'ni) \<Rightarrow> 'ni \<Rightarrow> 'nr \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_rsubst_concept_allc SDiff (v1, v2) x r c = 
     (nnf_IfThenElseFm (ConjFm (ConjFm
        (FactFm (Eq True x v1))
        (FactFm (Inst v2  (NegC (SubstC c (RSubst r SDiff (v1, v2)))))))
        (FactFm (AtomR True r v1 v2)))
      (FactFm (Inst x ([<] (Suc 1) r (NegC (SubstC c (RSubst r SDiff (v1, v2)))))))
      (FactFm (Inst x (AllC r (SubstC c (RSubst r SDiff (v1, v2)))))))"
  | "push_rsubst_concept_allc SAdd (v1, v2) x r c = 
     (nnf_IfThenElseFm (ConjFm (ConjFm
        (FactFm (Eq True x v1)) 
        (FactFm (Inst v2 (NegC (SubstC c (RSubst r SAdd (v1, v2)))))))
        (FactFm (AtomR False r v1 v2)))
      FalseFm
      (FactFm (Inst x (AllC r (SubstC c (RSubst r SAdd (v1, v2)))))))"


fun push_rsubst_concept :: "'nr \<Rightarrow> subst_op \<Rightarrow> ('ni * 'ni) \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_rsubst_concept r rop v1v2 x (AtomC sign a) = (FactFm (Inst x (AtomC sign a)))"
  | "push_rsubst_concept r rop v1v2 x Top = (FactFm (Inst x Top))"
  | "push_rsubst_concept r rop v1v2 x Bottom = (FactFm (Inst x Bottom))"
  | "push_rsubst_concept r rop v1v2 x (NegC c) = (FactFm (Inst x (NegC (SubstC c (RSubst r rop v1v2)))))"
  | "push_rsubst_concept r rop v1v2 x (BinopC bop c1 c2) = 
                (FactFm (Inst x (BinopC bop (SubstC c1 (RSubst r rop v1v2)) (SubstC c2 (RSubst r rop v1v2)))))"
  | "push_rsubst_concept r rop v1v2 x (NumRestrC nro n r' c) = 
               (if r = r'
                then push_rsubst_concept_numrestrc rop v1v2 x nro n r c
                else (FactFm (Inst x (NumRestrC nro n r' (SubstC c (RSubst r rop v1v2))))))"
  | "push_rsubst_concept r rop v1v2 x (SubstC c sb) = (SubstFm (FactFm (Inst x (SubstC c sb))) (RSubst r rop v1v2))"
  | "push_rsubst_concept r rop v1v2 x (SomeC r' c) = 
               (if r = r'
                then push_rsubst_concept_somec rop v1v2 x r c
                else (FactFm (Inst x (SomeC r' (SubstC c (RSubst r rop v1v2))))))"
  | "push_rsubst_concept r rop v1v2 x (AllC r' c) = 
               (if r = r'
                then push_rsubst_concept_allc rop v1v2 x r c
                else (FactFm (Inst x (AllC r' (SubstC c (RSubst r rop v1v2))))))"

definition "subst_AtomR_SDiff sign r x y v1 v2 \<equiv> 
  neg_norm_form sign (ConjFm (DisjFm (FactFm (Eq False x v1)) (FactFm (Eq False y v2))) (FactFm (AtomR True r x y)))"

definition "subst_AtomR_SAdd sign r x y v1 v2 \<equiv>
  neg_norm_form sign (DisjFm (ConjFm (FactFm (Eq True x v1)) (FactFm (Eq True y v2))) (FactFm (AtomR True r x y)))"

fun push_rsubst_fact :: "'nr \<Rightarrow> subst_op \<Rightarrow> ('ni * 'ni)  \<Rightarrow> ('nr, 'nc, 'ni) fact \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_rsubst_fact r rop v1v2 (Inst x c) = push_rsubst_concept r rop v1v2 x c"
  | "push_rsubst_fact r rop v1v2 (AtomR sign r' x y) = 
     (if r = r'
      then (let (v1, v2) = v1v2 in
             (case rop of 
               SDiff \<Rightarrow> (subst_AtomR_SDiff sign r x y v1 v2)
             | SAdd \<Rightarrow> (subst_AtomR_SAdd sign r x y v1 v2)))
      else FactFm (AtomR sign r' x y))"
  | "push_rsubst_fact r rop v1v2 (Eq sign x y) = FactFm (Eq sign x y)"

fun push_csubst_concept :: "'nc \<Rightarrow> subst_op \<Rightarrow> 'ni \<Rightarrow> 'ni \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_csubst_concept cr rop v x (AtomC sign a) = 
               (if cr = a
                then (case rop of 
                       SDiff \<Rightarrow> neg_norm_form sign (ConjFm (FactFm (Inst x (AtomC True a))) (FactFm (Eq False x v)))
                     | SAdd  \<Rightarrow> neg_norm_form sign (DisjFm (FactFm (Inst x (AtomC True a))) (FactFm (Eq True x v))))
                else (FactFm (Inst x (AtomC sign a))))"
  | "push_csubst_concept cr rop v x Top = (FactFm (Inst x Top))"
  | "push_csubst_concept cr rop v x Bottom = (FactFm (Inst x Bottom))"
  | "push_csubst_concept cr rop v x (NegC c) = (FactFm (Inst x (NegC (SubstC c (CSubst cr rop v)))))"
  | "push_csubst_concept cr rop v x (BinopC bop c1 c2) = 
                       (FactFm (Inst x (BinopC bop (SubstC c1 (CSubst cr rop v)) (SubstC c2 (CSubst cr rop v)))))"
  | "push_csubst_concept cr rop v x (NumRestrC nro n r c) = 
                       (FactFm (Inst x (NumRestrC nro n r (SubstC c (CSubst cr rop v)))))"
  | "push_csubst_concept cr rop v x (SubstC c sb) = (SubstFm (FactFm (Inst x (SubstC c sb))) (CSubst cr rop v))"
  | "push_csubst_concept cr rop v x (SomeC r c) = (FactFm (Inst x (SomeC r (SubstC c (CSubst cr rop v)))))"
  | "push_csubst_concept cr rop v x (AllC r c) = (FactFm (Inst x (AllC r (SubstC c (CSubst cr rop v)))))"

fun push_csubst_fact :: "'nc \<Rightarrow> subst_op \<Rightarrow> 'ni  \<Rightarrow> ('nr, 'nc, 'ni) fact \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_csubst_fact c rop v (Inst x c') = push_csubst_concept c rop v x c'"
  | "push_csubst_fact c rop v (AtomR sign r x y) = FactFm (AtomR sign r x y)"
  | "push_csubst_fact c rop v (Eq sign x y) = FactFm (Eq sign x y)"


fun push_subst_fact :: "('nr, 'nc, 'ni) fact \<Rightarrow> ('nr, 'nc, 'ni) subst \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_subst_fact fct (RSubst r rop p) = push_rsubst_fact r rop p fct"
  | "push_subst_fact fct (CSubst c rop v) = push_csubst_fact c rop v fct"
  

fun extract_subst :: "('nr, 'nc, 'ni) fact \<Rightarrow> 
     (('ni) * (('nr, 'nc, 'ni) concept) * (('nr, 'nc, 'ni) subst)) option" where
    "extract_subst (Inst x (SubstC c sb)) = Some (x, c, sb)"
  | "extract_subst fct = None"

function push_subst_form :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) subst list \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "push_subst_form (ConstFm cn) sbsts = (ConstFm cn)"
  | "push_subst_form (FactFm fct) sbsts = 
           (case extract_subst fct of
              None \<Rightarrow> 
              (case sbsts of
                 [] \<Rightarrow> (FactFm fct)
               | sb # sbsts' \<Rightarrow> push_subst_form (push_subst_fact fct sb) sbsts')
            | Some(x, c, sb) \<Rightarrow> push_subst_form (FactFm (Inst x c)) (sb#sbsts))"
  | "push_subst_form (NegFm f) sbsts = NegFm (push_subst_form f sbsts)"
  | "push_subst_form (BinopFm bop f1 f2) sbsts = (BinopFm bop (push_subst_form f1 sbsts) (push_subst_form f2 sbsts))"
  | "push_subst_form (SubstFm f sb) sbsts =  push_subst_form f (sb#sbsts)"
by pat_completeness auto


fun replace_var :: "'ni rename \<Rightarrow> 'ni \<Rightarrow> 'ni" where
  "replace_var (ISubst v1 v2) w = (if w = v1 then v2 else w)"

fun rename_in_var :: "'ni \<Rightarrow> 'ni rename list \<Rightarrow> 'ni" where
    "rename_in_var x [] = x"
  | "rename_in_var x (sb # sbsts) = rename_in_var (replace_var sb x) sbsts"

(* TODO: to be considered: rename push_isubst ... to push_rename ... *)
fun rename_in_subst :: "('nr, 'nc, 'ni) subst \<Rightarrow> 'ni rename list \<Rightarrow> ('nr, 'nc, 'ni) subst" where
    "rename_in_subst (RSubst r rop (x1, x2)) sbsts = (RSubst r rop ((rename_in_var x1 sbsts), (rename_in_var x2 sbsts)))"
  | "rename_in_subst (CSubst cr rop v) sbsts = (CSubst cr rop (rename_in_var v sbsts))"


fun rename_in_concept :: "('nr, 'nc, 'ni) concept \<Rightarrow> 'ni rename list \<Rightarrow> ('nr, 'nc, 'ni) concept" where
    "rename_in_concept (AtomC sign a) sbsts = (AtomC sign a)"
  | "rename_in_concept Top sbsts = Top"
  | "rename_in_concept Bottom sbsts = Bottom"
  | "rename_in_concept (NegC c) sbsts = (NegC (rename_in_concept c sbsts))"
  | "rename_in_concept (BinopC bop c1 c2) sbsts = 
                (BinopC bop (rename_in_concept c1 sbsts) (rename_in_concept c2 sbsts))"
  | "rename_in_concept (NumRestrC nro n r c) sbsts = 
                (NumRestrC nro n r (rename_in_concept c sbsts))"
  | "rename_in_concept (SubstC c sb) sbsts = 
                (SubstC (rename_in_concept c sbsts) (rename_in_subst sb sbsts))"
  | "rename_in_concept (SomeC r' c) sbsts = (SomeC r' (rename_in_concept c sbsts))"
  | "rename_in_concept (AllC r' c) sbsts = (AllC r' (rename_in_concept c sbsts))"

fun rename_in_fact :: "('nr, 'nc, 'ni) fact \<Rightarrow> 'ni rename list \<Rightarrow> ('nr, 'nc, 'ni) fact" where
    "rename_in_fact (Inst x c) sbsts = (Inst (rename_in_var x sbsts) (rename_in_concept c sbsts))"
  | "rename_in_fact (AtomR sign r x y) sbsts = (AtomR sign r (rename_in_var x sbsts) (rename_in_var y sbsts))"
  | "rename_in_fact (Eq sign x y) sbsts = (Eq sign (rename_in_var x sbsts) (rename_in_var y sbsts))"

fun rename_in_form :: "('nr, 'nc, 'ni) form \<Rightarrow> 'ni rename list \<Rightarrow> ('nr, 'nc, 'ni) form" where
    "rename_in_form (ConstFm cn) sbsts = (ConstFm cn)"
  | "rename_in_form (FactFm fct) sbsts = (FactFm (rename_in_fact fct sbsts))"
  | "rename_in_form (NegFm f) sbsts = NegFm (rename_in_form f sbsts)"
  | "rename_in_form (BinopFm bop f1 f2) sbsts = 
          (BinopFm bop (rename_in_form f1 sbsts) (rename_in_form f2 sbsts))"
  | "rename_in_form (SubstFm f sb) sbsts =
          (SubstFm (rename_in_form f sbsts) (rename_in_subst sb sbsts))"

definition lift_bound_substs :: "'ni var rename list \<Rightarrow> 'ni var rename list" where
  "lift_bound_substs = map (\<lambda> sb. case sb of (ISubst x y) \<Rightarrow> (ISubst (lift_var 0 x) (lift_var 0 y)))"

fun rename_in_qform :: "('nr, 'nc, 'ni) qform \<Rightarrow>  'ni var rename list \<Rightarrow> ('nr, 'nc, 'ni) qform" where
    "rename_in_qform (QConstFm cn) sbsts = (QConstFm cn)"
  | "rename_in_qform (QFactFm fct) sbsts = (QFactFm (rename_in_fact fct sbsts))"
  | "rename_in_qform (QNegFm f) sbsts = QNegFm (rename_in_qform f sbsts)"
  | "rename_in_qform (QBinopFm bop f1 f2) sbsts = 
            (QBinopFm bop (rename_in_qform f1 sbsts) (rename_in_qform f2 sbsts))"
  | "rename_in_qform (QSubstFm f sb) sbsts =  
            (QSubstFm (rename_in_qform f sbsts) (rename_in_subst sb sbsts))"
  | "rename_in_qform (QRenameFm f sb) sbsts = rename_in_qform f (sb#sbsts)"
  | "rename_in_qform (QuantifFm q v f) sbsts = (QuantifFm q v (rename_in_qform f (lift_bound_substs sbsts)))"


fun is_rename_free_qform :: "(('nr, 'nc, 'ni) qform) \<Rightarrow> bool" where
    "is_rename_free_qform (QConstFm cn) = True"
  | "is_rename_free_qform (QFactFm f) = True"
  | "is_rename_free_qform (QNegFm f) = (is_rename_free_qform f)"
  | "is_rename_free_qform (QBinopFm bop f1 f2) = ((is_rename_free_qform f1) \<and> (is_rename_free_qform f2))"
  | "is_rename_free_qform (QuantifFm q v f) = is_rename_free_qform f"
  | "is_rename_free_qform (QSubstFm f sb) = (is_rename_free_qform f)"
  | "is_rename_free_qform (QRenameFm f sb) = False"

(*<*)
end
(*>*)
