(* Translations from description logic to predicate logic *)

theory LogicTranslations imports PredicateLogic 
begin

datatype ('nc, 'nr) rel2 = Rel1 'nc | Rel2 'nr


fun concept_to_plform :: "'ni var \<Rightarrow> ('nr, 'nc, 'ni var) concept \<Rightarrow> (('nc, 'nr) rel2, 'ni) plform" where
  "concept_to_plform x Bottom = PlConstFm False"
| "concept_to_plform x Top = PlConstFm True"
| "concept_to_plform x (AtomC sign a) = (if sign then (PlConc (Rel1 a) x) else PlNegFm (PlConc (Rel1 a) x))"
| "concept_to_plform x (BinopC bop c1 c2) =  
           PlBinopFm bop (concept_to_plform x c1) (concept_to_plform x c2)"  
| "concept_to_plform x (NegC c) = PlNegFm (concept_to_plform x c)"

fun fact_to_plform :: "('nr, 'nc, 'ni var) fact \<Rightarrow> (('nc, 'nr) rel2, 'ni) plform" where
  "fact_to_plform (Inst x c) = concept_to_plform x c"
| "fact_to_plform (AtomR sign r x y) = PlBRel sign (Rel2 r) x y"
| "fact_to_plform (Eq sign x y) = PlEq sign x y"


  (* TODO: recheck QuantifFm *) 
    (* TODO: still do substitution in case QSubstFm and QRenameFm *) 
fun qform_to_plform :: "('nr, 'nc, 'ni) qform \<Rightarrow> (('nc, 'nr) rel2, 'ni) plform" where
  "qform_to_plform (QConstFm b) = PlConstFm b"
| "qform_to_plform (QFactFm fct) = fact_to_plform fct"
| "qform_to_plform (QNegFm f) = PlNegFm (qform_to_plform f)"
| "qform_to_plform (QBinopFm bop f1 f2) = PlBinopFm bop (qform_to_plform f1) (qform_to_plform f2)"
| "qform_to_plform (QuantifFm q v f) = PlQuantifFm q v (qform_to_plform f)"
| "qform_to_plform (QSubstFm f sb) = qform_to_plform f"
| "qform_to_plform (QRenameFm f sb) = qform_to_plform f"  

end

