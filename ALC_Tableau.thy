(*<*)
theory ALC_Tableau imports Semantics NormalForm SubstProofs 
begin
(*>*)

section {* Tableau Calculus for $\cal ALCQ$ *}

type_synonym ('nr, 'nc, 'ni) abox = "(('nr, 'nc, 'ni) form) set"

(*    (varbounds x) is an overapproximation of the set of possible decorations of x in 
     the further course of the proof
*)
type_synonym ('nr, 'nc, 'ni) varbounds = "'ni \<Rightarrow> (('nr, 'nc, 'ni) concept set)" 
record ('nr, 'nc, 'ni) tableau = 
  abox ::  "('nr, 'nc, 'ni) abox"
  varbounds :: "('nr, 'nc, 'ni) varbounds"


definition satisfiable :: "('nr, 'nc, 'ni) abox \<Rightarrow> bool"  where 
  "satisfiable ab = 
    (\<exists> (i:: ('d, 'nr, 'nc, 'ni) Interp). 
        well_formed_interp i \<and> 
        (\<forall> f \<in> (ab::('nr, 'nc, 'ni) abox). interp_form f i ))"

definition fv_abox::" ('nr, 'nc, 'ni) abox \<Rightarrow>'ni set" where 
 "fv_abox ab = \<Union>(fv_form` ab)"

abbreviation fv_tableau :: "('nr, 'nc, 'ni) tableau \<Rightarrow>'ni set" where 
 "fv_tableau tab \<equiv> (fv_abox (abox tab))"

definition "rename_in_abox ab ren = (\<lambda> f. rename_in_form f ren) ` ab"



 
  (* ----------------------------------------------------------------------  *)
subsection {* Rules *}
  (* ----------------------------------------------------------------------  *)
  
  (* Rules on aboxes *)
type_synonym ('nr, 'nc, 'ni) appcond_indiv = "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool"

(* abstract rule *)
type_synonym 'a arule = "'a \<Rightarrow> 'a \<Rightarrow> bool" 
type_synonym ('nr, 'nc, 'ni) rule = "('nr,'nc,'ni) abox arule"
type_synonym ('nr, 'nc, 'ni) tableau_rule = "('nr,'nc,'ni) tableau arule"

(* TODO: remove?
definition ex_rule_closure :: "('a \<Rightarrow> ('nr, 'nc, 'ni) rule) \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  "ex_rule_closure ir b1 b2 = (\<exists> x. (ir x b1 b2))"
*)
  (* more general type *)
definition ex_rule_closure :: "('f \<Rightarrow> ('a arule)) \<Rightarrow> ('a arule)" where
  "ex_rule_closure ir b1 b2 = (\<exists> x. (ir x b1 b2))"

definition "neq_complete x ab =  
  (\<forall> z1 z2. z1 \<le> x \<longrightarrow> z2 \<le> x \<longrightarrow> z1 \<noteq> z2 \<longrightarrow> z1 \<in> fv_abox ab \<longrightarrow> z2 \<in> fv_abox ab \<longrightarrow> 
  ((FactFm (Eq False z1 z2) \<in> ab) \<or> (FactFm (Eq False z2 z1) \<in> ab)))"



  (* -------------------------------------------- *)
  (* BEGIN EXPERIMENTAL *)
  (* Rules on tableaux *)

(* varbounds resulting from substituting v2 by v1 *)
definition join_varbounds :: "'ni \<Rightarrow> 'ni \<Rightarrow> ('ni \<Rightarrow> (('nr, 'nc, 'ni) concept set)) \<Rightarrow> ('ni \<Rightarrow> (('nr, 'nc, 'ni) concept set))" where
  "join_varbounds v2 v1 varb = (\<lambda> v.  if v = v1 then varb v1 \<union> varb v2 else if v = v2 then {} else varb v)"
  
definition lift_to_tableau_rule :: "('nr, 'nc, 'ni) rule \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
"lift_to_tableau_rule rl tab1 tab2 = (\<exists> ab2. rl (abox tab1) ab2 \<and> tab2 = tab1\<lparr>abox := ab2\<rparr>)"

(*the inverse *)
definition restrict_tableau_rule :: "('nr, 'nc, 'ni) tableau_rule \<Rightarrow> ('nr, 'nc, 'ni) rule" where
"restrict_tableau_rule trl ab1 ab2 = (\<exists> tab1 tab2. trl tab1 tab2 \<and> ab1 = (abox tab1) \<and> ab2 =  abox tab2)"

definition is_lift_to_tableau_rule :: "('nr, 'nc, 'ni) rule \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule \<Rightarrow> bool" where
"is_lift_to_tableau_rule rl trl = 
    ((\<forall> ab1 ab2 tab1. (rl ab1 ab2) \<longrightarrow> (abox tab1) = ab1 \<longrightarrow> 
       (\<exists> vb2. trl tab1 \<lparr> abox = ab2, varbounds = vb2 \<rparr>)) \<and>
     (\<forall> tab1 tab2. trl tab1 tab2 \<longrightarrow> rl (abox tab1) (abox tab2)))"

definition in_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) set" where
 "in_set R =  { (x, y) . R x y}"

lemma is_lift_to_tableau_rule_lift [simp]: "is_lift_to_tableau_rule rl (lift_to_tableau_rule rl)"
apply (auto simp add: lift_to_tableau_rule_def is_lift_to_tableau_rule_def)
apply (rename_tac ab2 tab1)
apply (case_tac tab1)
apply simp
done

lemma is_lift_to_tableau_rule_inv_image: 
   "is_lift_to_tableau_rule rl trl \<Longrightarrow> (in_set trl) \<subseteq> inv_image (in_set rl) abox"
by (clarsimp simp add: in_set_def inv_image_def is_lift_to_tableau_rule_def)


     (* other variants of the above notions 
definition is_lift_to_tableau_rule2 :: "('nr, 'nc, 'ni) rule \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule \<Rightarrow> bool" where
"is_lift_to_tableau_rule2 rl trl = 
    (\<forall> ab1 ab2. (rl ab1 ab2) \<longleftrightarrow> (\<exists> ve1 ve2. trl \<lparr> abox = ab1, vareqs = ve1 \<rparr> \<lparr> abox = ab2, vareqs = ve2 \<rparr>))"

    (* seems much too strong - would seem that arbitrary vareqs in tabs are admissible *)
definition is_lift_to_tableau_rule3 :: "('nr, 'nc, 'ni) rule \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule \<Rightarrow> bool" where
  "is_lift_to_tableau_rule3 rl trl = (\<forall> tab1 tab2. (trl tab1 tab2) \<longleftrightarrow> (rl (abox tab1) (abox tab2)))"

lemma "is_lift_to_tableau_rule3 rl trl \<Longrightarrow> is_lift_to_tableau_rule2 rl trl"
by (auto simp add:  is_lift_to_tableau_rule2_def is_lift_to_tableau_rule3_def)

(* here with unique existence *)
definition is_lift_to_tableau_rule4 :: "('nr, 'nc, 'ni) rule \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule \<Rightarrow> bool" where
"is_lift_to_tableau_rule4 rl trl = 
    ((\<forall> ab1 ab2 tab1. (rl ab1 ab2) \<longrightarrow> (abox tab1) = ab1 \<longrightarrow> (\<exists>! ve2. trl tab1 \<lparr> abox = ab2, vareqs = ve2 \<rparr>)) \<and>
     (\<forall> tab1 tab2. trl tab1 tab2 \<longrightarrow> rl (abox tab1) (abox tab2)))"

lemma "is_lift_to_tableau_rule rl trl \<Longrightarrow> is_lift_to_tableau_rule2 rl trl"
by (fastforce simp add:  is_lift_to_tableau_rule2_def is_lift_to_tableau_rule_def)

lemma "is_lift_to_tableau_rule4 rl trl \<Longrightarrow> is_lift_to_tableau_rule2 rl trl"
apply (auto simp add:  is_lift_to_tableau_rule2_def is_lift_to_tableau_rule4_def)
apply (drule spec, drule spec, drule mp, assumption)
apply (subgoal_tac "\<exists> tab1. abox tab1 = ab1")
apply clarsimp
apply (drule spec, drule mp, rule refl)
apply clarsimp
apply (case_tac tab1)
apply fastforce
apply (rule_tac x="\<lparr>abox = ab1, vareqs = \<lambda>x. {}\<rparr>" in exI)
apply fastforce+
done

lemma is_lift_to_tableau_rule2_lift [simp]: "is_lift_to_tableau_rule2 rl (lift_to_tableau_rule rl)"
by (auto simp add: lift_to_tableau_rule_def is_lift_to_tableau_rule2_def)

lemma is_lift_to_tableau_rule4_lift [simp]: "is_lift_to_tableau_rule4 rl (lift_to_tableau_rule rl)"
apply (auto simp add: lift_to_tableau_rule_def is_lift_to_tableau_rule4_def)
apply (case_tac tab1)
apply simp
apply (case_tac tab1)
apply simp
done


lemma "is_lift_to_tableau_rule2 rl trl \<Longrightarrow> (in_set trl) \<subseteq> inv_image (in_set rl) abox"
apply (clarsimp simp add: in_set_def inv_image_def)
apply (clarsimp simp add: is_lift_to_tableau_rule2_def)
apply (case_tac a)
apply (case_tac b)
apply fastforce
done
*)

(* TODO: not clear whether this is useful *)
definition sim_corresp :: "('s1 \<times> 's2) set \<Rightarrow> 's1 set \<Rightarrow> 's2 set \<Rightarrow> bool" where
  "sim_corresp sim S1 S2 \<equiv> \<forall> s1 \<in> S1. \<exists> s2 \<in> S2. (s1, s2) \<in> sim"
definition bisim_initial :: "('s1 \<times> 's2) set \<Rightarrow> 's1 set \<Rightarrow> 's2 set \<Rightarrow> bool" where
  "bisim_initial sim i1 i2 \<equiv>  sim_corresp sim i1 i2 \<and> sim_corresp (sim^-1) i2 i1"
definition bisim_step :: "('s1 \<times> 's2) set \<Rightarrow> 's1 rel \<Rightarrow> 's2 rel \<Rightarrow> bool" where
  "bisim_step sim ts1 ts2 \<equiv> 
   \<forall> s1 s2. (s1, s2) \<in> sim \<longrightarrow> 
    sim_corresp sim (ts1 `` {s1}) (ts2 `` {s2}) \<and> sim_corresp (sim^-1) (ts2 `` {s2}) (ts1 `` {s1})"
definition bisim :: "('s1 \<times> 's2) set \<Rightarrow> 's1 set \<Rightarrow> 's2 set \<Rightarrow> 's1 rel \<Rightarrow> 's2 rel \<Rightarrow> bool" where
  "bisim sim i1 i2 ts1 ts2 \<equiv> (bisim_initial sim i1 i2 \<and> bisim_step sim ts1 ts2)"



  (* END EXPERIMENTAL *)
  (* -------------------------------------------- *)


  (* ----------------------------------------------------------------------  *)
subsection {* Combinators for application conditions and rules *}

definition empty_rule :: "'a arule" where
  "empty_rule a b = False"

definition  alternative_rule :: "('a arule) \<Rightarrow> ('a arule) \<Rightarrow> ('a arule)" where
  "alternative_rule r1 r2 = (\<lambda> a b.  r1 a b  \<or>  r2 a b)"

definition alternative_appcond :: 
"('nr, 'nc, 'ni) appcond_indiv \<Rightarrow> ('nr, 'nc, 'ni) appcond_indiv \<Rightarrow> ('nr, 'nc, 'ni) appcond_indiv" where
  "alternative_appcond appc1 appc2 = (\<lambda> fm ab. appc1 fm ab \<or> appc2 fm ab)"

fun  alternative_rule_list  :: "'a arule list  \<Rightarrow> 'a arule" 
  where 
  " alternative_rule_list [] = empty_rule "
  |" alternative_rule_list (r#rs) =  alternative_rule r (alternative_rule_list rs)"
  

definition alternative_rule_of_set  :: "'a arule set  \<Rightarrow> 'a arule" where
   "alternative_rule_of_set rs a b = (\<exists> r \<in> rs. r a b)"

definition alternative_appcond_of_set  :: "('nr, 'nc, 'ni) appcond_indiv set  \<Rightarrow> ('nr, 'nc, 'ni) appcond_indiv" where
   "alternative_appcond_of_set appcs = (\<lambda> fm ab. (\<exists> appc \<in> appcs. appc fm ab))"


  (* ----------------------------------------------------------------------  *)
subsection {* Rules for fact *}
  
(* weak form of rule, without application condition. See lemma complete_weaken *)

inductive conjc_applicable :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow>  bool" where
  App_conjc:  "\<lbrakk> f = FactFm (Inst x (ConjC c1 c2)); f \<in> ab;  
  \<not> (FactFm (Inst x c1) \<in> ab \<and> FactFm (Inst x c2) \<in> ab) \<rbrakk> \<Longrightarrow> conjc_applicable f ab"

inductive  conjc_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_conjc_rule_indiv: "\<lbrakk> f = (FactFm (Inst x (ConjC c1 c2))); conjc_applicable f b1;
  b2 = {FactFm (Inst x c2), FactFm (Inst x c1)} \<union> b1\<rbrakk> \<Longrightarrow> conjc_rule_indiv f b1 b2"
  
definition conjc_rule :: "('nr, 'nc, 'ni) rule" where
"conjc_rule = ex_rule_closure conjc_rule_indiv"

definition conjc_tableau_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "conjc_tableau_rule_indiv f = lift_to_tableau_rule (conjc_rule_indiv f)"
  
  (* --------------------- *)
  
inductive disjc_applicable :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
  App_disjc:  "\<lbrakk> f = FactFm (Inst x (DisjC c1 c2));  f \<in> ab;  
  FactFm (Inst x c1) \<notin> ab;  FactFm (Inst x c2 ) \<notin> ab \<rbrakk> 
  \<Longrightarrow> disjc_applicable f ab"

inductive disjc_rule_indiv ::  "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_disjc_rule_indiv:  "\<lbrakk> f= (FactFm (Inst x (DisjC c1 c2))); disjc_applicable f b1;
       b2 = insert (FactFm (Inst x c1))  b1 \<or> b2 = insert (FactFm (Inst x c2)) b1\<rbrakk> 
  \<Longrightarrow> disjc_rule_indiv f b1 b2" 

definition disjc_rule :: "('nr, 'nc, 'ni) rule" where
"disjc_rule = ex_rule_closure disjc_rule_indiv"

definition disjc_tableau_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "disjc_tableau_rule_indiv f = lift_to_tableau_rule (disjc_rule_indiv f)"

  (* --------------------- *)
  
inductive allc_applicable :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
  App_allc:  "\<lbrakk> f = FactFm (Inst x (AllC r c));  f \<in> ab;  
  FactFm (AtomR True r x y) \<in> ab; FactFm (Inst y c) \<notin> ab \<rbrakk> \<Longrightarrow> allc_applicable f ab"

inductive allc_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where   
  mk_allc_rule: "\<lbrakk> f = (FactFm (Inst x (AllC r c))); allc_applicable f b1;
  b2 =  {f . (\<exists> y. (f = (FactFm (Inst y c))) \<and> FactFm (AtomR True r x y) \<in> b1)} \<union> b1 \<rbrakk>
  \<Longrightarrow> allc_rule_indiv f b1 b2"

definition allc_rule :: "('nr, 'nc, 'ni) rule" where
"allc_rule = ex_rule_closure allc_rule_indiv"

inductive somec_applicable :: "'ni \<Rightarrow> ('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow>  bool"  where
  App_somec : "\<lbrakk> f = FactFm (Inst x (SomeC  r c)); f \<in> ab ; 
                \<forall> y. \<not>  (FactFm (AtomR True r x y) \<in> ab  \<and>  FactFm (Inst y c) \<in> ab);
                  z \<notin> fv_abox ab\<rbrakk> 
  \<Longrightarrow> somec_applicable z f ab"

    (* --------------------- *)
    
definition somec_applicable_to_form :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
"somec_applicable_to_form f ab = (\<exists> z. somec_applicable z f ab)"

  (* TODO: potential for optimization? 
  For example: create (Inst z c) preferably for a z with (AtomR True r x z) \<in> b1 /
       and similarly for creation of (AtomR True r x z) for (Inst z c) \<in> b1  *)

inductive somec_rule_indiv :: "('ni * ('nr, 'nc, 'ni) form) \<Rightarrow> ('nr, 'nc, 'ni) rule" where
   mk_somec_rule_indiv: "\<lbrakk> f = (FactFm (Inst x (SomeC r c))); somec_applicable z f b1; 
                   b2= {FactFm (AtomR True r x z), FactFm (Inst z c)} \<union> b1 \<rbrakk>
  \<Longrightarrow> somec_rule_indiv (z, f) b1 b2"

definition somec_rule :: "('nr, 'nc, 'ni) rule" where
"somec_rule = ex_rule_closure somec_rule_indiv"

  (* --------------------- *)
  
inductive substc_applicable :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool"  where
  App_substc : "\<lbrakk> f = FactFm (Inst x (SubstC c sb)); f \<in> ab;  push_subst_form f [] \<notin> ab \<rbrakk> 
  \<Longrightarrow> substc_applicable f ab"

inductive substc_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_substc_rule_indiv: "\<lbrakk>substc_applicable f b1; b2 = insert (push_subst_form f []) b1\<rbrakk> 
  \<Longrightarrow> substc_rule_indiv f b1 b2" 

definition substc_rule :: "('nr, 'nc, 'ni) rule" where
"substc_rule = ex_rule_closure substc_rule_indiv"

definition substc_tableau_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "substc_tableau_rule_indiv f = lift_to_tableau_rule (substc_rule_indiv f)"

  (* --------------------- *)

inductive eq_applicable :: "('nr, 'nc, 'ni:: linorder) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool"  where
  App_eq: "\<lbrakk> f = FactFm (Eq True x y); f \<in> ab; x \<noteq> y \<rbrakk>  \<Longrightarrow> eq_applicable f ab"

inductive eq_rule_indiv :: "('nr, 'nc, 'ni:: linorder) form \<Rightarrow> ('nr,'nc,'ni) rule" where
   mk_eq_rule_indiv: "\<lbrakk> f = (FactFm (Eq True x y)); eq_applicable f b1; 
   b2 = rename_in_abox b1 (if x < y then [ISubst y x] else [ISubst x y])  \<rbrakk>
  \<Longrightarrow> eq_rule_indiv f b1 b2"
  
definition eq_rule :: "('nr, 'nc, 'ni:: linorder) rule" where
"eq_rule = ex_rule_closure eq_rule_indiv"

inductive eq_tableau_rule_indiv :: "('nr, 'nc, 'ni:: linorder) form \<Rightarrow> ('nr,'nc,'ni) tableau_rule" where
   mk_eq_tableau_rule_indiv: "\<lbrakk> f = (FactFm (Eq True x y)); eq_applicable f (abox tb1); 
   b2 = rename_in_abox (abox tb1) (if x < y then [ISubst y x] else [ISubst x y]);
   vb2 = (if x < y then join_varbounds y x (varbounds tb1) else join_varbounds x y (varbounds tb1));
   tb2 = \<lparr> abox = b2, varbounds = vb2 \<rparr>\<rbrakk>
  \<Longrightarrow> eq_tableau_rule_indiv f tb1 tb2"
  
lemma is_lift_to_tableau_rule_eq_indiv: 
   "is_lift_to_tableau_rule (eq_rule_indiv f) (eq_tableau_rule_indiv f)"
   apply (simp add: is_lift_to_tableau_rule_def)
   apply (fastforce simp add: eq_rule_indiv.simps eq_tableau_rule_indiv.simps)+
done


  (* ----------------------------------------------------------------------  *)
subsection {* Equality completion rule *}

inductive eq_compl_rule ::  "('nr, 'nc, 'ni:: linorder) rule" where
  mk_eq_compl_rule:  "\<lbrakk> x < y; {x, y} \<subseteq> fv_abox b1; 
       \<forall> s. (FactFm (Eq s x y) \<notin> b1); \<forall> s. FactFm (Eq s y x) \<notin> b1;
       b2 = insert (FactFm (Eq False x y))  b1 \<or> b2 = rename_in_abox b1 [ISubst y x] \<rbrakk> 
  \<Longrightarrow> eq_compl_rule b1 b2" 


inductive eq_compl_tableau_rule :: "('nr, 'nc, 'ni:: linorder) tableau_rule" where 
  mk_eq_tableau_rule_indiv: "(x < y) \<Longrightarrow>
  ({x, y} \<subseteq> fv_abox (abox tb1)) \<Longrightarrow>
  (\<forall> s. (FactFm (Eq s x y) \<notin> (abox tb1))) \<Longrightarrow> 
  (\<forall> s. (FactFm (Eq s y x) \<notin> (abox tb1))) \<Longrightarrow>
  tb2 = \<lparr> abox = insert (FactFm (Eq False x y)) (abox tb1), varbounds = varbounds tb1 \<rparr> \<or>
  tb2 = \<lparr> abox = rename_in_abox (abox tb1) [ISubst y x], varbounds = join_varbounds y x (varbounds tb1) \<rparr> 
  \<Longrightarrow> eq_compl_tableau_rule tb1 tb2" 


  (* ----------------------------------------------------------------------  *)
subsection {* Rules for form *}

inductive conjfm_applicable :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow>  bool" where
  App_conjfm:  "\<lbrakk> f = (ConjFm f1 f2); f \<in> ab;  \<not> (f1 \<in> ab \<and> f2 \<in> ab) \<rbrakk> 
  \<Longrightarrow>  conjfm_applicable f ab"

inductive conjfm_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_conjfm_rule_indiv: "\<lbrakk> f = (ConjFm f1 f2); conjfm_applicable f b1 ; b2 = {f2, f1} \<union> b1\<rbrakk> 
  \<Longrightarrow> conjfm_rule_indiv f b1 b2" 

definition conjfm_rule :: "('nr, 'nc, 'ni) rule" where
"conjfm_rule = ex_rule_closure conjfm_rule_indiv"

definition conjfm_tableau_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "conjfm_tableau_rule_indiv f = lift_to_tableau_rule (conjfm_rule_indiv f)"

  (* --------------------- *)
  
inductive disjfm_applicable :: " ('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
  App_disjfm:  "\<lbrakk> f = (DisjFm f1 f2);  f \<in> ab;  f1 \<notin> ab;  f2 \<notin> ab \<rbrakk> 
  \<Longrightarrow> disjfm_applicable f ab"

inductive disjfm_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_disjfm_rule_indiv: 
  "\<lbrakk> f = (DisjFm f1 f2); disjfm_applicable f b1; b2 = insert f1 b1 \<or> b2 = insert f2 b1 \<rbrakk>  
  \<Longrightarrow> disjfm_rule_indiv f b1 b2" 

definition disjfm_rule :: "('nr, 'nc, 'ni) rule" where
"disjfm_rule = ex_rule_closure disjfm_rule_indiv"

definition disjfm_tableau_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "disjfm_tableau_rule_indiv f = lift_to_tableau_rule (disjfm_rule_indiv f)"

  (* --------------------- *)
  
inductive substfm_applicable :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool"  where
  App_substfm : "\<lbrakk> f = SubstFm fm sb; f \<in> ab; push_subst_form f [] \<notin> ab  \<rbrakk> 
  \<Longrightarrow> substfm_applicable f ab"

inductive substfm_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_substfm_rule_indiv: "\<lbrakk>substfm_applicable f b1; b2 = insert (push_subst_form f []) b1\<rbrakk> 
  \<Longrightarrow> substfm_rule_indiv f b1 b2" 

definition substfm_rule :: "('nr, 'nc, 'ni) rule" where
"substfm_rule = ex_rule_closure substfm_rule_indiv"

definition substfm_tableau_rule_indiv :: "('nr,'nc,'ni) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "substfm_tableau_rule_indiv f = lift_to_tableau_rule (substfm_rule_indiv f)"

  (* --------------------- *)
  (* Choose rule*)

  (* TODO: choose_applicable not used any longer. 
  The y in choose_applicable would have to be the same as in choose_rule_indiv *)
inductive choose_applicable  :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
  App_choose:  "\<lbrakk>  FactFm (Inst x ([<] n r c)) = f ;  f \<in> ab; 
  FactFm (AtomR True r x y) \<in> ab ;   
  FactFm (Inst y c) \<notin> ab ;  FactFm (Inst y (neg_norm_concept False c)) \<notin> ab \<rbrakk> 
  \<Longrightarrow>  choose_applicable f ab"

inductive choose_rule_indiv :: "('nr, 'nc, 'ni:: linorder) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_choose_rule:  "\<lbrakk> f = (FactFm (Inst x ([<] n r c))); f \<in> b1;
       FactFm (AtomR True r x y) \<in> b1;
       FactFm (Inst y c) \<notin> b1 ;  FactFm (Inst y (neg_norm_concept False c)) \<notin> b1;
       b2 = insert (FactFm (Inst y c))  b1 \<or> b2 = insert (FactFm (Inst y (neg_norm_concept False c))) b1\<rbrakk> 
  \<Longrightarrow> choose_rule_indiv f b1 b2" 

definition choose_rule :: "('nr, 'nc, 'ni:: linorder) rule" where
"choose_rule = ex_rule_closure choose_rule_indiv"

definition choose_tableau_rule_indiv :: "('nr,'nc,'ni:: linorder) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "choose_tableau_rule_indiv f = lift_to_tableau_rule (choose_rule_indiv f)"


(* Choose rule - variant that is stable under substitutions *)

(*
inductive choose_stable_applicable  :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
  App_choose_stable:  "\<lbrakk> FactFm (Inst x ([<] n r c))  = f;  f \<in> ab; 
  FactFm (AtomR True r x' y) \<in> ab ;   
  FactFm (Inst y c) \<notin> ab ;  FactFm (Inst y (neg_norm_concept False c)) \<notin> ab \<rbrakk> 
  \<Longrightarrow>  choose_stable_applicable f ab"
*)

(*
inductive choose_stable_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_choose_stable_rule:  "\<lbrakk> (FactFm (Inst x ([<] n r c))) = f; f \<in> b1; 
       FactFm (AtomR True r x' y) \<in> b1 ;   
       FactFm (Inst y c) \<notin> b1 ;  FactFm (Inst y (neg_norm_concept False c)) \<notin> b1;  
       b2 = insert (DisjFm (ConjFm (FactFm (Eq True x x')) (FactFm (Inst y c))) (FactFm (Eq False x x'))) b1 \<or> 
       b2 = insert (DisjFm (ConjFm (FactFm (Eq True x x')) (FactFm (Inst y (neg_norm_concept False c)))) (FactFm (Eq False x x'))) b1\<rbrakk> 
  \<Longrightarrow> choose_stable_rule_indiv f b1 b2" 
*)

inductive choose_stable_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) rule" where
  mk_choose_stable_rule:  "\<lbrakk> f = (FactFm (Inst x ([<] n r c))); f \<in> b1; 
       FactFm (AtomR True r x' y) \<in> b1 ;   (FactFm (Eq False x x')) \<notin> b1 ;
       FactFm (Inst y c) \<notin> b1 ;  FactFm (Inst y (neg_norm_concept False c)) \<notin> b1;  
       b2 = insert (FactFm (Eq False x x')) b1 \<or> 
       b2 = insert (FactFm (Eq True x x')) (insert (FactFm (Inst y c)) b1) \<or> 
       b2 = insert (FactFm (Eq True x x')) (insert (FactFm (Inst y (neg_norm_concept False c))) b1)\<rbrakk> 
  \<Longrightarrow> choose_stable_rule_indiv f b1 b2" 

definition choose_stable_rule :: "('nr, 'nc, 'ni) rule" where
"choose_stable_rule = ex_rule_closure choose_stable_rule_indiv"

  (* --------------------- *)
  (* Numrestrc *)


definition "fresh_set Y ab = (Y \<inter> fv_abox ab = {})"
definition "fresh_set_incr (Y::('a::linorder) set) ab = (\<forall> x\<in>fv_abox ab. \<forall> y\<in>Y. x < y)"

definition "numrestrc_ge_blocked ab x n r c =
   (\<exists>S. finite S \<and> card S = n \<and>
        (\<forall>z\<in>S. FactFm (AtomR True r x z) \<in> ab \<and> FactFm (Inst z c) \<in> ab) \<and>
        (\<forall>z1\<in>S. \<forall>z2\<in>S.  z1 \<noteq> z2 \<longrightarrow> FactFm (Eq False z1 z2) \<in> ab \<or> FactFm (Eq False z2 z1) \<in> ab))"

lemma numrestrc_ge_blocked_for_0 [simp]: "numrestrc_ge_blocked ab x 0 r c"
by (fastforce simp add: numrestrc_ge_blocked_def)

definition numrestrc_ge_complete :: "'ni:: linorder \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
  "numrestrc_ge_complete x ab = (\<forall> n r c. numrestrc_ge_blocked ab x n r c)"
  
(* the additional side condition  S \<subseteq> fv_abox ab can be derived from the following *)
(*
inductive numrestrc_ge_applicable:: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
  App_numrestrc_ge:"FactFm (Inst x ([\<ge>] n r c)) = f \<Longrightarrow>
                    f \<in> ab \<Longrightarrow>
                    \<not> (\<exists>S. finite S \<and> card S = n \<and>
                        (\<forall>z\<in>S. FactFm (AtomR True r x z) \<in> ab \<and> FactFm (Inst z c) \<in> ab) \<and>
                        (\<forall>z1\<in>S. \<forall>z2\<in>S.  z1 \<noteq> z2 \<longrightarrow> FactFm (Eq False z1 z2) \<in> ab \<or> FactFm (Eq False z2 z1) \<in> ab)) \<Longrightarrow>
                       numrestrc_ge_applicable f ab"
*)

inductive numrestrc_ge_applicable:: "('nr, 'nc, 'ni::linorder) form \<Rightarrow> ('nr, 'nc, 'ni) abox \<Rightarrow> bool" where
  App_numrestrc_ge: "FactFm (Inst x ([\<ge>] n r c)) = f \<Longrightarrow>
                    f \<in> ab \<Longrightarrow> 
                    \<not> numrestrc_ge_blocked ab x n r c \<Longrightarrow>
                    numrestrc_ge_applicable f ab"

definition "numrestrc_ge_rule_facts c r x Y =
     {FactFm (AtomR True r x y) | y. y \<in> Y} 
   \<union> {FactFm (Inst y c) | y. y \<in> Y} 
   \<union> {FactFm (Eq False y1 y2) | y1 y2. y1 \<in> Y \<and> y2 \<in> Y \<and> y1 < y2}"


inductive numrestrc_ge_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, ('ni :: linorder)) rule" where
  mk_numrestrc_ge_rule_indiv: 
  "\<lbrakk> f = FactFm (Inst x ([\<ge>] n r c));
     numrestrc_ge_applicable f b1;
     neq_complete x b1;
     card Y = n; finite Y;
     fresh_set_incr Y b1;
     b2 =  numrestrc_ge_rule_facts c r x Y \<union> b1 \<rbrakk>
    \<Longrightarrow> numrestrc_ge_rule_indiv f b1 b2"
    

definition numrestrc_ge_rule :: "('nr, 'nc, 'ni :: linorder) rule" where
"numrestrc_ge_rule = ex_rule_closure numrestrc_ge_rule_indiv"

(*
definition numrestrc_ge_tableau_rule_indiv :: "('nr,'nc,'ni:: linorder) form \<Rightarrow> ('nr, 'nc, 'ni) tableau_rule" where
  "numrestrc_ge_tableau_rule_indiv f = lift_to_tableau_rule (numrestrc_ge_rule_indiv f)"
*)

definition successor_varbounds :: "'nr \<Rightarrow> ('nr, 'nc, 'ni) concept set \<Rightarrow> ('nr, 'nc, 'ni) concept set" where
  "successor_varbounds r vbs = 
    \<Union> (sub_concepts_pn ` (concept_of_NumRestrC_concept ` {c \<in> vbs. is_NumRestrC_concept UNIV {r} c}))"

definition "numrestrc_ge_successor_varbounds_old Y r tb1 x = 
            (\<lambda> v. if v \<in> Y then (successor_varbounds r (varbounds tb1 x)) else varbounds tb1 v)"

definition "varbounds_forw tab x = 
     (\<Union> y \<in> fv_tableau tab. (if (x < y \<and> varbounds tab y \<subset> varbounds tab x)
                              then varbounds tab y
                              else {}))"

(* TODO: this approach cannot work. One would have to make the successor smaller and not larger *)
definition "numrestrc_ge_successor_varbounds_new Y r tab x = 
            (\<lambda> v. if v \<in> Y 
                  then (successor_varbounds r (varbounds tab x)) \<union> varbounds_forw tab x 
                  else varbounds tab v)"

inductive numrestrc_ge_tableau_rule_indiv :: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, ('ni :: linorder)) tableau_rule" where
  mk_numrestrc_ge_tableau_rule_indiv: 
  "\<lbrakk> f = FactFm (Inst x ([\<ge>] n r c));
     numrestrc_ge_applicable f (abox tb1);
     neq_complete x (abox tb1);
     card Y = n; finite Y;
     fresh_set_incr Y (abox tb1);
     b2 =  numrestrc_ge_rule_facts c r x Y \<union> (abox tb1);
     vb2 = numrestrc_ge_successor_varbounds_old Y r tb1 x;
     tb2 =  \<lparr> abox = b2, varbounds = vb2 \<rparr> \<rbrakk>
    \<Longrightarrow> numrestrc_ge_tableau_rule_indiv f tb1 tb2"

    (* TODO:
    The condition about the fresh_set is questionable, one would have to choose variables fresh
    for all fv_tableau and not only for fv_abox. But then, lift_to_tableau_rule is not provable any more. 
    Possibly, it turns out that the vareqs are not required for the termination proof.
    *)

  (* --------------------- *)
 
inductive numrestrc_lt_applicable:: "('ni set * ('nr, 'nc, 'ni) form) \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
  App_numrestrc_lt:
  "f = FactFm (Inst x ([<] n r c)) \<Longrightarrow>
   f \<in> ab \<Longrightarrow>
   card S = n \<Longrightarrow>  1 < n \<Longrightarrow>
   \<forall>y\<in>S. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab 
   \<Longrightarrow> numrestrc_lt_applicable (S, f) ab"

   (* TODO: the name is not ideal, and maybe the def is not needed.
   Recheck after dealing with proof traces.
   Harmonize with somec_applicable.  *)
definition numrestrc_lt_applicable_to_form :: "('nr, 'nc, 'ni) form \<Rightarrow> (('nr, 'nc, 'ni) abox) \<Rightarrow> bool" where
"numrestrc_lt_applicable_to_form  f ab = (\<exists> S. numrestrc_lt_applicable (S, f) ab)"

inductive numrestrc_lt_rule_orig_indiv:: "('ni set * ('nr, 'nc, 'ni) form) \<Rightarrow> ('nr, 'nc, ('ni :: linorder)) rule" where
  mk_numrestrc_lt_rule_orig_indiv: 
    "\<lbrakk> f = (FactFm (Inst x ([<] n r c))); numrestrc_lt_applicable (S, f) b1; 
    y1 \<in> S; y2 \<in> S; y1 < y2;
    b2 = rename_in_abox b1 [ISubst y2 y1] \<rbrakk> 
    \<Longrightarrow> numrestrc_lt_rule_orig_indiv (S, f) b1 b2"

definition numrestrc_lt_rule_orig :: "('nr, 'nc, 'ni :: linorder) rule" where
"numrestrc_lt_rule_orig = ex_rule_closure numrestrc_lt_rule_orig_indiv"

(* the following variant makes a transition on f only, not also on S *)
inductive numrestrc_lt_rule_indiv:: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, ('ni :: linorder)) rule" where
  mk_numrestrc_lt_rule_indiv: 
    "\<lbrakk> f = (FactFm (Inst x ([<] n r c))); numrestrc_lt_applicable (S, f) b1; 
    y1 \<in> S; y2 \<in> S; y1 < y2;
    b2 = rename_in_abox b1 [ISubst y2 y1] \<rbrakk> 
    \<Longrightarrow> numrestrc_lt_rule_indiv f b1 b2"

definition numrestrc_lt_rule :: "('nr, 'nc, 'ni :: linorder) rule" where
"numrestrc_lt_rule = ex_rule_closure numrestrc_lt_rule_indiv"

inductive numrestrc_lt_tableau_rule_indiv:: "('nr, 'nc, 'ni) form \<Rightarrow> ('nr, 'nc, ('ni :: linorder)) tableau_rule" where
  mk_numrestrc_lt_tableau_rule_indiv: 
    "\<lbrakk> f = (FactFm (Inst x ([<] n r c))); numrestrc_lt_applicable (S, f) (abox tb1); 
    y1 \<in> S; y2 \<in> S; y1 < y2;
    b2 = rename_in_abox (abox tb1) [ISubst y2 y1];
    vb2 = join_varbounds y2 y1 (varbounds tb1);
    tb2 = \<lparr> abox = b2, varbounds = vb2 \<rparr>\<rbrakk>
    \<Longrightarrow> numrestrc_lt_tableau_rule_indiv f tb1 tb2"
    

lemma is_lift_to_tableau_rule_numrestrc_lt_indiv: 
   "is_lift_to_tableau_rule (numrestrc_lt_rule_indiv f) (numrestrc_lt_tableau_rule_indiv f)"
   apply (simp add: is_lift_to_tableau_rule_def)
   apply (fastforce simp add: numrestrc_lt_rule_indiv.simps numrestrc_lt_tableau_rule_indiv.simps)+
done


  (* --------------------- *)
  
definition set_alc_rules::"('nr, 'nc, 'ni::linorder) rule set" where  
  "set_alc_rules =  
  {conjc_rule, disjc_rule, allc_rule, somec_rule, substc_rule, 
  eq_rule, eq_compl_rule,
  conjfm_rule, disjfm_rule, substfm_rule, choose_rule, 
  numrestrc_ge_rule, numrestrc_lt_rule}"

definition alc_rule :: "('nr, 'nc, 'ni:: linorder) rule"  where   
  "alc_rule = alternative_rule_of_set set_alc_rules"

(* TODO: recheck name; these are maybe not only application conditions
definition set_alc_appconds ::"(('nr, 'nc, 'ni) appcond_indiv) set" where  
  "set_alc_appconds =  
  {conjc_applicable, disjc_applicable, allc_applicable, 
  somec_applicable_to_form, substc_applicable, eq_applicable, 
  conjfm_applicable, disjfm_applicable, substfm_applicable, choose_applicable, 
  numrestrc_ge_applicable, numrestrc_lt_applicable_to_form}"
*)


definition conjc_tableau_rule :: "('nr, 'nc, 'ni) tableau_rule" where
"conjc_tableau_rule = ex_rule_closure conjc_tableau_rule_indiv"

definition disjc_tableau_rule :: "('nr, 'nc, 'ni) tableau_rule" where
"disjc_tableau_rule = ex_rule_closure disjc_tableau_rule_indiv"

definition eq_tableau_rule :: "('nr, 'nc, 'ni:: linorder) tableau_rule" where
"eq_tableau_rule = ex_rule_closure eq_tableau_rule_indiv"

definition choose_tableau_rule :: "('nr, 'nc, 'ni:: linorder) tableau_rule" where
"choose_tableau_rule = ex_rule_closure choose_tableau_rule_indiv"

definition numrestrc_ge_tableau_rule :: "('nr, 'nc, 'ni:: linorder) tableau_rule" where
"numrestrc_ge_tableau_rule = ex_rule_closure numrestrc_ge_tableau_rule_indiv"

definition numrestrc_lt_tableau_rule :: "('nr, 'nc, 'ni:: linorder) tableau_rule" where
"numrestrc_lt_tableau_rule = ex_rule_closure numrestrc_lt_tableau_rule_indiv"

definition set_concept_tableau_rules::"('nr, 'nc, 'ni::linorder) tableau_rule set" where  
  "set_concept_tableau_rules =  
  {conjc_tableau_rule, disjc_tableau_rule, 
  eq_tableau_rule, eq_compl_tableau_rule, choose_tableau_rule, 
  numrestrc_ge_tableau_rule, numrestrc_lt_tableau_rule}"

definition concept_tableau_rule :: "('nr, 'nc, 'ni:: linorder) tableau_rule"  where   
  "concept_tableau_rule = alternative_rule_of_set set_concept_tableau_rules"

    (* ----------------------------------------------------------------------  *)
subsection {* Clashes *}
    
fun contains_bottom :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_bottom ab = (\<exists> x. FactFm (Inst x Bottom) \<in> ab)"

fun contains_contr_concept :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_contr_concept ab = (\<exists> x a. FactFm (Inst x (AtomC True a)) \<in> ab \<and> FactFm (Inst x (AtomC False a)) \<in> ab)"

fun contains_contr_role :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_contr_role ab = (\<exists> x y r. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (AtomR False r x y) \<in> ab)"

fun contains_contr_eq :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_contr_eq ab = (\<exists> x. FactFm (Eq False x x) \<in> ab)"

fun contains_falsefm :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_falsefm ab = (FalseFm \<in> ab)"

fun contains_numrestrc_lt_0 :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_numrestrc_lt_0 ab = (\<exists> x r c. FactFm (Inst x ([<] 0 r c)) \<in> ab) "

definition R_succs :: " 'nr => (('nr, 'nc, 'ni) concept)=> (('nr, 'nc, 'ni) abox)=> 'ni=> 'ni set" where
  "R_succs r c ab x =  {y. FactFm (AtomR True r x y) \<in> ab \<and> FactFm (Inst y c) \<in> ab} "

definition mutually_uneq :: "('nr, 'nc, 'ni) abox \<Rightarrow> 'ni set \<Rightarrow> bool" where
  "mutually_uneq ab S = (\<forall>x\<in>S. \<forall> y\<in>S. x\<noteq>y \<longrightarrow> FactFm (Eq False x y) \<in> ab \<or> FactFm (Eq False y x) \<in> ab)"

definition contains_atmost_clash :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_atmost_clash ab = (\<exists> x r c n. FactFm (Inst x ([<] n r c)) \<in> ab \<and>  
                               (\<exists> S. S \<subseteq> (R_succs r c ab x) \<and> mutually_uneq ab S \<and> card S \<ge> n))"

definition contains_clash :: "('ni,'nr,'nc) abox \<Rightarrow> bool" where  
  "contains_clash ab = 
    (contains_bottom ab \<or> 
     contains_contr_concept ab \<or>
     contains_contr_role ab \<or>
     contains_contr_eq ab \<or>
     contains_falsefm ab \<or>
     contains_atmost_clash ab \<or>
     contains_numrestrc_lt_0 ab)"

end

