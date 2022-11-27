theory ALC_PrInfrastruc imports New_Var ALC_Tableau

(* TODO: check activity and splitting status of rules, 
in particular AllC, Numrestr-rules, Subst-rules *)
begin

(* --------------  Tableau Constructors  -------------- *)

(* new_form: may contain any formula except for negations
 *)
type_synonym ('nr, 'nc, 'ni) new_form = "('nr, 'nc, 'ni) form list"

(* active_linear_form:
   FactFm(Inst(x, BinopC(Conj, c1, c2)))
   FactFm(Inst(x, NumRestrC(Ge, n, r, c)))
   FactFm(Inst(x, SomeC(r, c)))
   FactFm(Eq(true, x, y)) for x /= y
   BinopFm (Conj, f1, f2)
  *)
type_synonym ('nr, 'nc, 'ni) active_linear_form = "('nr, 'nc, 'ni) form list"


(* active_splitting_form:
   FactFm(Inst(x, BinopC(Disj, c1, c2)))
   FactFm(Inst(x, SubstC(c, sb)))
   BinopFm (Disj, f1, f2)
   SubstFm (f, sb)
*)
type_synonym ('nr, 'nc, 'ni) active_splitting_form = "('nr, 'nc, 'ni) form list"


(* active_permanent_form: permanently active formula
   FactFm(Inst(x, NumRestrC(Lt, n, r, c)))      
   FactFm(Inst x (AllC r c))
*)
type_synonym ('nr, 'nc, 'ni) active_permanent_form = "('nr, 'nc, 'ni) form list"


(* inactive_composite:
   FactFm(Inst(x, Top))
   FactFm(Eq(true, x, x))
   ConstFm true
   FactFm(Inst(x, BinopC(Conj, c1, c2)))
   FactFm(Inst(x, NumRestrC(Ge, n, r, c)))
   FactFm(Inst(x, SubstC(c, sb)))
   FactFm(Inst(x, BinopC(Disj, c1, c2)))
   BinopFm (Conj, f1, f2)
   BinopFm (Disj, f1, f2)
   SubstFm (f, sb)
*)
type_synonym ('nr, 'nc, 'ni) inactive_composite = "('nr, 'nc, 'ni) form list"

(* inactive_atomc:
   FactFm(Inst(x, AtomC(sign, a)))
*)
type_synonym ('nr, 'nc, 'ni) inactive_atomc = "('nr, 'nc, 'ni) form list"

(* inactive_atomr:
   FactFm(AtomR(sign, r, x, y))
*)
type_synonym ('nr, 'nc, 'ni) inactive_atomr = "('nr, 'nc, 'ni) form list"

(* inactive_equivs:
   FactFm(Eq(false, x, y)) for x /= y
 *)
type_synonym ('nr, 'nc, 'ni) inactive_equivs = "('nr, 'nc, 'ni) form list"


(* inactive_clash:
   FactFm(Inst(x, Bottom))
   FactFm(Eq(false, x, x))
   ConstFm false
 *)
type_synonym ('nr, 'nc, 'ni) inactive_clash = "('nr, 'nc, 'ni) form list"

datatype ('nr, 'nc, 'ni) inactive_frm = Inactive_form  
    "('nr, 'nc, 'ni) inactive_composite *
      ('nr, 'nc, 'ni) inactive_atomc *
      ('nr, 'nc, 'ni) inactive_atomr *
      ('nr, 'nc, 'ni) inactive_equivs *
      ('nr, 'nc, 'ni) inactive_clash"

datatype ('nr, 'nc, 'ni) proofbranch = Branch 
    "('nr, 'nc, 'ni) new_form * 
      ('nr, 'nc, 'ni) active_linear_form * 
      ('nr, 'nc, 'ni) active_splitting_form * 
      ('nr, 'nc, 'ni) active_permanent_form * 
      ('nr, 'nc, 'ni) inactive_frm"

type_synonym ('nr, 'nc, 'ni) proofstate = "('nr, 'nc, 'ni) proofbranch list"

(* --------------  Proof Trace Constructors  -------------- *)

(* TODO: use that later. Too complex for now.
datatype ('nr, 'nc, 'ni) clash_rep =
  Cl_bottom "('ni)"
| Cl_contr_concept "('ni)" "('nc)"
*)

datatype ('nr, 'nc, 'ni) rule_rep =
  Clash_rep 
| ConjCRule_rep "('nr, 'nc, 'ni) form"
| DisjCRule_rep "('nr, 'nc, 'ni) form"
| AllCRule_rep "('nr, 'nc, 'ni) form"
| SomeCRule_rep "('ni)" "('nr, 'nc, 'ni) form"
| SubstCRule_rep "('nr, 'nc, 'ni) form"
| EqRule_rep "('nr, 'nc, 'ni) form"
| ConjFmRule_rep "('nr, 'nc, 'ni) form"
| DisjFmRule_rep "('nr, 'nc, 'ni) form"
| SubstFmRule_rep "('nr, 'nc, 'ni) form"
| ChooseRule_rep "('nr, 'nc, 'ni) form"
| NumrestrC_GeRule_rep "('nr, 'nc, 'ni) form"
| NumrestrC_Lt1Rule_rep "('nr, 'nc, 'ni) form"
| NumrestrC_LtRule_rep "('ni) list" "('nr, 'nc, 'ni) form"
| Todo_rep

datatype ('a, 'b) proof_result = 
  TablUnsatisf 'a
| TablSatisf 'b
| InternalError

datatype ('nr, 'nc, 'ni) prooftrace = 
  Trace "(('nr, 'nc, 'ni) rule_rep)" "(('nr, 'nc, 'ni) prooftrace list)"

datatype ('nr, 'nc, 'ni) trace_constr = 
  CTrace "('nr, 'nc, 'ni) prooftrace"       (* complete trace *)
| ITrace "(('nr, 'nc, 'ni) prooftrace list)" nat "(('nr, 'nc, 'ni) rule_rep)" (* incomplete trace *)

(* Result of application of proof rule. 
   Required for reconstruction of proof trace in fct. search_pt 
   Appres n rr ps: 
     - n: number of successors in proof tree
     - rr: representation of rule that has been applied (None if no rule applied)
     - ps: new branches created by rule application*)
     
datatype ('nr, 'nc, 'ni) apply_result = 
  AppRes nat "(('nr, 'nc, 'ni) rule_rep option)" "(('nr, 'nc, 'ni) proofstate)"

    (* ----------------------------------------------------------------------  *)
    (* Auxiliary functions  *)

definition bag_insert_front :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "bag_insert_front x xs = (if List.member xs x then xs else x#xs)"
definition bag_insert_end :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "bag_insert_end x xs = (if List.member xs x then xs else xs@[x])"

definition "set_of_pairs xs = 
  List.concat 
    (List.map (\<lambda> x1.
      List.concat (List.map (\<lambda> x2. if x1 < x2 then [(x1, x2)] else []) xs)) xs)"

definition "make_mutually_distinct nvrs = 
  List.map (\<lambda> (x, y). FactFm (Eq False x y)) (set_of_pairs nvrs)"

definition "make_outgoing_r_c_from x r c nvrs =
  (List.map (\<lambda> y. FactFm (AtomR True r x y)) nvrs) @
  (List.map (\<lambda> y. FactFm (Inst y  c)) nvrs)"

fun powerset :: "'a list \<Rightarrow> 'a list list" where
  "powerset [] = [[]]"
| "powerset (x#xs) = 
    (let p = powerset xs in
    (List.map (\<lambda> ys. x#ys) p) @ p)"

(* all the subsets of xs having size n *)
definition "n_subsets n xs = List.filter (\<lambda> ys. List.length ys = n) (powerset xs)"

       (* ----------------------------------------------------------------------  *)
    (* Proof state management *)

definition "add_new_form f br = (case br of Branch(n, alf, asf, ap, ia) \<Rightarrow>
  (Branch(f#n, alf, asf, ap, ia)))"

definition "add_new_forms fs br = (case br of (Branch(n, alf, asf, ap, ia)) \<Rightarrow>
  (Branch(fs@n, alf, asf, ap, ia)))"

definition "add_active_linear f br = (case br of (Branch(n, alf, asf, ap, ia)) \<Rightarrow>
  (Branch(n, bag_insert_front f alf, asf, ap, ia)))"

definition "add_active_splitting f br = (case br of (Branch(n, alf, asf, ap, ia)) \<Rightarrow>
  (Branch(n, alf, bag_insert_front f asf, ap, ia)))"

(* the new formula is added at the end to allow for a fair rule application *)
definition "add_active_permanent f br = (case br of (Branch(n, alf, asf, ap, ia)) \<Rightarrow>
  (Branch(n, alf, asf, bag_insert_end f ap, ia)))"

definition "add_inactive_composite f br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (Branch(n, alf, asf, ap, Inactive_form(bag_insert_front f ico, iac, iar, ie, icl))))"

definition "add_inactive_atomc f br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (Branch(n, alf, asf, ap, Inactive_form(ico, bag_insert_front f iac, iar, ie, icl))))"

definition "add_inactive_atomr f br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (Branch(n, alf, asf, ap, Inactive_form(ico, iac, bag_insert_front f iar, ie, icl))))"

definition "add_inactive_equivs f br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, bag_insert_front f ie, icl))))"

definition "add_inactive_clash f br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, bag_insert_front f icl))))"

(* some inequalities may have become clashes after equality substitutions. *)
definition "reactivate_equivs br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (Branch(n@ie, alf, asf, ap, Inactive_form(ico, iac, iar, [], icl))))"
  

(* The NegC case should be: failwith "negation in classify_concept" *)

definition "classify_concept br f = (case f of 
    FactFm(Inst x Bottom) \<Rightarrow> add_inactive_clash f br
  | FactFm(Inst x Top) \<Rightarrow> add_inactive_composite f br
  | FactFm(Inst x (AtomC sign a)) \<Rightarrow>  add_inactive_atomc f br
  | FactFm(Inst x (NegC c)) \<Rightarrow> add_inactive_composite f br
  | FactFm(Inst x (BinopC Conj c1 c2)) \<Rightarrow> add_active_linear f br
  | FactFm(Inst x (BinopC Disj c1 c2)) \<Rightarrow> add_active_splitting f br
  | FactFm(Inst x (NumRestrC Lt n r c)) \<Rightarrow> add_active_permanent f br
  | FactFm(Inst x (NumRestrC Ge n r c)) \<Rightarrow> add_active_linear f br
  | FactFm(Inst x (SubstC c sb)) \<Rightarrow> add_active_splitting f br
  | FactFm(Inst x (SomeC r c)) \<Rightarrow> add_active_linear f br
  | FactFm(Inst x (AllC r c)) \<Rightarrow> add_active_permanent f br)"

definition "classify_fact br f = (case f of 
    FactFm(Inst x c) \<Rightarrow> classify_concept br f
  | FactFm(AtomR sign r x y) \<Rightarrow> add_inactive_atomr f br
  | FactFm(Eq True x y) \<Rightarrow> 
    (if x = y 
     then add_inactive_composite f br
     else add_active_linear f br)
  | FactFm(Eq False x y) \<Rightarrow> 
    (if x = y 
     then add_inactive_clash f br
     else add_inactive_equivs f br))"

(* The NegFm case should be: failwith "negation in classify_form" *)
definition "classify_form br f = (case f of 
    (ConstFm False) \<Rightarrow> add_inactive_clash f br
  | (ConstFm True) \<Rightarrow> add_inactive_composite f br
  | (FactFm fct) \<Rightarrow> classify_fact br f
  | (NegFm f) \<Rightarrow> add_inactive_composite f br
  | (BinopFm Conj f1 f2) \<Rightarrow> add_active_linear f br
  | (BinopFm Disj f1 f2) \<Rightarrow> add_active_splitting f br
  | (SubstFm f1 sb) \<Rightarrow> add_active_splitting f br)"

(* all formulas in a branch that are not new, used during classification of formulas *)
definition "all_forms_not_new br = (case br of
  (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (alf @ asf @ ap @ ico @ iac @ iar @ ie @ icl))"

fun classify_new :: "('nr, 'nc, 'ni) proofbranch \<Rightarrow> ('nr, 'nc, 'ni) proofbranch" where
    "classify_new br = (case br of
    (Branch ([], alf, asf, ap, ia)) \<Rightarrow> br
  | (Branch ((nf # nfs), alf, asf, ap, ia)) \<Rightarrow> 
    (if List.member (all_forms_not_new br) nf
     then classify_new (Branch (nfs, alf, asf, ap, ia))
     else classify_form (Branch(nfs, alf, asf, ap, ia)) nf))"

    (* ----------------------------------------------------------------------  *)
    (* Number restrictions *)

    
definition "outgoing_rel_from_list lst x r =
  remdups 
    (List.foldl
       (\<lambda> res f.
         (case f of
          FactFm (AtomR sign r' x' y) \<Rightarrow> if sign \<and> x = x' \<and> r = r' then y#res else res
         | _ \<Rightarrow> res))
       []
       lst)"

definition "outgoing_rel_from_branch br x r =
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  outgoing_rel_from_list iar x r)"

definition "having_class_list lst x c =
  list_ex
    (\<lambda> f. (case f of
      FactFm (Inst x' c') \<Rightarrow> x = x' \<and> c = c' 
    | _ \<Rightarrow> False))
    lst"
    
definition "having_class_branch br x c =
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow> 
   having_class_list (alf @ asf @ ico @ iac) x c)"

definition "unequal_in_list lst x1 x2 =
    ((List.member lst (FactFm(Eq False x1 x2))) \<or> (List.member lst (FactFm(Eq False x2 x1))))"
definition "unequal_in_branch br x1 x2 =
   (case br of  (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
     unequal_in_list ie x1 x2)"

definition "mutually_distinct_list lst xs = 
  list_all (\<lambda> x1. list_all (\<lambda> x2. x1 = x2 \<or> unequal_in_list lst x1 x2) xs) xs"
definition "mutually_distinct_branch br xs = 
  list_all (\<lambda> x1. list_all (\<lambda> x2. x1 = x2 \<or> unequal_in_branch br x1 x2) xs) xs"

definition "exist_outgoing_r_c_distincts_from_list lst x n r c = 
  (let ys_outgoing = outgoing_rel_from_list lst x r in
  let ys_c = List.filter (\<lambda> y. having_class_list lst y c) ys_outgoing in
  let ns = n_subsets n ys_c in 
  list_ex (mutually_distinct_list lst) ns)"
definition "exist_outgoing_r_c_distincts_from_branch br x n r c = 
  (let ys_outgoing = outgoing_rel_from_branch br x r in
  let ys_c = List.filter (\<lambda> y. having_class_branch br y c) ys_outgoing in
  let ns = n_subsets n ys_c in 
  list_ex (mutually_distinct_branch br) ns)"

definition "numrestrc_ge_applicable_branch br x n r c =
  (\<not> (exist_outgoing_r_c_distincts_from_branch br x n r c))"

definition "numrestrc_lt_applicable_vars_branch br x n r c = 
  (let ys_outgoing = remdups (outgoing_rel_from_branch br x r) in
  let ys_c = List.filter (\<lambda> y. having_class_branch br y c) ys_outgoing in
  if List.length ys_c < n
  then []
  else 
    let pys = set_of_pairs ys_c in
    List.filter (\<lambda> (x1, x2). \<not> (unequal_in_branch br x1 x2)) pys)"

definition "numrestrc_lt_applicable_branch br x n r c = 
  (\<not> (numrestrc_lt_applicable_vars_branch br x n r c = []))"

definition "choose_applicable_vars_branch br x r c = 
  (let ys_outgoing = remdups (outgoing_rel_from_branch br x r) in
  let ys_c = List.filter (\<lambda> y. having_class_branch br y c) ys_outgoing in
  let not_c = (neg_norm_concept False c) in
  let ys_not_c = List.filter (\<lambda> y. having_class_branch br y not_c) ys_outgoing in
  let ys_undet = List.filter (\<lambda> y. \<not> (List.member ys_c y) \<and> \<not> (List.member ys_not_c y)) ys_outgoing in
  let ys_contrad = list_inters ys_c ys_not_c in
  (ys_undet, ys_contrad))"

definition "choose_applicable_in_branch br x r c = (\<not> (fst (choose_applicable_vars_branch br x r c) = []))"

    (* ----------------------------------------------------------------------  *)
    (* Rule application *)

definition "all_forms br = (case br of
  (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  (n @ alf @ asf @ ap @ ico @ iac @ iar @ ie @ icl))"

definition "conjc_applicable_branch br x c1 c2 = 
  (let fs = all_forms br in 
  \<not> (List.member fs (FactFm(Inst x c1)) \<and> List.member fs (FactFm(Inst x c2)) ))"

definition "disjc_applicable_branch br x c1 c2 = 
  (let fs = all_forms br in 
  \<not> (List.member fs (FactFm(Inst x c1))) \<and> \<not> (List.member fs (FactFm(Inst x c2))))"

definition "conjfm_applicable_branch br f1 f2 = 
  (let fs = all_forms br in \<not> (List.member fs f1 \<and> List.member fs f2))"

definition "disjfm_applicable_branch br f1 f2 = 
  (let fs = all_forms br in \<not> (List.member fs f1) \<and> \<not> (List.member fs f2))"

definition "substc_applicable_branch br fp = 
  (let fs = all_forms br in \<not> (List.member fs fp))"

  definition "substfm_applicable_branch br fp = 
  (let fs = all_forms br in \<not> (List.member fs fp))"

definition "inactive_form_apply f iaf = 
  (case iaf of (Inactive_form(ico, iac, iar, ie, icl)) \<Rightarrow> 
  (Inactive_form( (f ico), (f iac), (f iar), (f ie), (f icl))))"

definition "branch_apply f br = 
  (case br of (Branch(n, alf, asf, ap, ia)) \<Rightarrow> 
  (Branch(f n, f alf, f asf, f ap, inactive_form_apply f ia)))"
  
definition "propagate_equality x y xs = 
  remdups (List.map (\<lambda> frm. rename_in_form frm [ISubst x y]) xs)"

definition "fv_branch br = 
   (let fs = all_forms br in 
    List.foldl (\<lambda> res vs. (fv_form_list vs) @ res) [] fs)"


(*
declare [[show_types]]
declare [[show_sorts]]
*)
definition numrestrc_ge_generated ::  
   "('nr, 'nc, 'ni::{new_var_list_class, ord}) proofbranch \<Rightarrow> 'ni \<Rightarrow> nat \<Rightarrow> 'nr 
   \<Rightarrow> ('nr, 'nc, 'ni) concept \<Rightarrow> ('nr, 'nc, 'ni) form list" where
"numrestrc_ge_generated br x n r c = 
  (let vrs = fv_branch br in
   let nvrs = new_vars_list n vrs x in
   make_mutually_distinct nvrs @ make_outgoing_r_c_from x r c nvrs)"
  
definition "apply_conjc_branch br f x c1 c2 = 
   (if conjc_applicable_branch br x c1 c2
    then  
      AppRes 1 (Some (ConjCRule_rep f)) 
            [add_new_forms [FactFm (Inst x c2), FactFm (Inst x c1)]
                           (add_inactive_composite f br)]
    else AppRes 0 None [add_inactive_composite f br])"

definition "apply_conjfm_branch br f f1 f2 =
   (if conjfm_applicable_branch br f1 f2
    then
      AppRes 1 (Some (ConjFmRule_rep f)) [add_new_forms [f2, f1] (add_inactive_composite f br)]
    else AppRes 0 None [add_inactive_composite f br])"

definition "apply_numrestrc_ge_branch br f x n r c = 
  (if n = 0 
   then AppRes 0 None [add_inactive_composite f br]
   else if numrestrc_ge_applicable_branch br x n r c
        then AppRes 1 (Some (NumrestrC_GeRule_rep f))
                [add_new_forms 
                    (numrestrc_ge_generated br x n r c)
                    (add_inactive_composite f br)]
        else AppRes 0 None [add_inactive_composite f br])"

definition "apply_substc_branch br f = 
  (let fp = (neg_norm_form True (push_subst_form f [])) in
    if substc_applicable_branch br fp
    then AppRes 1 (Some (SubstCRule_rep f)) [add_new_form fp (add_inactive_composite f br)]
    else AppRes 0 None [add_inactive_composite f br])"

definition "apply_substfm_branch br f = 
  (let fp = (neg_norm_form True (push_subst_form f [])) in
    if substfm_applicable_branch br fp
    then AppRes 1 (Some (SubstFmRule_rep f)) [add_new_form fp (add_inactive_composite f br)]
    else AppRes 0 None [add_inactive_composite f br])"

definition "apply_linear br f = (case f of 
    FactFm (Inst x (BinopC Conj c1 c2)) \<Rightarrow> apply_conjc_branch br f x c1 c2
  | FactFm (Inst x (NumRestrC Ge n r c)) \<Rightarrow> apply_numrestrc_ge_branch br f x n r c
  | FactFm (Eq True x y) \<Rightarrow> 
         AppRes 1 (Some (EqRule_rep f)) 
           [reactivate_equivs
               (branch_apply (propagate_equality x y) (add_inactive_composite f br))]
  | BinopFm Conj f1 f2 \<Rightarrow> apply_conjfm_branch br f f1 f2
  | _ \<Rightarrow> AppRes 0 None [add_inactive_composite f br])"
  
  
definition "apply_disjc_branch br f x c1 c2 = 
   (if disjc_applicable_branch br x c1 c2
    then
      AppRes 2 (Some (DisjCRule_rep f)) 
        [add_new_form (FactFm (Inst x c1)) (add_inactive_composite f br),
         add_new_form (FactFm (Inst x c2)) (add_inactive_composite f br)]
    else AppRes 0 None [add_inactive_composite f br])"

definition "apply_disjfm_branch br f f1 f2 =
   (if disjfm_applicable_branch br f1 f2
    then
      AppRes 2 (Some (DisjFmRule_rep f)) 
        [add_new_form f1 (add_inactive_composite f br),
         add_new_form f2 (add_inactive_composite f br)]
    else AppRes 0 None [add_inactive_composite f br])"

(* TODO
  | FactFm(Inst(x, SomeC(r, c))) ->
  | FactFm(Inst(x, AllC(r, c))) ->
*)

definition "apply_splitting br f = (case f of 
    FactFm(Inst x (BinopC Disj c1 c2)) \<Rightarrow> apply_disjc_branch br f x c1 c2
  | FactFm (Inst x (SubstC c sb)) \<Rightarrow> apply_substc_branch br f 
  | BinopFm Disj f1 f2 \<Rightarrow> apply_disjfm_branch br f f1 f2
  | SubstFm f1 sb \<Rightarrow> apply_substfm_branch br f 
  | _ \<Rightarrow> AppRes 0 None [add_inactive_composite f br])"

  (* TODO: needs a closer look:
  - can the AppRes 1 case ever occur for a non-clashed branch?
  - deal with rule numrestrc_lt_1. 
     Is that rule really needed? Interaction with Choose rule to be explored
  *)
definition "apply_permanent br f = (case f of 
    FactFm(Inst x (NumRestrC Lt n r c)) \<Rightarrow> 
      (case numrestrc_lt_applicable_vars_branch br x n r c of
        [] \<Rightarrow> 
        (case choose_applicable_vars_branch br x r c of 
          ([], []) \<Rightarrow> AppRes 0 None [(add_active_permanent f br)]
        | ([], _) \<Rightarrow> AppRes 1 (Some Todo_rep) [(add_inactive_clash (ConstFm False) br)]
        | (y#ys, _) \<Rightarrow> AppRes 2 (Some (ChooseRule_rep f))
                       [add_new_form (FactFm (Inst y c)) (add_active_permanent f br),
                        add_new_form (FactFm(Inst y (neg_norm_concept False c))) (add_active_permanent f br)]
        )
      | varpairs \<Rightarrow> AppRes(List.length varpairs) (Some Todo_rep) 
             (List.map
               (\<lambda> (x, y) \<Rightarrow> add_new_form (FactFm (Eq True x y)) (add_active_permanent f br))
               varpairs)
      )
  | _ \<Rightarrow> AppRes 0 None [add_inactive_composite f br])"


      
    (* ----------------------------------------------------------------------  *)
    (* Clashes *)

definition "is_bottom f = (case f of 
    FactFm (Inst x Bottom) \<Rightarrow> True
  | _ \<Rightarrow> False)"

definition "is_neg_concept f fn = (case fn of 
    FactFm (Inst x (AtomC sign a)) \<Rightarrow> (f = (FactFm (Inst x (AtomC (\<not> sign) a))))
  | _ \<Rightarrow> False)"

definition "is_neg_role f fn = (case fn of 
    FactFm (AtomR sign r x y) \<Rightarrow> (f = (FactFm (AtomR(\<not> sign) r x y)))
  | _ \<Rightarrow> False)"

definition "is_ineq_inst f = (case f of 
    FactFm (Eq False x y) \<Rightarrow> (x = y)
  | _  \<Rightarrow> False)"

definition "is_falsefm f = (case f of 
    ConstFm False \<Rightarrow> True
  | _ \<Rightarrow> False)"

(* the following three are subsumed by nonempty_clashset *)
definition "contains_bottom_list lst = (List.list_ex is_bottom lst)"
definition "contains_bottom_branch br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
    contains_bottom_list icl)"

definition "contains_falsefm_list lst = List.list_ex is_falsefm lst"
definition "contains_falsefm_branch br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
    contains_falsefm_list icl)"

definition "contains_contr_eq_list lst = List.list_ex is_ineq_inst lst"
definition "contains_contr_eq_branch br =
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow> 
   contains_contr_eq_list icl)"

definition "nonempty_clashset_branch br =
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow>
  \<not> (icl = []) ) "

definition "contains_contr_concept_list lst =
  List.list_ex (\<lambda> f. List.list_ex (is_neg_concept f) lst) lst"
definition "contains_contr_concept_branch br =
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow> 
    contains_contr_concept_list iac)"

definition "contains_contr_role_list lst =
  List.list_ex (\<lambda> f. List.list_ex (is_neg_role f) lst) lst"
definition "contains_contr_role_branch br = 
  (case br of (Branch(n, alf, asf, ap, Inactive_form(ico, iac, iar, ie, icl))) \<Rightarrow> 
  contains_contr_role_list iar)"


definition "contains_numrestrc_clash_list lst =
  List.list_ex
    (\<lambda> f. case f of 
     FactFm(Inst x (NumRestrC Lt n r c)) \<Rightarrow> 
      if n = 0
      then True
      else exist_outgoing_r_c_distincts_from_list lst x n r c
    | _ \<Rightarrow> False
    )
    lst"

definition "contains_numrestrc_clash_branch br = 
  (case br of (Branch(n, alf, asf, ap, ia)) \<Rightarrow>
  List.list_ex
    (\<lambda> f. case f of 
     FactFm(Inst x (NumRestrC Lt n r c)) \<Rightarrow> 
      if n = 0
      then True
      else exist_outgoing_r_c_distincts_from_branch br x n r c
    | _ \<Rightarrow> False
    )
    ap)"

(* don't try looking for a clash as long as there are new formulas *)
definition "contains_clash_branch br = (case br of 
    (Branch([], _, _, _, _)) \<Rightarrow>
    (nonempty_clashset_branch br \<or>
     contains_contr_concept_branch br \<or>
     contains_contr_role_branch br \<or>
     contains_contr_eq_branch br \<or>
     contains_falsefm_branch br \<or>
     contains_numrestrc_clash_branch br)
  | _ \<Rightarrow> False)"

  
    (* ----------------------------------------------------------------------  *)
    (* Search *)

definition "is_applicable_permanent br f = (case f of 
    FactFm(Inst x (NumRestrC Lt n r c)) \<Rightarrow>
    (choose_applicable_in_branch br x r c \<or> numrestrc_lt_applicable_branch br x n r c)
  | _ \<Rightarrow> False)"

definition "is_inactive br = (case br of
    (Branch([], [], [], ap, ia)) \<Rightarrow> list_all (\<lambda> f. (\<not> (is_applicable_permanent br f))) ap
  | _ \<Rightarrow> False)"
  
definition "map_classify_branches ar = 
  (case ar of (AppRes n rr_opt brs) \<Rightarrow> AppRes n rr_opt (List.map classify_new brs))"

  
fun apply_rules_pt :: "('nr, 'nc, 'ni::{new_var_list_class, ord}) proofbranch \<Rightarrow> ('nr, 'nc, 'ni) apply_result" where
     (* in fact an error case: *)
     "apply_rules_pt (Branch ([], [], [], [], ia)) = AppRes 0 None [Branch ([], [], [], [], ia)]"
  | "apply_rules_pt (Branch ([], [], [], (apf#apfs), ia)) = 
    map_classify_branches (apply_permanent (Branch ([], [], [], apfs, ia)) apf)"
  | "apply_rules_pt (Branch ([], [], (asf#asfs), ap, ia)) =
    map_classify_branches (apply_splitting (Branch ([], [], asfs, ap, ia)) asf)"
  | "apply_rules_pt (Branch ([], (alf#alfs), asf, ap, ia)) =
    map_classify_branches (apply_linear (Branch ([], alfs, asf, ap, ia)) alf)"
  | "apply_rules_pt br = AppRes 0 None [classify_new br]"
  
end

