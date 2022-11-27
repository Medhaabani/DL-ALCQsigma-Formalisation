(*<*)
theory New_Var imports Fresh String AuxilProofs 
begin
(*>*)

  (* ---------------------------------------------------------------------- *)
section {* Generating new variable names *}
  (* ---------------------------------------------------------------------- *)


(* new_var_list and new_var_set: 
   first parameter: list / set of already used names
   second parameter: suggestion for new name *)
class new_var_list_class = 
  fixes new_var_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes new_var_gen_list: "(new_var_list vs v \<notin> set vs) "
  (*
  and  eq_new_var_list: "( (set vs = set vs1)  \<Longrightarrow> ( new_var_list vs = new_var_list vs1))"
*)

class new_var_set_class = 
  fixes new_var_set :: "'a set \<Rightarrow> 'a::linorder \<Rightarrow> 'a"
  assumes new_var_gen_set [rule_format]: "\<forall> vs. finite vs \<longrightarrow> (new_var_set vs v \<notin> vs) "

class new_var_set_incr_class = 
  fixes new_var_set_incr :: "'a set \<Rightarrow> 'a::linorder \<Rightarrow> 'a"
  assumes new_var_gen_set_incr [rule_format]: 
     "\<forall> vs. finite vs \<longrightarrow> (\<forall> vo. vo < new_var_set_incr vs v) "


(* Generate a set of n new varnames *)
fun new_vars_set :: "nat \<Rightarrow> ('ni::new_var_set_class) set \<Rightarrow> 'ni \<Rightarrow> 'ni set" where
  "new_vars_set 0 vns vn = {}" |
  "new_vars_set (Suc n) vns vn =
    (let nvar = (new_var_set vns vn) in 
     insert nvar (new_vars_set n (insert nvar vns) vn))" 

fun new_vars_set_incr :: "nat \<Rightarrow> ('ni::new_var_set_incr_class) set \<Rightarrow> 'ni \<Rightarrow> 'ni set" where
  "new_vars_set_incr 0 vns vn = {}" |
  "new_vars_set_incr (Suc n) vns vn =
    (let nvar = (new_var_set_incr vns vn) in 
     insert nvar (new_vars_set_incr n (insert nvar vns) vn))" 
     
instantiation nat :: new_var_list_class
begin
definition
  new_var_list_nat_def: "new_var_list vs v = (Suc (list_max vs))"
instance proof
  case goal1 thus ?case 
    by (simp add: new_var_list_nat_def list_max_Suc)
qed
end   (* nat :: new_var_list_class *)

    
fun new_vars_list :: "nat \<Rightarrow> ('ni::new_var_list_class) list \<Rightarrow> 'ni \<Rightarrow> 'ni list" where
  "new_vars_list 0 vns vn = []" |
  "new_vars_list (Suc n) vns vn =
    (let nvar = (new_var_list vns vn) in 
     nvar # (new_vars_list n (nvar # vns) vn))" 


(*** String type ***)
(* Isomorphic to char list, not a dataype. 
   Therefore, it has to be encapsulated as string_dt 
*)
datatype string_dt = String string
fun unstring :: "string_dt \<Rightarrow> string" where 
"unstring (String str) = str"

fun fresh_string :: "string_dt list \<Rightarrow> string_dt \<Rightarrow> string_dt" where
"fresh_string strs str = String (fresh (List.map unstring strs) (unstring str))"

lemma fresh_string_set: "fresh_string vs v \<notin> set vs"
apply simp
apply (subgoal_tac "fresh (List.map unstring vs) (unstring v) \<notin> set (List.map unstring vs)") 
  prefer 2 apply (rule fresh_set)
apply clarsimp
apply (subgoal_tac "unstring (String  (fresh (map unstring vs) (unstring v)))  \<in> unstring ` set vs")
prefer 2 apply  (erule Set.imageI)
apply simp
done

instantiation string_dt :: new_var_list_class
begin
definition
  new_var_list_string_dt_def: "new_var_list = fresh_string"
instance proof
  case goal1 thus ?case 
    by (simp add: new_var_list_string_dt_def fresh_string_set del: fresh_string.simps)
qed
end   (* string_dt :: new_var_list_class *)

(*** String.literal type ***)
(* Is mapped to native strings by code extraction. To be preferred. 
*)

fun fresh_string_literal :: 
"String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
"fresh_string_literal strs str = String.implode (fresh (List.map String.explode strs) (String.explode str))" 

lemma string_implode_explode [simp]: "String.implode (String.explode x) = x"
by (simp add: String.implode_def String.literal.explode_inverse)

lemma string_explode_implode [simp]: "String.explode (String.implode x) = x"
by (simp add: String.implode_def ) (simp add: String.literal.STR_inverse)

lemma fresh_string_literal_set: "fresh_string_literal vs v \<notin> set vs"
apply clarsimp
apply (subgoal_tac "fresh (List.map String.explode vs) (String.explode v) \<notin> set (List.map String.explode vs)") 
  prefer 2 apply (rule fresh_set)
apply clarsimp
apply (subgoal_tac "String.explode (String.implode (fresh (List.map String.explode vs) (String.explode v)))  \<in> String.explode ` set vs")
prefer 2 apply  (erule Set.imageI)
apply simp 
done

instantiation "String.literal" :: new_var_list_class
begin
definition
  new_var_list_literal_def: "new_var_list = fresh_string_literal"
instance proof
  case goal1 thus ?case 
    by (simp add: new_var_list_literal_def fresh_string_literal_set del: fresh_string_literal.simps)
qed
end   (* String.literal :: new_var_list_class *)

(*<*)
end
(*>*)

