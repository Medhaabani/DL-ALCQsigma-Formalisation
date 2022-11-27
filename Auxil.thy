(*<*)
theory Auxil imports Main
begin
(*>*)

section {* Auxiliary definitions \label{sec:aux} *}


  (* Function rel_restrict *)
definition rel_restrict :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
 "rel_restrict R A B =  (R \<inter> (A \<times> B))"

definition dom_of_range_restrict :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> 'a set" where
 "dom_of_range_restrict R C = (Domain (rel_restrict R UNIV C))"

lemma self_member_UNION [rule_format]: "\<forall> c. c \<in> B c \<Longrightarrow> A \<subseteq> UNION A B"
by auto

(*--------- Set operations implemented on lists ----------------*)


fun list_max :: "nat list \<Rightarrow> nat"  where
  "list_max [] = 0"
  | "list_max (x # xs) = max x (list_max xs)"

fun list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_diff [] ys = []"
| "list_diff (x#xs) ys = (if (x : set ys) then list_diff xs ys else x # (list_diff xs ys))"

fun list_distrib ::  " 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list " where
  "list_distrib xs ys = map (\<lambda> x. (x# ys)) xs"

fun list_inters :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "list_inters xs ys = List.filter (List.member ys) xs"

fun list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_union xs ys = remdups (xs @ ys)"

definition list_Union :: "'a list list \<Rightarrow> 'a list" where
  "list_Union xss = List.foldr List.union xss []"

definition list_remove :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_remove xs ys = List.foldr (List.removeAll) ys xs"

(*<*)
end
(*>*)
