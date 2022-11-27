(*<*)
theory Card imports Main
begin
(*>*)

section {* Cardinalities of sets; finite and infinite sets \label{sec:card} *}

definition card_lt :: "'a set \<Rightarrow> nat \<Rightarrow> bool" where
 "card_lt B n == ((finite B) \<and> (card B < n))"

definition  card_ge :: "'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "card_ge B n == ((\<not> (finite B)) \<or> (card B \<ge> n))"


(*<*)
end
(*>*)
