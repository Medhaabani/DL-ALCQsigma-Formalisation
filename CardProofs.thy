(*<*)
theory CardProofs imports Card AuxilProofs
begin
(*>*)

section {* Cardinalities of sets (Proofs) *}

lemma card_lt_0 [simp]: "card_lt B 0 = False"
by (simp add: card_lt_def)

lemma card_ge_0 [simp]: "card_ge B 0"
by (simp add: card_ge_def)

lemma not_card_lt_card_ge [simp]: " (\<not> (card_lt B n)) = card_ge B n"
apply (simp add: card_ge_def card_lt_def)
apply arith
done

lemma not_card_ge_card_lt [simp]: " (\<not> (card_ge B n)) = card_lt B n"
apply (simp add: card_ge_def card_lt_def)
apply arith
done

lemma empty_finite: "\<forall> a. a \<notin> A \<Longrightarrow> finite A"
by auto

lemma non_finite_non_empty: "\<not> finite A \<Longrightarrow> \<exists> a. a \<in> A"
apply (insert empty_finite [of A])
apply blast
done

lemma card_lt_Suc_insert: "a \<notin> B \<Longrightarrow> card_lt (insert a B) (Suc n) = card_lt B n"
by (auto simp add: card_lt_def)

lemma card_ge_Suc_insert: "a \<notin> B \<Longrightarrow> card_ge (insert a B) (Suc n) = card_ge B n"
by (auto simp add: card_ge_def)

lemma card_lt_Suc_diff: "a \<in> B \<Longrightarrow> card_lt (B - {a}) n = card_lt B (Suc n)"
apply (insert card_lt_Suc_insert [of a "B - {a}" n])
apply (subgoal_tac "insert a B = B")
apply auto
done

lemma card_ge_Suc_diff: "a \<in> B \<Longrightarrow> card_ge (B - {a}) n = card_ge B (Suc n)"
apply (insert card_ge_Suc_insert [of a "B - {a}" n])
apply (subgoal_tac "insert a B = B")
apply auto
done

lemma card_lt_Range_rel_restrict: "card_lt (Range (rel_restrict R {x} C)) = card_lt  {y. ((x,y) \<in> R \<and> y \<in> C)}"
  by (rule arg_cong) (fastforce simp add:  rel_restrict_def) 

(*<*)
end
(*>*)
