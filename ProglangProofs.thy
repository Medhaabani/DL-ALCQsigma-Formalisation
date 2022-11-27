(*<*)
theory ProglangProofs imports Proglang SemanticsProofs VariablesProofs SubstProofs
begin
(*>*)

section {* Programming language (Proofs) \label{sec:proglang} *}

lemma well_formed_interp_pres_add_node [simp]: 
  "well_formed_interp s \<Longrightarrow> well_formed_interp (add_node v c s)"
by (simp add: well_formed_interp_def add_node_def)

lemma well_formed_interp_pres_delete_node [simp]: 
  "well_formed_interp s \<Longrightarrow> well_formed_interp (delete_node v c s)"
by (simp add: well_formed_interp_def delete_node_def) blast
  
lemma well_formed_interp_pres_add_edge [simp]: 
  "well_formed_interp s \<Longrightarrow> well_formed_interp (add_edge v1 r v2 s)"
by (simp add: well_formed_interp_def add_edge_def)

lemma well_formed_interp_pres_delete_edge [simp]: 
  "well_formed_interp s \<Longrightarrow> well_formed_interp (delete_edge v1 r v2 s)"
by (simp add: well_formed_interp_def delete_edge_def) blast

lemma well_formed_interp_pres_interp_i_modif [simp]:
  "well_formed_interp s \<Longrightarrow> vi \<in> interp_d s \<Longrightarrow> well_formed_interp (interp_i_modif v vi s)"
by (simp add: well_formed_interp_def interp_i_modif_def) 

lemma well_formed_interp_pres_interp_i_modif_list [rule_format, simp]:
  "length vs = length vis \<Longrightarrow>
  well_formed_interp s \<Longrightarrow>
  set vis \<subseteq> interp_d s \<longrightarrow> 
  well_formed_interp (interp_i_modif_list (zip vs vis) s)"
by (induct vs vis arbitrary: s rule: list_induct2) auto

lemma well_formed_interp_big_step [rule_format,elim]:
   "(c, s) \<Rightarrow> s' \<Longrightarrow> well_formed_interp s \<longrightarrow> well_formed_interp s'"
apply (induct rule: big_step_induct)
apply simp_all
apply clarsimp
done

(*<*)
end
(*>*)
