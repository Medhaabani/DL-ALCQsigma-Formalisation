(*<*)
theory AuxilProofs imports Auxil
begin
(*>*)

section {* Auxiliary definitions (Proofs) *}
(* Propositional logic *)

lemma mp_obj [simp]: "(A \<and> (A \<longrightarrow> B)) = (A \<and> B)"
by blast
lemma mp_obj2 [simp]: "((A \<longrightarrow> B) \<and> A) = (A \<and> B)"
by blast

lemma triv_inequality1 [simp]: "(\<forall> x. x \<noteq> y) = False"
by blast

lemma triv_inequality2 [simp]: "(\<forall> x. y \<noteq> x) = False"
by blast


lemma card_greater_0_nonempty: "finite A \<Longrightarrow> (0 < card A) = (\<exists> x. x \<in> A)"
apply (case_tac "A = {}")
apply simp
apply (rule)
apply auto
done


-- "Absorption rules"
lemmas absorb = Un_Int_distrib Un_Int_distrib2 Int_absorb1 Int_absorb2 Un_upper1 Un_upper2


(* Map *)

lemma map_le_implies_ran_le: "m \<subseteq>\<^sub>m m' \<Longrightarrow> ran m \<subseteq> ran m'"
by (fastforce simp add: dom_def ran_def map_le_def)

lemma image_dom: "m ` dom m = Some ` (ran m)"
by (auto simp add: image_def dom_def ran_def)

lemma image_dom_ran: "(the \<circ> m) ` dom m = ran m"
by (auto simp add: dom_def ran_def image_def)

lemma finite_dom_ran: "finite (dom m) \<Longrightarrow> finite (ran m)"
by (simp add: image_dom_ran [THEN sym])

lemma Some_the_map [simp]: "x \<in> dom m \<Longrightarrow> Some (the (m x)) = m x"
by (clarsimp simp add: dom_def)

lemma ran_map_upd_notin_dom: "a \<notin> dom m \<Longrightarrow> ran (m(a \<mapsto> b)) = ran m \<union> {b}"
by auto

lemma ran_map_upd_subset: "ran (m(a \<mapsto> b)) \<subseteq> ran m \<union> {b}"
by (auto simp add: ran_def)


lemma image_fun_upd: "
  (m ` ((f(x:=y)) e)) = (if e = x then m ` y else m ` (f e))"
by (clarsimp simp add: fun_upd_def image_def)

(* Injective map *)

lemma inj_on_map_upd:
  "a \<notin> dom m \<Longrightarrow> inj_on (m(a \<mapsto> b)) (dom m) =  inj_on m (dom m)"
apply (rule iffI)

apply (clarsimp simp add: inj_on_def)
apply (drule_tac bspec) prefer 2
apply (drule_tac bspec) prefer 2
apply (drule mp) prefer 2
apply assumption
apply (auto simp add: inj_on_def)
done


(* Inversion of a map *)

lemma restrict_map_le [simp]: "m |` A \<subseteq>\<^sub>m m"
by (simp add: map_le_def)

lemma restrict_map_le_in_dom: "\<lbrakk> m \<subseteq>\<^sub>m m'; dom m \<subseteq> A \<rbrakk> \<Longrightarrow> m \<subseteq>\<^sub>m m' |` A"
by (fastforce simp add: map_le_def )

lemma restrict_map_Some: "((m |` A) x = Some y) = (m x = Some y \<and> x \<in> A)"
by (simp add: restrict_map_def)

(* restriction of a map *)
lemma restrict_map_le_eq: "((m|`A)  \<subseteq>\<^sub>m (m|`B)) = (dom m \<inter> A \<subseteq> B)"
apply (rule iffI)
apply (frule map_le_implies_dom_le) apply (fastforce simp only: dom_restrict) 
apply (simp add: map_le_def) apply (fastforce simp add: restrict_map_def)
done

lemma restrict_map_dom [simp]: "m \<subseteq>\<^sub>m m' \<Longrightarrow> m' |` (dom m) = m"
apply (rule map_le_antisym)
apply (simp add: restrict_map_def map_le_def dom_def)
apply (erule restrict_map_le_in_dom) apply simp
done

lemma restrict_map_dom_subset: "dom m \<subseteq> A \<Longrightarrow> m |` A = m"
apply (rule  map_le_antisym)
apply simp
apply (simp add: restrict_map_le_in_dom)
done

lemma ran_restrict_iff: "(y \<in> ran (m |` A)) = (\<exists>x\<in>A. m x = Some y)"
apply (rule iffI)
apply (erule ran_restrictD)
apply (auto simp add: ran_def restrict_map_def)
done


(* Relation *)

lemma Field_insert [simp]: "Field (insert (a,a') A) = {a,a'} \<union> Field A"
by (fastforce simp add: Field_def Domain_unfold Domain_converse [symmetric])

lemma finite_Image: "finite (Field R) \<Longrightarrow> finite (R `` S)"
apply (rule finite_subset [where B="Range R"])
apply (auto simp add: Field_def)
done

lemma Image_Field_subset [simp]: "(R `` S) \<subseteq> Field R"
by (auto simp add: Field_def)

lemma Field_converse [simp]: "Field (R^-1) = Field R"
by (auto simp add: Field_def)

lemma Field_Un: "Field (R \<union> S) = (Field R  \<union> Field S)"
by (auto simp add: Field_def)

lemma Field_prod [simp]: "Field (A \<times> A) = A"
by (auto)

lemma Field_product_subset: "(A \<subseteq> B \<times> B) = (Field A \<subseteq> B)"
by (fastforce simp add: Field_def)

lemma Field_Diff_subseteq: "Field (R - S) \<subseteq> Field R"
by (auto simp add: Field_def)

lemma in_Field: "(a, b) \<in> R \<Longrightarrow> {a,b} \<subseteq> Field R"
by (fastforce simp add: Field_def Domain_unfold Domain_converse [symmetric])

lemma converse_insert: "(insert (x, y) R)\<inverse> = insert (y, x) (R\<inverse>)"
by (unfold insert_def) (auto simp add: converse_Un)

lemma converse_Diff: "(R - S)\<inverse> = R\<inverse> -  S\<inverse>"
by auto

lemma Diff_Image: "(R - S) `` {x} = R `` {x} - S `` {x}"
by blast

lemma finite_rel_finite_Field: "\<lbrakk> Field R \<subseteq> A; finite A \<rbrakk> \<Longrightarrow> finite R"
apply (subgoal_tac "R \<subseteq> A \<times> A")
apply (rule finite_subset) apply assumption+
apply (fast intro: finite_cartesian_product)
apply (fastforce simp add: Field_def)
done

lemma insert_Image_split:
  "((insert (a, b) R) `` {c}) = ((if a = c then {b}  else {}) \<union> (R `` {c}))"
by auto


lemma Image_rel_empty [simp]: "{} `` A = {}"
by auto

lemma converse_mono: "A \<subseteq> B \<Longrightarrow> (A)\<inverse> \<subseteq> (B)\<inverse>"
by auto

  (* Function rel_restrict *)

lemma dom_of_range_restrict_expanded: "dom_of_range_restrict R C = { x. \<exists>y. ((x,y) \<in> R \<and> y \<in> C)}"
by (fastforce simp add: dom_of_range_restrict_def rel_restrict_def)


lemma rel_restrict_diff: "rel_restrict (R1 - R2) A B = (((rel_restrict R1) A B) - ((rel_restrict R2) A B))"
by (simp add: rel_restrict_def) blast

lemma rel_restrict_insert: "rel_restrict (insert (x, y) R) A B = 
  (if (x \<in> A \<and> y \<in> B) then (insert (x, y) (rel_restrict R A B)) else (rel_restrict R A B))"
by (simp add: rel_restrict_def)

lemma rel_restrict_empty [simp]: "rel_restrict {} A B = {}"
by (simp add: rel_restrict_def)


lemma rel_restrict_remove: "b \<in> B \<Longrightarrow>  (a, b) \<in> R \<Longrightarrow>
  Range ((rel_restrict R {a} B) - {(a, b)}) = ((Range (rel_restrict R {a} B)) - {b})"
by (simp add: rel_restrict_def) blast


lemma rel_restrict_remove_from_rel: 
  "b \<in> B \<Longrightarrow> (Range (rel_restrict (R - {(a, b)}) {a} B)) = Range (rel_restrict R {a} B) - {b}"
by (auto simp add: rel_restrict_def)

lemma Range_Image: "Range (r \<inter> A \<times> C) = (r `` A) \<inter> C"
by (fastforce simp add: Image_def Range.simps intro: set_eqI)

lemma map_add_dom_disj1: "\<lbrakk>dom tt1 \<inter> dom tt2 = {}; tt1 b = Some ntp' \<rbrakk> 
  \<Longrightarrow> (tt1 ++ tt2) b = Some ntp'"
by (auto simp add: map_add_Some_iff)

lemma map_add_dom_disj2: "\<lbrakk>dom tt1 \<inter> dom tt2 = {}; tt2 b = Some ntp' \<rbrakk> 
  \<Longrightarrow> (tt1 ++ tt2) b = Some ntp'"
by (auto simp add: map_add_Some_iff)

lemma map_add_disj:
  "\<lbrakk> (m1 ++ m2) x = Some x'; dom m1 \<inter> dom m2 = {} \<rbrakk> \<Longrightarrow> (m1 x = Some x') \<or> (m2 x = Some x')"
by auto

(* TODO: remove
lemma dom_map_comp: "ran g \<subseteq> dom f \<Longrightarrow> dom (f o_m g) = dom g"
apply (simp add: dom_def ran_def map_comp_def)
apply (auto split add: option.split_asm)
done
*)

lemma map_add_image_ran: "dom m2 = A \<Longrightarrow>(the \<circ> m1 ++ m2) ` A = ran m2"
by (clarsimp simp add: map_add_def image_def ran_def dom_def) auto

lemma map_add_image: "dom m2 \<inter> A = {} \<Longrightarrow>(m1 ++ m2) ` A = (m1) ` A"
by (fastforce simp add: map_add_def image_def split: option.splits)+

lemma the_map_add_image: "dom m2 \<inter> A = {} \<Longrightarrow>(the \<circ> (m1 ++ m2)) ` A = (the \<circ> m1) ` A"
by (simp add: image_comp[symmetric] map_add_image)

lemma image_Int_subset: "A \<subseteq> B \<Longrightarrow> f ` (A \<inter> B) = f ` A \<inter> f ` B"
by (fastforce simp add: image_def)


lemma dom_reduce_insert: "
  (dom gm = insert a A) = (\<exists> b gm'. gm = gm'(a\<mapsto>b) \<and> dom gm' = A)"
apply (rule iffI)
apply (rule_tac x="the (gm a)" in exI)
apply (rule_tac x="gm|` A" in exI)

apply (simp add: restrict_map_insert [THEN sym] restrict_map_dom_subset)
apply fastforce
apply clarsimp
done


  (* Function map_prod *)


lemma inj_map_prod [simp]: "inj f \<Longrightarrow> inj g \<Longrightarrow> inj (map_prod f g)"
by (simp add: map_prod_def inj_on_def)

lemma rtrancl_map_prod: "(b0, c0) \<in> B\<^sup>* \<Longrightarrow> (f b0, f c0)  \<in> (map_prod f f ` B)\<^sup>*"
apply (induct b0 c0 rule: rtrancl.induct)
apply fast
apply (subgoal_tac "(f b, f c) \<in> (map_prod f f ` B)")
apply (rule rtrancl_into_rtrancl) apply assumption+
apply (fastforce simp add: map_prod_def image_def)
done

lemma rtrancl_inclusion_map_prod: 
  "A^* \<subseteq> B^* \<Longrightarrow>  ((map_prod f f) ` A)^* \<subseteq> ((map_prod f f) ` B)^*"
apply clarify
apply (rename_tac x y)
apply (erule_tac rtrancl.induct [where P = "\<lambda> x y.  (x, y) \<in>  ((map_prod f f) ` B)^*"])
apply fast
apply (subgoal_tac "\<exists> b0 c0. (b0, c0) \<in> A \<and> b = (f b0) \<and> c = (f c0)")
  prefer 2 apply (fastforce simp add: map_prod_def image_def)
apply clarsimp
apply (subgoal_tac "(b0, c0) \<in> B^*") prefer 2 apply blast
apply (fast intro: rtrancl_trans rtrancl_map_prod)
done


  (* Transitive closure *)

lemma rtrancl_id_trancl: "R\<^sup>* = Id \<union> R\<^sup>+"
apply (simp add: set_eq_iff rtrancl_eq_or_trancl)
apply blast
done

(*--------- Set operations implemented on lists ----------------*)

lemma list_max_leq [rule_format]: "x \<in> set vs \<longrightarrow> x \<le> list_max vs"
  by (induct vs) auto

lemma list_max_Suc: "Suc (list_max vs) \<notin> set vs"
  by (fastforce dest: list_max_leq)

lemma  Max_set_max_list :"set a \<noteq> {}  \<longrightarrow>   list_max a =  Max (set  a)  "
  apply (induct a)
  apply simp
  apply (rename_tac a1 a2)
  apply (case_tac a2)
  apply simp+
done

lemma  new_var_eq : "set a = set b \<Longrightarrow> (list_max a) = (list_max b) "
  apply (induct a )
  apply clarsimp
  apply (induct  b)
  apply fastforce
  apply  (subgoal_tac "list_max (a1# a2) = Max( set (a1#a2))")
  apply  (subgoal_tac "list_max (a# b) = Max( set (a#b))")
  apply simp
  apply (metis Max_set_max_list empty_subsetI set_subset_Cons subset_antisym)
  by (metis Max_set_max_list Set.is_empty_def is_empty_set null_rec(1))

lemma nat_is_alloc: "Suc (list_max vs) \<notin> set vs \<and> (set a = set b  \<longrightarrow>   Suc (list_max a) = Suc (list_max b))"
by (clarsimp simp add: list_max_Suc) (intro impI new_var_eq, assumption)


lemma set_list_diff [simp]: "set (list_diff xs ys) = (set xs) - (set ys)"
  by (induct xs) auto

lemma set_list_distrib [simp]: 
  "set (list_distrib xs ys) = (\<lambda>x. x # ys) ` set xs"
by simp

lemma set_list_inters [simp]: "set (list_inters xs ys) = set xs \<inter> set ys"
by (fastforce simp add: List.member_def)

lemma set_list_union [simp]: "set (list_union xs ys) = set xs \<union> set ys"
by simp

lemma  set_list_Union [simp]: "set (list_Union xss) =  \<Union>(set ` (set xss))"  
by (induct xss) (auto simp add: list_Union_def)

lemma set_list_remove [simp]: "set (list_remove xs ys) = set xs - set ys"
by (induct ys) (auto simp add: list_remove_def)

lemma distinct_removeAll [rule_format, simp]: 
  "distinct xs \<longrightarrow> distinct (removeAll x xs)"
by (induct xs) simp_all

lemma distinct_list_remove [rule_format, simp]: 
  "\<forall> xs. distinct xs \<longrightarrow> distinct (list_remove xs ys)"
by (induct ys) (clarsimp simp add: list_remove_def)+

   
lemma distinct_list_Union_map [rule_format, simp]:
 "(\<forall> x \<in> set xs. distinct (f x)) \<longrightarrow> distinct (list_Union (map f xs))"
by (induct xs) (auto simp add: list_Union_def)

(* Congruence for proving termination of functions using list_all2 *)
lemma list_all2_cong [fundef_cong]:
  "xs1 = xs2 \<Longrightarrow> ys1 = ys2 \<Longrightarrow> 
  (\<And>x y. x \<in> set xs1 \<Longrightarrow> y \<in> set ys1 \<Longrightarrow> f x y = g x y) \<Longrightarrow> list_all2 f xs1 ys1 = list_all2 g xs2 ys2"
  by (simp add: list_all2_iff) (metis case_prodE in_set_zipE old.prod.case)

(*<*)
end
(*>*)
