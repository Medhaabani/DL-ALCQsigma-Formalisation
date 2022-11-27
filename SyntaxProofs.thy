(*<*)
theory SyntaxProofs imports Syntax
begin
(*>*)

section {* Syntax of the $\cal ALCQ$ logic (Proofs) *}

lemma dual_numres_ord_dual_numres_ord [simp]: 
  "dual_numres_ord b1 (dual_numres_ord b2 nro) = (dual_numres_ord (b1 \<longleftrightarrow> b2) nro)"
by (case_tac nro) simp_all

lemma dual_binop_dual_binop [simp]: 
  "dual_binop b1 (dual_binop b2 bop) = (dual_binop (b1 \<longleftrightarrow> b2) bop)"
by (case_tac bop) simp_all

lemma dual_quantif_dual_quantif [simp]: 
  "dual_quantif b1 (dual_quantif b2 q) = (dual_quantif (b1 \<longleftrightarrow> b2) q)"
by (case_tac q) simp_all

lemma dual_quantif_QAll [simp]:
  "(dual_quantif b q = QAll) = (if b then (q = QAll) else (q = QEx))"
by (case_tac q) simp_all

lemma dual_binop_inj [simp]: "(dual_binop b1 bop = dual_binop b2 bop) = (b1 = b2)"
by (case_tac bop) simp_all

lemma dual_numres_ord_inj [simp]: 
   "(dual_numres_ord b1 nro = dual_numres_ord b2 nro) = (b1 = b2)"
by (case_tac nro) simp_all

lemma dual_binop_True [simp]: "dual_binop True bop = bop"
by (case_tac bop) simp_all

lemma dual_numres_ord_True [simp]: "dual_numres_ord True nro = nro"
by (case_tac nro) simp_all


lemma dual_binop_eq1 [simp]: "(dual_binop b bop = bop) = b"
by (case_tac bop) auto
lemma dual_binop_eq2 [simp]: "(bop = dual_binop b bop) = b"
by (case_tac bop) auto

lemma dual_numres_ord_eq1 [simp]: "(dual_numres_ord b nro = nro) = b"
by (case_tac nro) auto
lemma dual_numres_ord_eq2 [simp]: "(nro = dual_numres_ord b nro) = b"
by (case_tac nro) auto


lemma dual_quantif_eq1 [simp]: "(dual_quantif b q = q) = b"
by (case_tac q) auto
lemma dual_quantif_eq2[simp]: "(q = dual_quantif b q) = b"
by (case_tac q) auto

(* ---------------------------------------------------- *)
(* Functions sub_concepts and sub_concepts_pn *)
(* ---------------------------------------------------- *)

(* sub_concepts *)

lemma sub_concepts_self [simp, intro]: "c \<in> sub_concepts c"
by (case_tac c) auto

lemma sub_concepts_not_empty [simp]: "sub_concepts c \<noteq> {}"
by (insert sub_concepts_self [of c]) fast

lemma sub_concepts_idem [simp]: "(\<Union>s\<in>sub_concepts c. sub_concepts s) = sub_concepts c"
by (induct c) auto

lemma sub_concepts_closed: 
  "s\<in>sub_concepts c \<Longrightarrow>  sub_concepts s \<subseteq> sub_concepts c"
by (insert sub_concepts_idem [of c]) fast

lemma finite_sub_concepts [simp]: "finite (sub_concepts c)"
by (induct c) auto

(* sub_concepts_pn *)

lemma sub_concepts_pn_self [simp, intro]: "c \<in> sub_concepts_pn c"
by (induct c) (auto simp add: Let_def)

lemma sub_concepts_pn_not_empty [simp]: "sub_concepts_pn c \<noteq> {}"
by (insert sub_concepts_pn_self [of c]) fast

lemma sub_concepts_pn_idem [simp]: "(\<Union>s\<in>sub_concepts_pn c. sub_concepts_pn s) = sub_concepts_pn c"
  apply (induct c)  apply(simp_all add: Let_def) by(blast)+
  
lemma sub_concepts_pn_closed: 
  "sc\<in>sub_concepts_pn c \<Longrightarrow> sub_concepts_pn sc \<subseteq> sub_concepts_pn c"
by (insert sub_concepts_pn_idem [of c]) fast

lemma finite_sub_concepts_pn [simp]: "finite (sub_concepts_pn c)"
by (induct c) (auto simp add: Let_def)

(*<*)
end
(*>*)
