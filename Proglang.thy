(*<*)
theory Proglang imports Semantics Variables
begin
(*>*)

section {* Programming language \label{sec:proglang} *}

(*
TODO: the proposal for Forall currently contains a (domtype set option) which contains the
elements of the domain that the variable ranges over. After removal of domtype in interpretations,
one would either have to parameterize stmt by the domain (inacceptable) or, better, take
the domtype set out of the syntax and add a set of pending domain elements to the state space. 
*)
datatype ('r, 'c, 'i) stmt 
  = Skip 
  | NAdd 'i 'c
  | NDel 'i 'c
  | EAdd 'i 'r 'i
  | EDel 'i 'r 'i
  | SelAss "('i list)" "(('r, 'c, 'i) form)"
(*
  | Forall 'i "(('r, 'c, 'i) form)" "('r, 'c, 'i) stmt" "(domtype set option)"
*)
  | Seq    "('r, 'c, 'i) stmt" "('r, 'c, 'i) stmt"         ("_;/ _"  [60, 61] 60)
  | If     "(('r, 'c, 'i) form)" "(('r, 'c, 'i) stmt)" "(('r, 'c, 'i) stmt)"  ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  | While  "(('r, 'c, 'i) form)" "(('r, 'c, 'i) form)" "(('r, 'c, 'i) stmt)"         ("(WHILE {_}/ _/ DO _)"  [0, 0, 61] 61)

  (* In While, the first argument is an invariant (without operational significance) *)

definition form_collect :: "'i \<Rightarrow> (('r, 'c, 'i) form)\<Rightarrow> ('d, 'r, 'c, 'i) Interp \<Rightarrow> 'd set" where
   "form_collect x f i = {xi. interp_form f (interp_i_modif x xi i)}"

(* The following semantics blocks for SelAss if there is no vi that makes the formula b true *)
inductive
  big_step :: "('r, 'c, 'i) stmt \<times> ('d, 'r, 'c, 'i) Interp \<Rightarrow> ('d, 'r, 'c, 'i) Interp \<Rightarrow> bool" ("_\<Rightarrow>_" [61,61]60)
where
Skip:    "(Skip, s) \<Rightarrow> s" |
NAdd:    "s' = add_node v c s \<Longrightarrow> 
          (NAdd v c, s) \<Rightarrow> s'" |
NDel:    "s' = delete_node v c s \<Longrightarrow> 
          (NDel v c, s) \<Rightarrow> s'" |
EAdd:    "s' = add_edge v1 r v2 s \<Longrightarrow> 
          (EAdd v1 r v2, s) \<Rightarrow> s'" |
EDel:    "s' = delete_edge v1 r v2 s \<Longrightarrow> 
          (EDel v1 r v2, s) \<Rightarrow> s'" |
SelAssTrue: "\<exists> vis. set vis \<subseteq> (interp_d s) \<and> length vs = length vis \<and> 
                (s' = interp_i_modif_list (zip vs vis) s \<and> interp_form b s') \<Longrightarrow>
             (SelAss vs b, s) \<Rightarrow> s'" |

(*
ForallEmpty: "(Forall v b c (Some {}), s) \<Rightarrow> s" |

-- "forall reestablishes the value of v before execution of the loop"
-- "That only makes sense if no assignment to v is possible within the loop"
-- "(to be enforced by the type system)"
ForallNonEmpty: "a \<in> A \<Longrightarrow>  
          (c, interp_i_modif v a s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow> 
          (Forall v b c (Some (A - {a})), s\<^sub>2) \<Rightarrow> s\<^sub>3 \<Longrightarrow> 
          s\<^sub>4 = interp_i_modif v (interp_i s\<^sub>1 v) s\<^sub>3 \<Longrightarrow>
         (Forall v b c (Some A), s\<^sub>1) \<Rightarrow> s\<^sub>4 " |

ForallStart: "(Forall v b c (Some (form_collect v b s)), s)  \<Rightarrow> s' \<Longrightarrow>
         (Forall v b c None, s) \<Rightarrow> s'" |
*)

Seq:     "(c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow>
          (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3  \<Longrightarrow>
          (c\<^sub>1;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |

IfTrue:  "interp_form b s \<Longrightarrow>
          (c\<^sub>1,s) \<Rightarrow> t  \<Longrightarrow>
         (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<not> interp_form b s \<Longrightarrow>
         (c\<^sub>2,s) \<Rightarrow> t \<Longrightarrow>
         (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |

WhileFalse: "\<not>interp_form b s \<Longrightarrow> (WHILE {iv} b DO c,s) \<Rightarrow> s" |
WhileTrue:  "interp_form b s\<^sub>1 \<Longrightarrow>  
             (c,s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow> 
             (WHILE {iv} b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3  \<Longrightarrow>
             (WHILE {iv} b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" 

       
declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]


inductive_cases SkipE[elim!]: "(Skip,s) \<Rightarrow> t"
inductive_cases NAddE[elim!]: "(NAdd v c, s) \<Rightarrow> s'"
inductive_cases NDelE[elim!]: "(NDel v c, s) \<Rightarrow> s'"
inductive_cases EAddE[elim!]: "(EAdd v1 r v2, s) \<Rightarrow> s'"
inductive_cases EDelE[elim!]: "(EDel v1 r v2, s) \<Rightarrow> s'"
inductive_cases ESelAss[elim!]: "(SelAss v b, s) \<Rightarrow> s'"
inductive_cases SeqE[elim!]: "(c1;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE {iv} b DO c,s) \<Rightarrow> t"


  (* ---------------------------------------------------------------------- *)
  (* Some auxiliary functions *)

fun apply_var_stmt :: "('a \<Rightarrow> 'b) \<Rightarrow> ('r, 'c, 'a) stmt \<Rightarrow> ('r, 'c, 'b) stmt" where
  "apply_var_stmt f Skip = Skip"
| "apply_var_stmt f (NAdd v c) = (NAdd (f v) c)"
| "apply_var_stmt f (NDel v c) = (NDel (f v) c)"
| "apply_var_stmt f (EAdd v1 r v2) = EAdd (f v1) r (f v2)"
| "apply_var_stmt f (EDel v1 r v2) = EDel (f v1) r (f v2)"
| "apply_var_stmt f (SelAss vs b) =  (SelAss (map f vs) (apply_var_form f b))"
| "apply_var_stmt f (c\<^sub>1 ; c\<^sub>2) = (apply_var_stmt f c\<^sub>1 ; (apply_var_stmt f c\<^sub>2))"
| "apply_var_stmt f (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (IF (apply_var_form f b) THEN (apply_var_stmt f c\<^sub>1) ELSE (apply_var_stmt f c\<^sub>2))"
| "apply_var_stmt f (WHILE {iv} b DO c) = (WHILE {apply_var_form f iv} (apply_var_form f b) DO (apply_var_stmt f c))"


(*
fun form_prop_in_stmt :: "(('nr, 'nc, 'ni var) form \<Rightarrow> bool) \<Rightarrow> ('nr, 'nc, 'ni) stmt \<Rightarrow> bool" where 
    "form_prop_in_stmt fp Skip = True"
  | "form_prop_in_stmt fp (NAdd v c) = True"
  | "form_prop_in_stmt fp (NDel v c) = True"
  | "form_prop_in_stmt fp (EAdd v1 r v2) = True"
  | "form_prop_in_stmt fp (EDel v1 r v2) = True"
  | "form_prop_in_stmt fp (SelAss v b) = fp b"
  | "form_prop_in_stmt fp (c\<^sub>1 ; c\<^sub>2) = (form_prop_in_stmt fp c\<^sub>1 \<and> form_prop_in_stmt fp c\<^sub>2)"
  | "form_prop_in_stmt fp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = 
     (fp b \<and> form_prop_in_stmt fp c\<^sub>1 \<and> form_prop_in_stmt fp c\<^sub>2)"
  | "form_prop_in_stmt fp (WHILE {iv} b DO c) = (fp iv \<and> fp b \<and> form_prop_in_stmt fp c)"
*)

(*<*)
end
(*>*)
