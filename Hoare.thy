(*<*)
theory Hoare imports Proglang 
begin
(*>*)

section {* Hoare logic where the conditions of the Hoare triples are DL formulae \label{sec:hoare}*}

fun wp_dl :: "('r, 'c, 'i) stmt \<Rightarrow> ('r, 'c, 'i) qform \<Rightarrow> ('r, 'c, 'i) qform" where
  "wp_dl Skip Qd = Qd"
| "wp_dl (NAdd v c) Qd = QSubstFm Qd (CSubst c SAdd (Free v))"
| "wp_dl (NDel v c) Qd = QSubstFm Qd (CSubst c SDiff (Free v))"
| "wp_dl (EAdd v1 r v2) Qd = QSubstFm Qd (RSubst r SAdd (Free v1, Free v2))"
| "wp_dl (EDel v1 r v2) Qd = QSubstFm Qd (RSubst r SDiff (Free v1, Free v2))"
| "wp_dl (SelAss vs b) Qd =  bind_list QAll vs (QImplFm (qform_of_form b) Qd)"
| "wp_dl (c\<^sub>1 ; c\<^sub>2) Qd = wp_dl c\<^sub>1 (wp_dl c\<^sub>2 Qd)"
| "wp_dl (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Qd = QIfThenElseFm (qform_of_form b) (wp_dl c\<^sub>1 Qd) (wp_dl c\<^sub>2 Qd)"
| "wp_dl (WHILE {iv} b DO c) Qd = (qform_of_form iv)"

fun vc :: "('r, 'c, 'i) stmt \<Rightarrow> ('r, 'c, 'i) qform \<Rightarrow> ('r, 'c, 'i) qform" where
  "vc Skip Qd = QTrueFm"
| "vc (NAdd v c) Qd = QTrueFm"
| "vc (NDel v c) Qd = QTrueFm"
| "vc (EAdd v1 r v2) Qd = QTrueFm"
| "vc (EDel v1 r v2) Qd = QTrueFm"
| "vc (SelAss vs b) Qd = QTrueFm"
| "vc (c\<^sub>1 ; c\<^sub>2) Qd = QConjFm (vc c\<^sub>1 (wp_dl c\<^sub>2 Qd)) (vc c\<^sub>2 Qd)"
| "vc (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Qd = QConjFm (vc c\<^sub>1 Qd) (vc c\<^sub>2 Qd)"
| "vc (WHILE {iv} b DO c) Qd = 
      (let qb = (qform_of_form b) in 
      let qiv = (qform_of_form iv) in 
      QConjFm (QConjFm 
           (QImplFm (QConjFm qiv (QNegFm qb)) Qd)
           (QImplFm (QConjFm qiv qb) (wp_dl c qiv)))
           (vc c qiv))"


definition "extract_vcs P c Q =  (QConjFm (vc c Q) (QImplFm P (wp_dl c Q)))"

  (* ----------------------------------------------------------------------  *)
  (* Hoare rules defined as inductive relation *)
  (* ----------------------------------------------------------------------  *)
inductive
  hoare :: "'d itself \<Rightarrow> ('r, 'c, 'i) qform \<Rightarrow> ('r, 'c, 'i) stmt \<Rightarrow> ('r, 'c, 'i) qform \<Rightarrow> bool" 
   ("\<turnstile> _ ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip: "\<turnstile> t {P} Skip {P}" |
NAdd: "\<turnstile> t { QSubstFm Q (CSubst c SAdd (Free v)) } NAdd v c {Q}"  |
NDel: "\<turnstile> t { QSubstFm Q (CSubst c SDiff (Free v)) }  NDel v c {Q}" |
EAdd: "\<turnstile> t { QSubstFm Q (RSubst r SAdd (Free v1, Free v2)) } EAdd v1 r v2 {Q}"  |
EDel: "\<turnstile> t { QSubstFm Q (RSubst r SDiff (Free v1, Free v2)) }  EDel v1 r v2  {Q}" |
SelAss: "\<turnstile> t { bind_list QAll vs (QImplFm (qform_of_form b) Q) } (SelAss vs b) {Q}" |

Seq: "\<lbrakk> \<turnstile> t {P} c\<^sub>1 {Q};  \<turnstile> t {Q} c\<^sub>2 {R} \<rbrakk>
      \<Longrightarrow> \<turnstile> t {P} (c\<^sub>1;c\<^sub>2) {R}"  |
If: "\<lbrakk> \<turnstile> t {QConjFm P (qform_of_form b)} c\<^sub>1 {Q};  \<turnstile> t {QConjFm P (QNegFm (qform_of_form b)) } c\<^sub>2 {Q} \<rbrakk>
     \<Longrightarrow> \<turnstile> t {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |

While: "\<turnstile> t {QConjFm P (qform_of_form b)} c {P} \<Longrightarrow>
        \<turnstile> t {P} WHILE {iv} b DO c {QConjFm P (QNegFm (qform_of_form b))}"  |

conseq: "valid_qform TYPE('d) ((QImplFm P' P))   \<Longrightarrow>
         \<turnstile> TYPE('d) {P} c {Q} \<Longrightarrow> 
         valid_qform TYPE('d) ((QImplFm Q Q')) \<Longrightarrow>
          \<turnstile> TYPE('d) {P'} c {Q'}"


lemmas [simp] = hoare.Skip hoare.NAdd hoare.NDel hoare.EAdd hoare.EDel hoare.SelAss hoare.Seq hoare.If

lemmas [intro!] = hoare.Skip hoare.NAdd hoare.NDel hoare.EAdd hoare.EDel hoare.SelAss hoare.Seq hoare.If


(*<*)
end
(*>*)
