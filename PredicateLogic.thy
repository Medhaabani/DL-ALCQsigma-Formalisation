
theory PredicateLogic imports Syntax Variables
begin

(*
Restrictive hypotheses to get rid of later:
 - The formulas cannot contain free variables (however, the subformulas may obviously contain some).
 - There is no equality symbol.
*)


lemma "(∃ x ∈ {a, b}. P x) = (∃ x. (x = a \<or> x = b) \<and> P x)"
by blast


(************************************* Syntax and semantics **************************************)

(* 'nR type can be an concept name, a role name or a constant name ; also a relation of greater
arity, but it won't be useful here. *)
datatype ('nR, 'ni) plform = 
    PlConstFm bool
  | PlRel bool  "('nR)" "('ni var) list"
  | PlEq bool "'ni var" "'ni var"
  | PlNegFm "(('nR, 'ni) plform)"
  | PlBinopFm binop "(('nR, 'ni) plform)" "(('nR, 'ni) plform)"
(*| PlQuantifFm quantif "(numres_ord)" "(nat)" "('ni)" "(('nR, 'ni) plform)" *)
  | PlQuantifFm quantif "('ni)" "(('nR, 'ni) plform)"

abbreviation PlConc where "PlConc c v ≡ (PlRel True c [v])"
abbreviation PlBRel where "PlBRel b r v w ≡ (PlRel b r [v,w])"
abbreviation PlImplFm where "PlImplFm f g ≡ (PlBinopFm Disj (PlNegFm f) g)"
abbreviation PlEquivFm where "PlEquivFm f g ≡ (PlBinopFm Conj (PlImplFm f g) (PlImplFm g f))"


record ('d, 'nR, 'ni) PlInterp =
  plinterp_d :: "'d set" 
  plinterp_r :: "'nR ⇒ 'd list ⇒ bool"
  plinterp_i :: "'ni ⇒ 'd"

definition plinterp_bound :: "'d ⇒ ('d, 'nR, 'ni var) PlInterp ⇒ ('d, 'nR, 'ni var) PlInterp" where
  "plinterp_bound xi i = i\<lparr>plinterp_i :=  ((plinterp_i i) ∘ (drop_var 0))(Bound 0 := xi) \<rparr>"
  
fun interp_plform :: "('nR, 'ni) plform ⇒ ('d, 'nR, 'ni var) PlInterp ⇒ bool" where
    "interp_plform (PlConstFm b) i = b"
  | "interp_plform (PlRel b r v) i = (if b
                                        then ( (plinterp_r i r) (map (plinterp_i i) v) )
                                        else ¬ ( (plinterp_r i r) (map (plinterp_i i) v) )
                                       )"
  | "interp_plform (PlEq b x y) i = ((plinterp_i i x) = (plinterp_i i y))"
  | "interp_plform (PlNegFm φ) i = (¬ interp_plform φ i)"
  | "interp_plform (PlBinopFm binop φ ψ) i = (case binop of
                                              Conj ⇒ ((interp_plform φ i) ∧ (interp_plform ψ i)) |
                                              Disj ⇒ ((interp_plform φ i) ∨ (interp_plform ψ i))
                                              )"
  | "interp_plform (PlQuantifFm QAll x φ) i = (∀ ξ ∈ plinterp_d i. interp_plform φ (plinterp_bound ξ i))"
  | "interp_plform (PlQuantifFm QEx  x φ) i = (∃ ξ ∈ plinterp_d i. interp_plform φ (plinterp_bound ξ i))"




(*************************************** Scott's Reduction ***************************************)

datatype 'nR scott_rel = Orig 'nR | Created "bool list"

(* Changes the type of relations from 'nR to 'nR scott_rel. *)
fun pl_to_scott_pl :: "('nR, 'ni) plform ⇒ ('nR scott_rel, 'ni) plform" where
    "pl_to_scott_pl (PlConstFm b) = (PlConstFm b)"
  | "pl_to_scott_pl (PlRel b r l) = (PlRel b (Orig r) l)"
  | "pl_to_scott_pl (PlEq b x y) = (PlEq b x y)"
  | "pl_to_scott_pl (PlNegFm φ) = (PlNegFm (pl_to_scott_pl φ))"
  | "pl_to_scott_pl (PlBinopFm binop φ ψ) = (PlBinopFm binop (pl_to_scott_pl φ) (pl_to_scott_pl ψ))"
  | "pl_to_scott_pl (PlQuantifFm Q x φ) = (PlQuantifFm Q x (pl_to_scott_pl φ))"


(* Simplifies terms containing ∃∨∃ or ∀∧∀, and replaces ∃s with ∀s. *)
fun scott_preprocessing :: "('nR scott_rel, 'ni) plform ⇒ ('nR scott_rel, 'ni) plform" where
  (* Simplification *)
    "scott_preprocessing (PlBinopFm Disj (PlQuantifFm QEx x φ) (PlQuantifFm QEx y ψ)) =
                          (PlNegFm (PlQuantifFm QAll x (PlNegFm (PlBinopFm Disj (scott_preprocessing φ) (scott_preprocessing ψ)))))"
  | "scott_preprocessing (PlBinopFm Conj (PlQuantifFm QAll x φ) (PlQuantifFm QAll y ψ)) =
                          (PlQuantifFm QAll x (PlBinopFm Conj (scott_preprocessing φ) (scott_preprocessing ψ)))"
  (* Other cases *)
  | "scott_preprocessing (PlNegFm φ) = (PlNegFm (scott_preprocessing φ))"
  | "scott_preprocessing (PlBinopFm binop φ ψ) = (PlBinopFm binop (scott_preprocessing φ) (scott_preprocessing ψ))"
  | "scott_preprocessing (PlQuantifFm QAll x φ) = (PlQuantifFm QAll x (scott_preprocessing φ))"
  | "scott_preprocessing (PlQuantifFm QEx x φ) = (PlNegFm (PlQuantifFm QAll x (PlNegFm (scott_preprocessing φ))))"
  | "scott_preprocessing φ = φ"


(* Gives the free variables of an atomic formula. *)
fun fv_atomic :: "('nR, 'ni) plform \<Rightarrow> nat list" where
    " fv_atomic (PlConstFm b) = [] "
  | " fv_atomic (PlRel b r []) = [] "
  | " fv_atomic (PlRel b r ((Bound m)#l)) = (m # (fv_atomic (PlRel b r l))) "
  | " fv_atomic (PlEq b (Bound m) (Bound n)) = [m,n] "
  | " fv_atomic (PlEq b _         (Bound n)) = [n] "
  | " fv_atomic (PlEq b (Bound m) _        ) = [m] "
  | " fv_atomic (PlEq b _         _        ) = [] "


(* Merge two SORTED nat lists. *)
fun fv_merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
    " fv_merge l [] = l "
  | " fv_merge [] l = l "
  | " fv_merge (h1#t1) (h2#t2) = (if (h1 \<le> h2) 
                                  then (h1 # (fv_merge t1 (h2#t2)))
                                  else (h2 # (fv_merge (h1#t1) t2))) "


(* Shift all De Bruijn indices of a set of free variables. *)
fun scott_reduction_bind :: "nat list \<Rightarrow> nat list" where
    " scott_reduction_bind [] = [] "
  | " scott_reduction_bind (0#l) = (scott_reduction_bind l) "
  | " scott_reduction_bind (n#l) = ((n-1)#(scott_reduction_bind l)) "


(* Put universal quantifiers before a given formula, with its free variables' names. *)
fun forallize :: "('nR scott_rel, 'ni) plform  ⇒ 'ni list ⇒ nat list ⇒ nat
                       ⇒ ('nR scott_rel, 'ni) plform" where
    "forallize f _       []      _ = f"
  | "forallize f (hb#tb) (hf#tf) n = (if (n > hf)
                                      then (forallize f tb (hf#tf) (n-1))
                                      else (forallize (PlQuantifFm QAll hb f) tb tf (n-1))
                                     )"


(* Compute the formula ∀v.Qψ(v)↔theta'ψ(v). *)
fun scott_reduction_theta_PlConstFm :: " bool
       ⇒ bool list
       ⇒ ('nR scott_rel, 'ni) plform" where
    "scott_reduction_theta_PlConstFm b p = (PlEquivFm (PlRel True (Created p) []) (PlConstFm b))"
fun scott_reduction_theta_PlRel :: " bool ⇒ ('nR scott_rel) ⇒ ('ni var) list
       ⇒ bool list
       ⇒ 'ni list
       ⇒ nat list
       ⇒ ('nR scott_rel, 'ni) plform" where
    "scott_reduction_theta_PlRel b r v p bv fv = (forallize (PlImplFm 
           (PlRel True (Created p) (map Bound fv))
           (PlRel b r (map Bound fv))
      ) (rev bv) (rev fv) (hd (rev fv)))"
fun scott_reduction_theta_PlEq :: "bool ⇒ 'ni var ⇒ 'ni var ⇒ bool list ⇒ 'ni list ⇒ nat list
     ⇒ ('nR scott_rel, 'ni) plform" where
    "scott_reduction_theta_PlEq b x y p bv fv = (forallize (PlImplFm
           (PlRel True (Created p) [Bound 0, Bound 1])
           (PlEq b (Bound 0) (Bound 1))
      ) (rev bv) (rev fv) 2 )"
fun scott_reduction_theta_PlNegFm :: " bool list
       ⇒ 'ni list
       ⇒ nat list
       ⇒ ('nR scott_rel, 'ni) plform" where
    "scott_reduction_theta_PlNegFm p bv fv = (forallize (PlImplFm
           (PlRel True (Created p) (map Bound fv))
           (PlNegFm (PlRel True (Created (True#p)) (map Bound fv)))
      ) (rev bv) (rev fv) (hd (rev fv)))"
fun scott_reduction_theta_PlBinopFm :: " binop
       ⇒ bool list
       ⇒ 'ni list
       ⇒ nat list ⇒ nat list
       ⇒ ('nR scott_rel, 'ni) plform" where
    "scott_reduction_theta_PlBinopFm bop p bv fv fv' = (forallize (PlImplFm
           (PlRel True (Created p) (map Bound (fv_merge fv fv')))
           (PlBinopFm bop (PlRel True (Created  (True#p)) (map Bound fv ))
                          (PlRel True (Created (False#p)) (map Bound fv')))
      ) (rev bv) (rev (fv_merge fv fv')) (hd (rev (fv_merge fv fv'))) )"
fun scott_reduction_theta_PlQuantifFm :: "'ni
       ⇒ bool list
       ⇒ 'ni list
       ⇒ nat list
       ⇒ ('nR scott_rel, 'ni) plform" where
   "scott_reduction_theta_PlQuantifFm x p bv fv = (forallize (PlImplFm 
           (PlRel True (Created p) (map Bound fv))
           (PlQuantifFm QAll x (PlRel True (Created (True#p)) (map Bound (0#fv))))
      ) (rev bv) (rev fv) (hd (rev fv)) )"


definition " scott_reduction_build_PlNegFm bv p ind ≡ let (Θ, fv) = ind in
             (insert (scott_reduction_theta_PlNegFm p bv fv) Θ, fv) "
definition " scott_reduction_build_PlBinopFm bop bv p ind ≡ let ((Θ, fv), (Θ', fv')) = ind in
             (insert (scott_reduction_theta_PlBinopFm bop p bv fv fv') Θ ∪ Θ', fv_merge fv fv') "
definition " scott_reduction_build_PlQuantifFm x bv p ind ≡ let (Θ, fv) = ind in
             (insert (scott_reduction_theta_PlQuantifFm x p bv (scott_reduction_bind fv)) Θ, scott_reduction_bind fv) "


(* Give the set Θ of the formulas \<theta> computed for the formula ψ and its subformulas. 
   NEEDS ψ TO CONTAIN NO ∃ AND NO Bound() CONSTRUCTOR. *)
fun scott_reduction_build :: "('nR scott_rel, 'ni) plform                                   (* ψ *)
                              ⇒ bool list               (* identifier of ψ, i.e. path to ψ in ϕ *)
                              ⇒ 'ni list                  (* names associated to bound variables *)
                              ⇒ (('nR scott_rel, 'ni) plform set                           (* Θ *)
                                 \<times>  nat list)"                            (* free variables *)
where "scott_reduction_build (PlConstFm b) p bv = ({scott_reduction_theta_PlConstFm b p}, [])"
   |  "scott_reduction_build (PlRel b r v) p bv = 
       ({scott_reduction_theta_PlRel b r v p bv (sort (fv_atomic (PlRel b r v)))}, sort (fv_atomic (PlRel b r v)))"
(* |  "scott_reduction_build (PlEq b x y) p bv = 
      ({scott_reduction_theta_PlEq b x y p bv (sort (fv_atomic (PlEq b x y)))}, sort (fv_atomic (PlEq b x y)))" *)
   |  "scott_reduction_build (PlNegFm f) p bv = 
       (scott_reduction_build_PlNegFm bv p (scott_reduction_build f (True#p) bv))"
   |  "scott_reduction_build (PlBinopFm bop f g) p bv = 
       (scott_reduction_build_PlBinopFm bop bv p ((scott_reduction_build f (True#p) bv), 
                                                  (scott_reduction_build g (False#p) bv)) )"
   |  "scott_reduction_build (PlQuantifFm Q x f) p bv = 
       (scott_reduction_build_PlQuantifFm x bv p (scott_reduction_build f (True#p) bv))"


(* Main function : take φ and build Θ. *)
definition scott_reduction :: "('nR, 'ni) plform ⇒ ('nR scott_rel, 'ni) plform set" where
  "scott_reduction φ = (fst (scott_reduction_build (scott_preprocessing (pl_to_scott_pl φ)) [] []))"



value "scott_reduction (PlQuantifFm QAll x (PlRel True r [Bound 0]))"

lemma "∀p bv. ∀f ∈ fst (scott_reduction_build f_orig p bv) . interp_plform f i \<Longrightarrow> interp_plform f_orig i"
  apply (induct f_orig)
  prefer 4
  apply clarsimp
  sorry


end
