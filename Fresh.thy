(* Copied verbatim from the Isabelle mailing list (2/3/2015) *)

section {* Operators on strings dealing with fresh variable generation *}

theory Fresh imports String (* "~~/src/HOL/Library/Char_ord" *)
"~~/src/HOL/Library/Code_Char"
begin

subsection{* A strict ordering on strings, "odrdst",
and its nonstrict version, "ordstNS"   *}

definition  ordst :: "string \<Rightarrow> string \<Rightarrow> bool" where
(* the first criterion is the length, and the second
   the last character, alphabetically *)
"ordst X Y \<equiv>
 (length X \<le> length Y \<and> X \<noteq> [] \<and> Y \<noteq> [] \<and> nat_of_char (last X) < nat_of_char(last Y))
 \<or> (length X < length Y)"

definition ordstNS :: "string \<Rightarrow> string \<Rightarrow> bool" where
"ordstNS X Y == X = Y \<or> ordst X Y"

lemma ordst_antirefl: "~ ordst X X"
by(auto simp add: ordst_def)

lemma ordst_trans:
assumes As1: "ordst X Y" and As2: "ordst Y Z"
shows "ordst X Z"
proof(cases "(length X < length Y) \<or> (length Y < length Z)")
  assume "(length X < length Y) \<or> (length Y < length Z)"
  moreover
  {assume "length X < length Y"
   moreover have "length Y <= length Z"
   using As2 ordst_def by force
   ultimately have "length X < length Z" by force
   hence ?thesis using ordst_def by force}
  moreover
  {assume "length Y < length Z"
   moreover have "length X <= length Y"
   using As1 ordst_def by force
   ultimately have "length X < length Z" by force
   hence ?thesis using ordst_def by force}
  ultimately show ?thesis by force
next
  assume "\<not> (length X < length Y \<or> length Y < length Z)"
  hence Ft: "~ length X < length Y  \<and> ~ length Y < length Z" by force
  hence "nat_of_char(last X) < nat_of_char(last Y) \<and>
         nat_of_char(last Y) < nat_of_char(last Z) \<and>
         length X <= length Y \<and> length Y <= length Z"
  using As1 As2 ordst_def by force
  hence "nat_of_char(last X) < nat_of_char(last Z) \<and>
         length X <= length Z" by force
  moreover have "X ~= [] \<and> Z ~= []"
  using As1 As2 Ft ordst_def by force
  ultimately show ?thesis using ordst_def[of X Z] by force
qed

lemma ordstNS_refl: "ordstNS X X"
by(simp add: ordstNS_def)

lemma ordstNS_trans:
assumes As1: "ordstNS X Y" and As2: "ordstNS Y Z"
shows "ordstNS X Z"
proof-
  {assume As: "X = Y"
    moreover
    {assume "Y = Z"
     with As ordstNS_def have ?thesis by force}
    moreover
    {assume "ordst Y Z"
     with As As2 ordstNS_def have ?thesis by force}
    ultimately have ?thesis using ordstNS_def[of Y Z] As2
    by force
  }
  moreover
  {assume As: "ordst X Y"
   moreover
    {assume "Y = Z"
     with As As1 ordstNS_def have ?thesis by force}
   moreover
    {assume "ordst Y Z"
     with As ordst_trans[of X Y Z] ordstNS_def have ?thesis by force}
   ultimately have ?thesis using ordstNS_def[of Y Z] As2
   by force
  }
  ultimately
  show ?thesis using ordstNS_def As1 by force
qed

lemma ordst_ordstNS_trans:
assumes As1: "ordst X Y" and
        As2: "ordstNS Y Z"
shows "ordst X Z"
proof-
  {assume "Y = Z"
   with As1 As2 ordstNS_def have ?thesis by force
  }
  moreover
  {assume "ordst Y Z"
   with As1 ordst_trans[of X Y Z] ordstNS_def have ?thesis by force
  }
  ultimately show ?thesis using ordstNS_def[of Y Z] As2
  by force
qed

lemma ordstNS_ordst_trans:
assumes As1: "ordstNS X Y" and
        As2: "ordst Y Z"
shows "ordst X Z"
proof-
  {assume "X = Y"
   with As2 ordstNS_def
   have ?thesis by force
  }
  moreover
  {assume As: "ordst X Y"
   with As2 ordst_trans[of X Y Z] ordstNS_def
   have ?thesis by force
  }
  ultimately
  show ?thesis using ordstNS_def As1 by force
qed


subsection{* The fresh-variable arsenal *}

fun upChar :: "string \<Rightarrow> string" where
(* If the last character is >= 'a' and < 'z',
   then upChar increments this last character;
   otherwise upChar appens an 'a'.  *)
"upChar Y =
 (if (Y ~= [] \<and> nat_of_char(last Y) >= 97 \<and>
                nat_of_char(last Y) < 122)
    then (butlast Y) @
         [char_of_nat(nat_of_char(last Y) + 1)]
    else Y @ ''a''
 )"

lemma upChar_ordst: "ordst Y (upChar Y)"
proof-
  {assume "~(Y ~= [] \<and> nat_of_char(last Y) >= 97
                       \<and> nat_of_char(last Y) < 122)"
   hence "upChar Y = Y @ ''a''" by force
   hence ?thesis using ordst_def by force
  }
  moreover
  {assume As: "Y ~= [] \<and> nat_of_char(last Y) >= 97
                       \<and> nat_of_char(last Y) < 122"
   hence Ft: "upChar Y = (butlast Y) @
                     [char_of_nat(nat_of_char(last Y) + 1)]"
   by force
   hence Ft': "last (upChar Y) = char_of_nat(nat_of_char(last Y) + 1)"
   by force
   hence "nat_of_char(last (upChar Y)) mod 256  =
          (nat_of_char(last Y) + 1) mod 256"
   using nat_of_char_of_nat by force
   moreover
   have "nat_of_char(last(upChar Y))  < 256 \<and>
         nat_of_char(last Y) + 1 < 256 "
   using As nat_of_char_of_nat Ft' by force
   ultimately
   have "nat_of_char (last Y) < nat_of_char (last(upChar Y))" by force
   moreover
   from Ft have "length Y <= length (upChar Y)" by force
   ultimately have ?thesis using ordst_def by force}
  ultimately show ?thesis by force
qed

function fresh :: "string list \<Rightarrow> string \<Rightarrow> string"
(* fresh Xs Y changes Y as little as possible so that
   it becomes disjoint from all strings in Xs. *)
where
"Y : set Xs \<Longrightarrow> fresh Xs Y = fresh (remove1 Y Xs) (upChar Y)"
|
"Y ~: set Xs \<Longrightarrow> fresh Xs Y = Y"
by(atomize_elim, auto)
termination
proof(relation "measure (%(Xs,Y). length Xs)", auto simp add: length_remove1)
  fix Y Xs assume "Y : set Xs"
  hence "Xs ~= []" by force
  thus "length Xs - Suc 0 < length Xs" by force
qed

lemma fresh_ordstNS: "ordstNS Y (fresh Xs Y)"
proof-
  have "!!n. ALL Xs Y. length Xs = n \<longrightarrow> ordstNS Y (fresh Xs Y)"
  proof-
    fix n
    show "ALL Xs Y. length Xs = n \<longrightarrow> ordstNS Y (fresh Xs Y)"
    proof(induct n, simp add: ordstNS_def, clarify)
      fix n and Xs::"string list" and Y
      assume IH: "\<forall>Xs Y. length Xs = n \<longrightarrow> ordstNS Y (fresh Xs Y)" and
             L: "length Xs = Suc n"
      show "ordstNS Y (fresh Xs Y)"
      proof(cases "Y : set Xs")
        (* assumptions can be stated in any order *)
        assume "Y ~: set Xs"
        thus ?thesis using ordstNS_refl by force
      next
        assume As: "Y : set Xs"
        with L length_remove1[of Y Xs]
        have "length (remove1 Y Xs) = n" by force
        with IH
        have "ordstNS (upChar Y) (fresh (remove1 Y Xs) (upChar Y))"
        by force
        with upChar_ordst[of Y]
             ordst_ordstNS_trans[of Y "upChar Y"
                                      "fresh (remove1 Y Xs) (upChar Y)"]
        have "ordst Y (fresh (remove1 Y Xs) (upChar Y))"
        by force
        hence "ordstNS Y (fresh (remove1 Y Xs) (upChar Y))"
        using ordstNS_def by force
        with As show ?thesis by force
      qed
    qed
  qed
  thus ?thesis by force
qed

lemma fresh_set: "fresh Xs Y \<notin> set Xs"
proof-
  have "!!n. ALL Xs Y. length Xs = n \<longrightarrow> ~ fresh Xs Y : set Xs"
  proof-
    fix n
    show "ALL Xs Y. length Xs = n \<longrightarrow> ~ fresh Xs Y : set Xs"
    proof(induct n, simp, clarify)
      fix n and Xs::"string list" and Y
      assume IH: "\<forall>Xs Y. length Xs = n \<longrightarrow> ~ fresh Xs Y : set Xs" and
             L: "length Xs = Suc n" and
             L': "fresh Xs Y \<in> set Xs"
      show False
      proof(cases "Y : set Xs")
        assume As: "Y : set Xs"
        with L length_remove1[of Y Xs]
        have "length (remove1 Y Xs) = n" by force
        with IH
        have "~ (fresh (remove1 Y Xs) (upChar Y)) : set (remove1 Y Xs)"
        by blast
        moreover with As L'
        have "(fresh (remove1 Y Xs) (upChar Y)) : set Xs" by force
        ultimately
        have "fresh (remove1 Y Xs) (upChar Y) = Y"
        using in_set_remove1 by metis
        moreover
        from upChar_ordst[of Y]
             fresh_ordstNS[of "upChar Y" "remove1 Y Xs"]
             ordst_ordstNS_trans[of "Y" "upChar Y"
                                    "fresh (remove1 Y Xs) (upChar Y)"]
        have "ordst Y (fresh (remove1 Y Xs) (upChar Y))" by force
        ultimately show False using ordst_antirefl by force
      qed(insert L', auto)
    qed
  qed
  thus ?thesis by force
qed

(*
(* How to execute fresh: *)
lemma "[fresh [] ''Abc'',
        fresh [''X'', ''Abc''] ''Abd'',
        fresh [''X'', ''Y''] ''Y'',
        fresh [''X'', ''Yaa'', ''Ya'', ''Yaa''] ''Ya'',
        fresh [''X'', ''Yaa'', ''Yz'', ''Yza''] ''Yz'',
        fresh [''X'', ''Y'', ''Yab'', ''Y''] ''Y'']
       = dummy"
       apply (simp add: char_of_nat_def nat_of_char_def)
apply (simp add: char_of_nat_def nibble_pair_of_nat_def)
apply (simp add: nat_of_char.simps char_of_nat_def nibble_pair_of_nat_def)
oops
*)

(* done: peter, code generation setup for fresh *)
lemma [code]:
  "fresh Xs Y = (
     if Y \<in> set Xs then fresh (remove1 Y Xs) (upChar Y)
     else Y)"
  by simp

end