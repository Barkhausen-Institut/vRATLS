Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssreflect
  ssrfun ssrbool eqtype.
Set Warnings "notation-overridden,ambiguous-paths".

From extructures Require Import ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Facts.

  Variable A:ordType.
  Variable a b :A.

  Lemma neq_ltgt:
    (a == b) = false -> (a < b)%ord || (b < a)%ord.
  Proof. by [case: (Ord.ltgtP a b)]. Qed.

  Lemma ord_lt_false :
    (b < a)%ord = true -> (a < b)%ord = false.
  Proof.
  (* TODO there must be a simpler version of thios proof!

             see below:
             move => h.
             rewrite /Ord.lt.
             apply/negP/negP/nandP.
             left.
             rewrite Ord.ltNge in h; exact: h.
   *)
    move => h2.
    move/idP: h2 => h2.
    rewrite Ord.lt_neqAle in h2.
    move/andP: h2; case => a_neq_a' a_lt_a'.
    case: Ord.ltgtP => //=.
    move => h.
    rewrite Ord.leq_eqVlt in a_lt_a'.
    move/orP: a_lt_a'. case.
    - move/eqP => a_eq_a' => //=. rewrite a_eq_a' in a_neq_a'. move/eqP: a_neq_a' => //=.
    - move => a'_lt_a //=.
      have bla := a'_lt_a.
      move/eqP/eqP: bla => bla; rewrite -bla.

      apply Ord.ltW in h.
      apply Ord.ltW in a'_lt_a.
      have c:= conj h a'_lt_a.
      move/andP: c => c.
      have d := (Ord.anti_leq c).
      rewrite d.
      by [apply Ord.ltxx].
  Qed.

  Lemma lt_antisym:
    (a < b)%ord = true -> (b < a)%ord = false.
  Proof.
    move/idP => a_lt_b.
    rewrite /Ord.lt; apply/nandP; left.
    rewrite -Ord.ltNge; exact: a_lt_b.
  Qed.

End Facts.
