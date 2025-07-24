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
    move => h.
    rewrite /Ord.lt.
    apply/negP/negP/nandP.
    left.
    rewrite Ord.ltNge in h; exact: h.
  Qed.

  Lemma lt_antisym:
    (a < b)%ord = true -> (b < a)%ord = false.
  Proof.
    move/idP => a_lt_b.
    rewrite /Ord.lt; apply/nandP; left.
    rewrite -Ord.ltNge; exact: a_lt_b.
  Qed.

End Facts.
