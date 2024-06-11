Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssrnat ssreflect
  ssrfun ssrbool ssrnum eqtype seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From Coq Require Import Unicode.Utf8.

From extructures Require Import ord fset.

#[local] Open Scope fset_scope.

Lemma fset_fsetU_norm2 {T:ordType} (a b: T) : fset [:: a; b] = fset [:: a] :|: fset [:: b].
Proof.
  rewrite -[LHS]fset0U fset0E.
  rewrite [X in  (_ :|: X) = _]fset_cons.
  rewrite fsetUA fset1E.
  by rewrite -fset0E fset0U.
Qed.

Lemma fset_fsetU_norm3 {T:ordType} (a b c : T) : fset [:: a; b; c] = fset [:: a] :|: fset [:: b] :|: fset [:: c].
Proof.
  rewrite [LHS]fset_cons.
  rewrite [X in _ |: X = _]fset_cons.
  rewrite fsetUA.
  by repeat rewrite fset1E.
Qed.

Lemma fset_fsetU {T:ordType} (a b c : T) : fset [:: a; b; c] = fset [:: a; b] :|: fset [:: c].
Proof.
  rewrite [LHS]fset_fsetU_norm3.
  rewrite -fset_cat.
  by rewrite cat1s.
Qed.

Lemma fset_setC {T:ordType} (a b : T) : fset [:: a; b] = fset [:: b; a].
Proof. by rewrite [LHS]fset_cons fsetUC fset1E -fset_cat cat1s. Qed.

(* TODO create a normalization tactic for [fset] where [fsetU] is the normal form.*)
