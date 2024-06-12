Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssrnat ssreflect
  ssrfun ssrbool ssrnum eqtype seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From Coq Require Import Unicode.Utf8.

From extructures Require Import ord fset.

#[local] Open Scope fset_scope.

Section fset_help.
  Context {T : ordType}.

  (* TODO This can probably be tactic-driven to work for any size of an
          fset.
   *)
  Lemma fset_fsetU_norm2 (a b: T) :
    fset [:: a; b] = fset [:: a] :|: fset [:: b].
  Proof.
    rewrite -[LHS]fset0U fset0E.
    rewrite [X in  (_ :|: X) = _]fset_cons.
    rewrite fsetUA fset1E.
    by rewrite -fset0E fset0U.
  Qed.

  Lemma fset_fsetU_norm3 (a b c : T) :
    fset [:: a; b; c] = fset [:: a] :|: fset [:: b] :|: fset [:: c].
  Proof.
    rewrite [LHS]fset_cons.
    rewrite fset_fsetU_norm2.
    repeat rewrite fsetUA.
    by repeat rewrite fset1E.
  Qed.

  Lemma fset_fsetU_norm4 (a b c d : T) :
    fset [:: a; b; c; d] = fset [:: a] :|: fset [:: b] :|: fset [:: c] :|: fset [:: d].
  Proof.
    rewrite [LHS]fset_cons.
    rewrite fset_fsetU_norm3.
    repeat rewrite fsetUA.
    by repeat rewrite fset1E.
  Qed.

  Lemma fset_fsetU_norm5 (a b c d e : T) :
    fset [:: a; b; c; d; e] = fset [:: a] :|: fset [:: b] :|: fset [:: c] :|: fset [:: d] :|: fset [:: e].
  Proof.
    rewrite [LHS]fset_cons.
    rewrite fset_fsetU_norm4.
    repeat rewrite fsetUA.
    by repeat rewrite fset1E.
  Qed.

  Lemma fset_fsetU (a b c : T) :
    fset [:: a; b; c] = fset [:: a; b] :|: fset [:: c].
  Proof.
    rewrite [LHS]fset_fsetU_norm3.
    rewrite -fset_cat.
    by rewrite cat1s.
  Qed.

  Lemma fset_setC (a b : T) :
    fset [:: a; b] = fset [:: b; a].
  Proof. by rewrite [LHS]fset_cons fsetUC fset1E -fset_cat cat1s. Qed.


  Lemma fset_swap12 (a b : T) s (a_neq_b: a ≠ b) :
    fset (a :: (b :: s)) = fset (b :: (a :: s)).
  Proof.
    rewrite -eq_fset /(_ =i _) => x0.
    repeat rewrite fset_cons.
    repeat rewrite in_fsetU1.
    do 2! rewrite Bool.orb_assoc.
    by rewrite (@Bool.orb_comm (x0==a) (x0==b)).
  Qed.

End fset_help.

(* TODO create a normalization tactic for [fset] where [fsetU] is the normal form.*)
