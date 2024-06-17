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

  Lemma fset_fsetU (a b : T) (s : seq T) :
    fset ([:: a; b] ++ s) = fset [:: a; b] :|: fset s.
  Proof.
    apply fset_cat.
  Qed.

  Lemma fset_cons_cat (a b : T) (s : seq T) :
    fset [:: a, b & s] = fset ([:: a; b] ++ s).
  Proof.
    by rewrite /(_ ++ _).
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


(* ** festU normalization
   The following tactics normalize fset(s) to fsetU(s) and
   provide a simple tactic to move and rotate the members of the
   fset.
*)

Ltac normalize_lhs :=
  match goal with
  | [ |- ?mLHS = _ ] =>
      match mLHS with
      | context [ fset (cons _ (cons _ _)) ] =>
          repeat rewrite fset_cons_cat fset_cat fset_fsetU_norm2;
          repeat rewrite fsetUA
      end
  end.

Goal forall (T : ordType) (a b c d e : T),
  fset [:: a; b; c; d; e] = fset [:: a] :|: fset [:: b] :|: fset [:: c] :|: fset [:: d] :|: fset [:: e].
Proof.
  by intros; normalize_lhs.
Qed.

Ltac move_right n :=
  (* we need the other form for rewriting *)
  repeat rewrite -fsetUA;
  match n with
  | O   => rewrite fsetUC
  | S O => rewrite [(X in _ :|: X)]fsetUC (* parentheses needed: https://github.com/coq/coq/issues/10928 *)
  | S ?n =>
      do n! rewrite fsetUA; rewrite [(X in _ :|: X)]fsetUC
  end;
  (* normalize again with respect to the parenthesis *)
  repeat rewrite fsetUA.

Goal forall (T : ordType) (a b c d e : T),
    fset [:: a; b; c; d; e] = fset [:: b] :|: fset [:: c] :|: fset [:: d] :|: fset [:: e] :|: fset [:: a].
Proof.
  by intros; normalize_lhs; move_right 0.
Qed.

Goal forall (T : ordType) (a b c d e : T),
    fset [:: a; b; c; d; e] = fset [:: a] :|: fset [:: c] :|: fset [:: d] :|: fset [:: e] :|: fset [:: b].
Proof.
  by intros; normalize_lhs; move_right 1.
Qed.

Goal forall (T : ordType) (a b c d e : T),
    fset [:: a; b; c; d; e] = fset [:: a] :|: fset [:: b] :|: fset [:: d] :|: fset [:: e] :|: fset [:: c].
Proof.
  by intros; normalize_lhs; move_right 2.
Qed.

Goal forall (T : ordType) (a b c d e : T),
    fset [:: a; b; c; d; e] = fset [:: a] :|: fset [:: b] :|: fset [:: c] :|: fset [:: e] :|: fset [:: d].
Proof.
  by intros; normalize_lhs; move_right 3.
Qed.

Ltac denormalize :=
  (* now fold back into fset (from right to left ... think list!) *)
  repeat rewrite -fset_cat cat1s.
