From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl
  Package Prelude RandomOracle.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Require Import Coq.Init.Logic.
Require Import List.

Set Equations With UIP.
(*
  This is needed to make definitions with Equations transparent.
  Otherwise they are opaque and code simplifications in the
  proofs with [ssprove_code_simpl] do not resolve properly.
 *)
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.

From vRATLS Require Import examples.Signature.
From vRATLS Require Import examples.RA.
From vRATLS Require Import examples.Sig_Prot.  
From vRATLS Require Import examples.RA_Facts.
(* A more generic definition for swapping codes. *)
Definition cmd_locs {A:choiceType} (c:command A) : {fset Location} :=
  match c with
  | cmd_op _  _ => fset0
  | cmd_get l => fset1 l
  | cmd_put l _ => fset1 l
  | cmd_sample _ => fset0
  end.

Definition pre_fun : heap * heap -> Prop := fun '(s0,s1) => s0 = s1.


(** This is an assumption of SSProve.
    Imports are resolved before stepping into the
    relational Hoare Logic.
    For reference, check out [ssprove_sync].
 *)
Definition no_import {A} (c: command A) : Prop :=
  match c with
  | cmd_op _ _ => False
  | _ => True
  end.

Lemma swap_get_disjoint {B l v} {c: command B} :
    no_import c ->
    fset1 l :#: cmd_locs c
    -> (forall x:B,
   ⊢ ⦃ λ '(s0, s1), (pre_fun ⋊ rem_lhs l v) (s0, s1) ⦄
     ret x
       ≈
     ret x
     ⦃ λ '(a0, s0) '(a1, s1), ( pre_fun ⋊ rem_lhs l v) (s0, s1) /\ a0 = a1 ⦄)
   ->
     ⊢ ⦃ λ '(s0, s1), (pre_fun ⋊ rem_lhs l v) (s0, s1) ⦄
       x ← cmd c ;;
       ret x
         ≈
       x ← cmd c ;;
       ret x
       ⦃ λ '(a0, s0) '(a1, s1), (pre_fun ⋊ rem_lhs l v) (s0, s1) /\ a0 = a1 ⦄.
Proof.
  elim: c => //=.
  - move => l1 _ d H1.
    ssprove_sync.
    + rewrite /get_pre_cond => s0 s1.
      rewrite /pre_fun => s0_eq_s1.
      by rewrite s0_eq_s1.
    + exact: H1.
  - move => l1 v0 _.
    rewrite fdisjoint1s; move/fset1P/eqP => l_neq_l1 H1.
    ssprove_sync => //=.
    rewrite /put_pre_cond/pre_fun => s0 s1 pre.
    by rewrite pre.
  - move => op _ _ H1.
    ssprove_sync.
    exact: H1.
Qed.

Lemma reshape_pair_id {T T0 T1 : Type} (f : T * T0 -> T1) : (fun '(pair x y) => f (pair x y)) = f.
  Proof.
    apply functional_extensionality; by [case].
Qed.


(* TODO move into SSProve. *)
Lemma r_swap_scheme_locs_cmd :
  ∀ {A B : choiceType} {S: {fset Location}} (s : raw_code A) (c : command B),
    no_import c ->
    S :#: cmd_locs c →
    ValidCode S [interface] s →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      x ← s ;; y ← cmd c ;; ret (x,y) ≈
      y ← cmd c ;; x ← s ;; ret (x,y)
    ⦃ eq ⦄.
Proof.
  intros A B S s c noi d h.
  induction h.
  - simpl. apply rreflexivity_rule.
  - eapply fromEmpty. rewrite fset0E. eauto.
  - simpl in *. eapply r_transR.
    + eapply (rswap_cmd_eq _ _ _ (cmd_get _) _). simpl.
      set xxx := fun '(s0,s1) => s0 = s1; rewrite -(reshape_pair_id xxx).
      eapply r_get_remember_lhs => a0.
      eapply (rsame_head_cmd_alt c).
      *
        (**
           At this point, I really need to do a case analysis.
           This really is a more general goal though that only holds when the heaps are disjoint!
           After all, the comand could be a write in which case I could not just say that reading the
           value afterwards, it turns out to be the same, as the post condition suggests.
         *)
        move/fdisjointP: d => d; specialize (d l H); move: d; rewrite -fdisjoint1s => d.
        apply (swap_get_disjoint noi d) => x.
        by apply r_ret.
      * move => a1. eapply r_get_remind_rhs.
        ** eapply Remembers_rhs_from_tracked_lhs.
           *** ssprove_invariant.
           *** rewrite /xxx; ssprove_invariant.
        ** ssprove_forget_all. rewrite /xxx.
           eapply r_ret => s0 s1 s0_eq_s1.
           repeat f_equal; exact s0_eq_s1.
    + simpl.
      ssprove_sync_eq.
      exact: H1.
  - simpl in *. eapply r_transR.
    +
      (* Fail eapply rswap_cmd_eq. *)
      instantiate (1 := cmd_bind (cmd_put l v) (fun z => cmd_bind c (fun y => bind k (fun x => ret (pair x y))))).
      simpl.
      case: c noi d IHh => //=.
      * move => l0 _ d IHh.
        ssprove_swap_lhs 0.
        ** move/fdisjointP: d => d; specialize (d l H); move: d.
           by rewrite in_fset1; move/eqP.
        ** apply rreflexivity_rule.
      * move => l0 v0 _ d IHh.
        ssprove_swap_lhs 0.
        ** move/fdisjointP: d => d; specialize (d l H); move: d.
           by rewrite in_fset1; move/eqP.
        ** apply rreflexivity_rule.
      * move => op _ d IHh.
        ssprove_swap_lhs 0.
        apply rreflexivity_rule.
    + simpl. ssprove_sync_eq.
      exact: IHh.
  - simpl in *.
    eapply r_transR.
    + eapply (rswap_cmd_eq _ _ _ (cmd_sample _) _). simpl.
      eapply rsamplerC'_cmd.
    + simpl. eapply (rsame_head_cmd (cmd_sample _)). intro a.
      eauto.
Qed.

Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
eapply r_swap_scheme_locs_cmd => //= ; ssprove_valid
: ssprove_swap.
