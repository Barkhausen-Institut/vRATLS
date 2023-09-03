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

Require Import Coq.Init.Logic.
Require Import List.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import PackageNotation.

Module Type SignatureDefs.

    Variable (n: nat).
    Definition pos_n: nat := 2^n.
    Definition Seed : choice_type := chFin(mkpos pos_n).
    Definition SecKey : choice_type := chFin(mkpos pos_n).
    Definition PubKey : choice_type := chFin(mkpos pos_n).

    Parameter KeyGen : Seed -> (SecKey × PubKey).

    #[local] Open Scope package_scope.
    Parameter KeyGenM :
      ∀ {L : {fset Location}} (sd : Seed),
        code L [interface] (SecKey × PubKey).

End SignatureDefs.

Module RemoteAttestation (π : SignatureDefs).

  Import π.

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2) : package_scope.
  Notation " 'seckey "    := SecKey      (in custom pack_type at level 2) : package_scope.
  Notation " 'seed "      := Seed        (in custom pack_type at level 2) : package_scope.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition key_gen   : nat := 42.
  Definition KeyGen_locs := fset [:: pk_loc ; sk_loc ].
  Definition KG_interface := [interface #val #[key_gen] : 'seed → 'pubkey ].

  Definition KG_real :
  package KeyGen_locs
    [interface]
    KG_interface
  :=
  [package
    #def  #[key_gen] (sd : 'seed) : 'pubkey
    {
    let (sk,pk) := KeyGen sd in
    ret pk
    }
  ].

  Definition KG_ideal :
  package KeyGen_locs
    [interface]
    KG_interface
  :=
  [package
    #def  #[key_gen] (sd : 'seed) : 'pubkey
    {
    let (sk,pk) := KeyGen sd in
    ret pk
    }
  ].

  Definition mkpair {Lt Lf E}
    (t: package Lt [interface] E)
    (f: package Lf [interface] E):
    loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.

  Definition KG_ind := @mkpair KeyGen_locs KeyGen_locs KG_interface KG_real KG_ideal.

  Lemma KG_real_vs_KG_true :
  KG_ind true ≈₀ KG_ind false.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    Fail eapply rreflexivity_rule.
    Fail ssprove_sync.
    Fail eapply r_ret.
    Check rpost_weaken_rule.
    eapply rpost_weaken_rule.
    1:{ eapply rreflexivity_rule. }
    intros.
    move: H1; case eq_a0: a₀ => [b₀ s₀]; move => eq_a1 //=.
    move: eq_a1; case eq_a1: a₁ => [b₁ s₁]; move => eq_b_s.
    by [injection eq_b_s => eq_s eq_b].
  Qed.

End RemoteAttestation.

Module RemoteAttestationM (π : SignatureDefs).

  Import π.

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2) : package_scope.
  Notation " 'seckey "    := SecKey      (in custom pack_type at level 2) : package_scope.
  Notation " 'seed "      := Seed        (in custom pack_type at level 2) : package_scope.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition key_gen   : nat := 42.
  Definition KeyGen_locs := fset [:: pk_loc ; sk_loc ].
  Definition KG_interface := [interface #val #[key_gen] : 'seed → 'pubkey ].

  Definition KG_real :
  package KeyGen_locs
    [interface]
    KG_interface
  :=
  [package
    #def  #[key_gen] (sd : 'seed) : 'pubkey
    {
    '(sk,pk) ← KeyGenM sd ;;
    ret pk
    }
  ].

  Definition KG_ideal :
  package KeyGen_locs
    [interface]
    KG_interface
  :=
  [package
    #def  #[key_gen] (sd : 'seed) : 'pubkey
    {
    '(sk,pk) ← KeyGenM sd ;;
    ret pk
    }
  ].

  Definition mkpair {Lt Lf E}
    (t: package Lt [interface] E)
    (f: package Lf [interface] E):
    loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.

  Definition KG_ind := @mkpair KeyGen_locs KeyGen_locs KG_interface KG_real KG_ideal.

  Lemma KG_real_vs_KG_true :
  KG_ind true ≈₀ KG_ind false.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    Fail eapply rsame_head.
    Fail eapply rsame_head_alt.
    eapply rpost_weaken_rule.
    1:{ eapply rreflexivity_rule. }
    intros.
    move: H1; case eq_a0: a₀ => [b₀ s₀]; move => eq_a1 //=.
    move: eq_a1; case eq_a1: a₁ => [b₁ s₁]; move => eq_b_s.
    by [injection eq_b_s => eq_s eq_b].
  Qed.

End RemoteAttestationM.
