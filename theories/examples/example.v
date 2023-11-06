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


Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.

Variable (n: nat).
Definition pos_n: nat := 2^n.
Definition tt := Datatypes.tt.


Definition SecKey : choice_type := chFin(mkpos pos_n).
Definition PubKey : choice_type := chFin(mkpos pos_n).

Parameter KeyGen : ∀ {L : {fset Location}},
  code L [interface] (SecKey × PubKey).

Notation " 'pk "    := PubKey      (in custom pack_type at level 2).
Notation " 'pk "    := PubKey      (at level 2): package_scope.
Notation " 'sk "    := SecKey      (in custom pack_type at level 2).
Notation " 'sk "    := SecKey      (at level 2): package_scope.

Definition keygen : nat := 1.

Definition kg_int := [interface
  #val #[keygen] : 'unit → 'pk
].

Definition KG_lhs : package (fset [:: ]) [interface] kg_int
 := [package
  #def #[keygen] (_ : 'unit) : 'pk
   {
     '(sk,pk) ← KeyGen ;;
      ret pk
   }
].

Definition KG_rhs : package (fset [:: ]) [interface] kg_int
 := [package
  #def #[keygen] (_ : 'unit) : 'pk
   {
     '(sk,pk) ← KeyGen ;;
      ret pk
   }
].

Definition Aux : package (fset [:: ]) kg_int kg_int
 := [package
  #def #[keygen] (_ : 'unit) : 'pk
   {
     #import {sig #[keygen] : 'unit  → 'sk } as kg ;;
      pk ← kg tt ;;
      ret pk
   }
].

Lemma concat:
  KG_lhs ≈₀  Aux ∘ KG_rhs.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  ssprove_code_simpl.





