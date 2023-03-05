(** *Introduction

In order to get into SSProve, it makes sense to look at a "simple" protocol
implementation and its verification.
I took this file straight from 'ssprove/theories/Crypt/examples/SigmaProtocol.v' and copied it here such
that I/we can add comments that will help us to understand.
*)
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

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

(** Simple scheme: Diffie Hellmann Key Exchange

The scheme: A, B agree on prime p and element g \in group G = Z_p

    A:                          B:
sample a from G
A = g^a          ----A --->
                             sample b from G
                             B = g^b
                <----B-----
k=B^a                        k'=A^b

Lemma: k = k'
**)

Locate ">".
Print cycle_group. (* Has Notation <[ g ]> *)

Locate "#[".
Print order.

(*
  The math part:
 *)
Module Type GroupParams.

  Parameter gT : finGroupType.            (* We need a group type of finite size. *)
  Definition ζ : {set gT} := [set : gT].  (* The group [Z_p] is a set of type finite group type. *)
  Parameter g :  gT.                      (* This is the group element [g]. *)
  Parameter g_gen : ζ = <[g]>.            (* Predicate: [Z_p] is equal to the cyclic group over [g]. *)
  Parameter prime_order : prime #[g].     (* Property: The order of the group generated from [g] is a prime number. *)

End GroupParams.

Module Type DiffieHellmannProtocolParams.

  Parameter Space: finType.
  Parameter Space_pos : Positive #|Space|.

End DiffieHellmannProtocolParams.


(*
  Here, we would define abstractions.
 *)
Module Type SigmaProtocolAlgorithms (DDHP : DiffieHellmannProtocolParams) (GP : GroupParams).

  Import DDHP.
  Import GP.

  #[local] Open Scope package_scope.

  #[local] Existing Instance Space_pos.

  (* We need to prove that #|GroupSpace| is positive. *)
  Definition GroupSpace : finType := FinGroup.arg_finType gT.
  #[local] Instance GroupSpace_pos : Positive #|GroupSpace|.
  Proof.
    apply /card_gt0P; by exists g.
  (* Needs to be transparent to unify with local positivity proof? *)
  Defined.

  Definition chGroup : choice_type := 'fin #|GroupSpace|.
  Notation " 'group " := (chGroup) (in custom pack_type at level 2).

  (* [p] itself is derived from the DiffieHellmann Parameters. *)
  Definition p := #|Space|.
  Definition chPElem : choice_type := 'fin p.

  Parameter Protocol_locs : {fset Location}.    (* | Here I will note all the steps of the protocol *)
  Parameter Simulator_locs : {fset Location}.   (* | This is for the simulator || not used yet *)

  (*
  Parameter Simulate :
    ∀ (g : choicePubKey) (sk_A : choicePrivKey) (sk_B : choicePrivKey),
      code Simulator_locs [interface] choiceTranscript.
   *)

End SigmaProtocolAlgorithms.

Module SigmaProtocol
  (DDHP : DiffieHellmannProtocolParams)
  (GP : GroupParams)
  (Alg : SigmaProtocolAlgorithms DDHP GP).

  Import Alg.
  Import GP. (* We actually only need [g], the group. *)

  (* This is a trick to give names to functions. *)
  Definition DDH : nat := 0.

  (* I want to store some elements of the group in the state. *)
  Definition sk_A : Location := (chPElem ; 0%N).
  Definition sk_B : Location := (chPElem ; 1%N).

  Definition Protocol_locs' := fset [:: sk_A ; sk_B].

  #[local] Open Scope package_scope.

  Print fto.

  Definition Diffie_Hellman_real:
  package Protocol_locs'
    [interface] (** No procedures from other packages are imported. *)
    [interface #val #[ DDH ] : 'unit → 'group × 'group] (** The "DDH" proceducre is exported. *)
  :=
  [package
    #def #[ DDH ] (u : 'unit) : 'group × 'group
    {
      (* Initially the state locations are empty. Let's fill them: *)
      sk_alice ← sample uniform p ;;
      sk_bob ← sample uniform p ;;
      #put sk_A := sk_alice ;;
      #put sk_B := sk_bob ;;

      (* Now, let's start with the protocol. *)

      (* Alice side: ephemeral key gen *)
      sk_alice' ← get sk_A ;;
      let e_a := (g^+ sk_alice') in

      (* Bob side: ephemeral key gen *)
      sk_bob' ← get sk_B ;;
      let e_b := (g^+ sk_bob') in

      (*
        If we want to model this properly then we would also have a state
        for the communication between Alice and Bob.
        Right now, the [Send_EphKey] function does not make much sense.
        It is essentially just [id].
       *)
      (*
      e_a_at_bob ← Send_EphKey e_a ;;
      e_b_at_alice ← Send_EphKey e_b ;;
       *)
      let e_a_at_bob := e_a in
      let e_b_at_alice := e_b in

      (* Alice side: final key gen *)
      let fk_alice := (e_b_at_alice^+ sk_alice') in

      (* Bob side: final key gen *)
      let fk_bob := (e_a_at_bob^+ sk_bob') in

     ret (fto fk_alice, fto fk_bob)
    }
  ].

  (** *** Simulated implementation
      Note that it uses the primitive [Simulate] that provides an
      ideal simulation.
  *)

  Definition Diffie_Hellman_ideal:
  package Simulator_locs
    [interface] (** No procedures from other packages are imported. *)
    [interface #val #[ TRANSCRIPT ] : chInput → chTranscript] (** The "TRANSCRIPT" proceducre is exported. *)
  :=
  [package
    #def #[ TRANSCRIPT ] (keys : chInput) : chTranscript
    {
     let '(g, sk_A, sk_B) := keys in
     t ← Simulate g sk_A sk_B ;;
     ret t
    }
  ].

  Definition ɛ_DH A := AdvantageE Diffie_Hellman_real Diffie_Hellman_ideal A.

 

