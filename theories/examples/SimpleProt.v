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

(** Simple scheme: Diffie Hellmann Key Exchange

The scheme: A, B agree on prime p and element g \in group G = Z_p

    A:                          B:
samle a from G   
A = g^a          ----A --->   
                             sample b from G
                             B = g^b
                <----B-----
k=B^a                        k'=A^b 

Lemma: k = k'
**)


Module Type SigmaProtocolParams.

  Parameter PubKey PrivKey EphKey Message Space: finType.
  Parameter g : PubKey.
  Parameter sk_A : PrivKey.
  Parameter sk_B : PrivKey.

  Parameter PubKey_pos : Positive #|PubKey|.
  Parameter PrivKey_pos : Positive #|PrivKey|. 
  Parameter EphKey_pos : Positive #|EphKey|.
  Parameter Space_pos : Positive #|Space|.

End SigmaProtocolParams.


Module Type SigmaProtocolAlgorithms (π : SigmaProtocolParams).

  Import π.

  #[local] Open Scope package_scope. 

  #[local] Existing Instance PubKey_pos.    
  #[local] Existing Instance PrivKey_pos.
  #[local] Existing Instance EphKey_pos.
  #[local] Existing Instance Space_pos.

  Definition choicePubKey := 'fin #|PubKey|.      
  Definition choicePrivKey := 'fin #|PrivKey|.
  Definition choiceEphKey := 'fin #|EphKey|. (**  ephemeral keys: A=g^a and B=g^b   **)
  Definition choiceTranscript :=
    chProd (chProd (chProd (chProd choicePubKey choicePrivKey) choicePrivKey) choiceEphKey ) choiceEphKey.

  Parameter Protocol_locs : {fset Location}.    (* | Here I will note all the steps of the protocol *)
  Parameter Simulator_locs : {fset Location}.   (* | This is for the simulator || not used yet *)

 
  Parameter EphKey :
  ∀ (g : choicePubKey),
    code Protocol_locs [interface] choiceEphKey.

  Parameter Send_EphKey :
    ∀ (g : choiceEphKey),
      code Protocol_locs [interface] choiceEphKey.
    
  Parameter Simulate :
    ∀ (g : choicePubKey) (sk_A : choicePrivKey) (sk_B : choicePrivKey),
      code Simulator_locs [interface] choiceTranscript.

End SigmaProtocolAlgorithms.

Module SigmaProtocol (π : SigmaProtocolParams)
  (Alg : SigmaProtocolAlgorithms π).

  Import π.
  Import Alg.

  Notation " 'chPubKey' " :=
    choicePubKey (in custom pack_type at level 2).
  Notation " 'chPrivKey' " :=
    choicePrivKey (in custom pack_type at level 2).
  Notation " 'chTranscript' " :=
    choiceTranscript (in custom pack_type at level 2).
  (*Definition choiceInput :=  chProd (chProd choicePubKey choicePrivKey) choicePrivKey.)*)
  Definition choiceInput :=  choicePubKey.
  Notation " 'chInput' " := 
    choiceInput (in custom pack_type at level 2).

  (**
     This is a trick to give names to functions.
   *)
  Definition TRANSCRIPT : nat := 0.
  Definition COM : nat := 1.
  Definition VER : nat := 2.
  Definition ADV : nat := 3.
  Definition SOUNDNESS : nat := 4.


  Definition skA : Location := (choicePrivKey ; 0%N).
  Definition skB : Location := (choicePrivKey ; 1%N).

  Definition Protocol_locs' :=
    fset [:: skA ; skB].

  #[local] Open Scope package_scope.

  Definition Diffie_Hellman_real:
  package Protocol_locs'
    [interface] (** No procedures from other packages are imported. *)
    [interface #val #[ TRANSCRIPT ] : chInput → chTranscript] (** The "TRANSCRIPT" proceducre is exported. *)
  :=
  [package
    #def #[ TRANSCRIPT ] (keys : chInput) : chTranscript
    {
     let g := keys in
     skA2 <- get skA ;;
     let e_a := (g^+ skA2) in
     A ← Send_EphKey e_a ;;
     (*skB2 <- get skB ;;
     let e_b := g+ skB2 in
     B ← Send_EphKey e_b ;; *)
     @ret choiceTranscript (e_a)
     (* @ret choiceTranscript (e_a, e_b) *)
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

 

