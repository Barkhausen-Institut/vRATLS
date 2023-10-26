(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.

(** REMOTE ATTESTATION
    VERIFIER                             PROVER
Generates a chal-
  lenge 'chal'
                   -----chal----->    
                                       Attestation
                                       (using TPM) 
                   <-----res------
Validity check
  of proof
  *)

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

Require Import examples.Signature.
Require Import examples.RA.

Module Protocol
    (π1 : SignatureParams)
    (π2 : HeapHash.RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2)
    (π4 : HeapHash.RemoteAttestationAlgorithms π1 π2 π3)
    (π5 : SignatureScheme π1 π2 π3)
    (π6 : HeapHash.RemoteAttestation π1 π2 π3 π4 π5).

  Import π1 π2 π3 π4 π5 π6.

  Definition chal_loc   : Location := ('challenge ; 5%N).
  Definition RA_locs := fset [:: state_loc ; chal_loc ; pk_loc].
  Definition RA   : nat := 46. (* routine to get the public key *)
  Definition RA_prot_interface := 
    [interface #val #[RA] : 'unit → ('pubkey × ('challenge × 'signature) ) ].

  

  Parameter Hash' : chState -> chChallenge -> chMessage.

  (*
  (* those are redefined, change above once fixed *)
  Definition Challenge := Arit (uniform pos_n).
  Definition chChal : choice_type := 'fin (mkpos pos_n).
  Notation " 'challenge " := Challenge       (in custom pack_type at level 2).
  Notation " 'challenge " := chChal        (at level 2): package_scope.*)

  Definition i_chal := #|Challenge|.

  Definition RA_real :
      package
        RA_locs
        Att_interface
        RA_prot_interface
    :=
    [package
      #def #[RA] (_ : 'unit) : ('pubkey × ('challenge × 'signature) )
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
        #import {sig #[attest] : 'challenge → ('signature × 'message) } as attest ;;
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;

        (* PROTOCOL *)

        (* Verifier-side *)
        (* ------------> *)
            (* get the public key *)
            pk ← get pk_loc ;;
            (* sample the challenge *)
            chal ← sample uniform i_chal ;;
            #put chal_loc := chal ;;
            (* take the state *)

            (* Send message to prover *)
            let chal_v := chal in

        (* Prover-side *)
        (* <---------- *)

            (* sign (=attest) message *)
            attest_tuple ← attest chal_v ;;
            let (att, msg) := attest_tuple in
            (* Send attestation to verifier *)
            let att_p := att in
            (* Send message to verifier *)
            let msg_p := msg in

        (* Verifier-side *)
        (* ------------> *)
            bool ← verify_att (chal, att_p) ;;
            if bool then

              (* Verifier checks state *)
              state ← get state_loc ;;
              let msg_v := Hash state chal_v in
              if msg_v == msg_p then
                (* We make the whole communication and the pk available to the attacker. *)
                 ret (pk, (chal, att))
              else
                (* We make the whole communication and the pk available to the attacker. *)
                 ret (pk, (chal, att)) 
            
            else 
              ret (pk, (chal, att)) 
          (* FIXME
            I do not think that the handling of state is properly done here.
            Not that this protocol assumes that the verifier and the prover
            have the verify same [pk] and [sk].
          *)
      }
    ].

  (* J: I think this is not the right way. *)
  (* Variant 1: unhash 
     let state_at_prover := get_state att_v in
     if state_at_prover == state then
       #put trust_loc := true;;
     else
       #put trust_loc := false;;
  *)

    Definition RA_ideal :
      package
        RA_locs
        Att_interface
        RA_prot_interface
    :=
    [package
      #def #[RA] (_ : 'unit) : ('pubkey × ('challenge × 'signature) )
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
        #import {sig #[attest] : 'challenge → ('signature × 'message) } as attest ;;
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;

        (* PROTOCOL *)

        (* Verifier-side *)
        (* ------------> *)
            (* get the public key *)
            pk ← get pk_loc ;;
            (* sample the challenge *)
            chal ← sample uniform i_chal ;;
            #put chal_loc := chal ;;
            (* take the state *)

            (* Send message to prover *)
            let chal_v := chal in

        (* Prover-side *)
        (* <---------- *)

            (* sign (=attest) message *)
            att ← sample uniform pos_n ;;
            msg ← sample uniform pos_n ;;
            (* Send attestation to verifier *)
            let att_p := att in
            (* Send message to verifier *)
            let msg_p := msg in

        (* Verifier-side *)
        (* ------------> *)
            bool ← verify_att (chal, att_p) ;;
            if bool then

              (* Verifier checks state *)
              state ← get state_loc ;;
              let msg_v := Hash state chal_v in
              if msg_v == msg_p then
                (* We make the whole communication and the pk available to the attacker. *)
                 ret (pk, (chal, att))
              else
                (* We make the whole communication and the pk available to the attacker. *)
                 ret (pk, (chal, att)) 
            
              else 
                 ret (pk, (chal, att)) 
          (* FIXME
            I do not think that the handling of state is properly done here.
            Not that this protocol assumes that the verifier and the prover
            have the verify same [pk] and [sk].
          *)
      }
    ].
    
    Definition mkpair' {Lt Lf E}
      (t: package Lt E E) (f: package Lf E E): loc_GamePair E :=
      fun b => if b then {locpackage t} else {locpackage f}.
    

    Definition RA_unforg := @mkpair RA_locs RA_locs RA_prot_interface RA_real RA_ideal.


    Theorem RA_prot_unforg LA A :
        ValidPackage LA Att_interface A_export A →
        fdisjoint LA (Sig_unforg true).(locs) →
        fdisjoint LA (Sig_unforg false).(locs) →
        fdisjoint LA Aux_locs →
        fdisjoint LA (Att_unforg true).(locs) →
        fdisjoint LA (Att_unforg false).(locs) →
        (Advantage Att_unforg A <= AdvantageE Sig_ideal Sig_real (A ∘ Aux))%R.
    Proof.


End Protocol.

