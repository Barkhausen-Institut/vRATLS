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

  

  Parameter Hash' : chState -> chChallenge -> chMessage.

  (*
  (* those are redefined, change above once fixed *)
  Definition Challenge := Arit (uniform pos_n).
  Definition chChal : choice_type := 'fin (mkpos pos_n).
  Notation " 'challenge " := Challenge       (in custom pack_type at level 2).
  Notation " 'challenge " := chChal        (at level 2): package_scope.*)

  Definition i_chal := #|Challenge|.

  (* New Version *)

  Definition RA_locs_real := fset [:: pk_loc ; sk_loc ; chal_loc ; state_loc].
  Definition RA_locs_ideal := RA_locs_real :|: fset [:: attest_loc ].

  (* NEW VERSION *)

  Definition RA_prot_interface := 
    [interface #val #[attest] : 'unit → 'pubkey × ('attest × 'bool) ].

  Definition Att_prot_real : package RA_locs_real [interface] RA_prot_interface
  := [package
    #def  #[attest] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;

      chal ← sample uniform i_chal ;;
      #put chal_loc := chal ;;
      state ← get state_loc ;;
      let msg := Hash' state chal in
      let sig := Sign sk msg in
      let bool := Ver_sig pk sig msg in
      ret (pk, ( sig, bool ))
    } 
  ].

  Equations Att_prot_ideal : package RA_locs_ideal [interface] RA_prot_interface :=
  Att_prot_ideal := [package
    #def  #[attest] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;

      chal ← sample uniform i_chal ;;
      #put chal_loc := chal ;;
      state ← get state_loc ;;
      let msg := Hash' state chal in
      let att := Sign sk msg in

      A ← get attest_loc ;;
      let A' := setm A (att, msg) tt in
      #put attest_loc := A' ;;

      let bool := ( (att,msg) \in domm A) in
      ret (pk, ( att, bool ))
    } 
].
 Next Obligation.
 ssprove_valid; rewrite /RA_locs_ideal/RA_locs_real in_fsetU; apply /orP.
    1,2,3,4: left; auto_in_fset.
    1,2: right; auto_in_fset.
  Defined.


  Definition Aux_locs := fset [:: pk_loc ; state_loc ; chal_loc].

  Definition Aux : package Aux_locs Sign_interface2 RA_prot_interface :=
    [package
      #def  #[attest] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
      {
        #import {sig #[sign] : 'message → 'pubkey × ('signature × 'bool)}  as sign ;;
        state ← get state_loc ;;
        chal  ← get chal_loc ;;
        let msg := Hash state chal in
        sig ← sign msg ;;
        let '(pk, ( att, bool )) := sig in
        ret (pk, ( att, bool ))
      }
    ].

  Definition Sig_prot_unforg := 
    @mkpair Signature_locs_real Signature_locs_ideal Sign_interface2 
       Sig_prot_real Sig_prot_ideal.
  Definition Att_prot_unforg := 
    @mkpair RA_locs_real RA_locs_ideal RA_prot_interface 
       Att_prot_real Att_prot_ideal.

  Lemma prot_sig_real_vs_att_real_true:
    Att_prot_unforg true ≈₀  Aux ∘ Sig_prot_unforg true.
  Proof.
  Admitted.

  Lemma prot_sig_ideal_vs_att_ideal_false :
    Att_prot_unforg false ≈₀ Aux ∘ Sig_prot_unforg false.
  Proof.
  Admitted.

  Theorem RA_protunforg LA A :
      ValidPackage LA Att_interface A_export A →
      fdisjoint LA (Sig_prot_unforg true).(locs) →
      fdisjoint LA (Sig_prot_unforg false).(locs) →
      fdisjoint LA Aux_locs →
      fdisjoint LA (Att_prot_unforg true).(locs) →
      fdisjoint LA (Att_prot_unforg false).(locs) →
      (Advantage Att_prot_unforg A <= 
          AdvantageE Sig_prot_ideal Sig_prot_real (A ∘ Aux))%R.
   Proof.
   Admitted.
  






  (* Old Version *)

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

    Lemma RA_security:
      RA_prot_real ≈₀ RA_prot_ideal.
    
    Definition mkpair {Lt Lf E}
    (t: package Lt [interface] E) (f: package Lf [interface] E): loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.


    Definition mkpair' {Lt Lf E}
      (t: package Lt E) (f: package Lf E): loc_GamePair E :=
      fun b => if b then {locpackage t} else {locpackage f}.
    

    Definition RA_prot_unforg := @mkpair RA_locs RA_locs RA_prot_interface RA_real RA_ideal.


    Theorem RA_prot_unforg LA A :
        ValidPackage LA Att_interface A_export A →
        fdisjoint LA (Sig_unforg true).(locs) →
        fdisjoint LA (Sig_unforg false).(locs) →
        fdisjoint LA Aux_locs →
        fdisjoint LA (Att_unforg true).(locs) →
        fdisjoint LA (Att_unforg false).(locs) →
        (Advantage RA_prot_unforg <= Advantage Sig_unforg).
    Proof.


End Protocol.

