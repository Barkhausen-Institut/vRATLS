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
    (π5 : SignaturePrimitives π1 π2 π3)
    (π6 : HeapHash.RemoteAttestation π1 π2 π3 π4 π5)
    (π7 : SignatureProt π1 π2 π3 π5).

  Import π1 π2 π3 π4 π5 π6 π7.

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

  Definition Aux : package Aux_locs Sig_interface RA_prot_interface :=
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

  (* Need to change that such that interface is not empty *)  
  Definition mkpair {Lt Lf E}
    (t: package Lt [interface] E) (f: package Lf [interface] E): loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.

  Definition Sig_prot_unforg := 
    @mkpair Signature_locs_real Signature_locs_ideal Sig_interface
       Sig_real Sig_ideal.
  Definition Att_prot_unforg := 
    @mkpair RA_locs_real RA_locs_ideal RA_prot_interface 
       Att_prot_real Att_prot_ideal.

  Lemma prot_sig_real_vs_att_real_true:
    Att_prot_unforg true ≈₀  Aux ∘ Sig_prot_unforg true.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    - 
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
  


End Protocol.

