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
  Definition RA   : nat := 46. 

  Parameter Hash' : chState -> chChallenge -> chMessage.

  Definition i_chal := #|Challenge|.

  Definition RA_locs_real := fset [:: pk_loc ; sk_loc ; chal_loc ; state_loc ; sign_loc ].
  Definition RA_locs_ideal :=  RA_locs_real :|: fset [:: attest_loc].

  Definition att : nat := 50.

  Definition RA_prot_interface := 
    [interface #val #[att] : 'unit → 'pubkey × ('attest × 'bool) ].

  Definition Att_prot : package RA_locs_real 
     Att_interface RA_prot_interface
  := [package
    #def  #[att] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
      #import {sig #[attest] : 'challenge → ('signature × 'message)  } as attest ;;
      #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;
  
      (* Protocol *)
      pk ← get_pk tt ;;
      chal ← sample uniform i_chal ;;
      '(att, msg) ← attest chal ;;
      bool ← verify_att (chal, att) ;;
      ret (pk, ( att, bool ))
    } 
  ].

  Equations Att_prot_real : package RA_locs_real [interface] RA_prot_interface :=
    Att_prot_real := {package Att_prot ∘ Att_real }.
  Next Obligation.
    ssprove_valid. 
    - rewrite /RA_locs_real.
      rewrite !fset_cons.
      apply fsetUS.
      apply fsetUS.
      apply fsetUS.
      apply fsetUS.
      apply fsetUS.
      apply fsubsetxx.
    - rewrite/ Attestation_locs_real/RA_locs_real.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite !fset_cons.
      apply fsubsetU ; apply /orP ; right.
      apply fsetUS.
      apply fsubsetU ; apply /orP ; right.
      apply fsubsetxx.
    Defined.

  Equations Att_prot_ideal : package RA_locs_ideal [interface] RA_prot_interface :=
    Att_prot_ideal := {package Att_prot ∘ Att_ideal }.
  Next Obligation.
    ssprove_valid.
    - rewrite /RA_locs_ideal/RA_locs_real.
      rewrite -fset_cat.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset X _]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset X _]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset X _]fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - rewrite/ Attestation_locs_ideal/Attestation_locs_real/RA_locs_ideal/RA_locs_real.      
      rewrite -!fset_cat.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite !fset_cons.
      apply fsubsetU ; apply /orP ; right.
      apply fsetUS.
      apply fsubsetU ; apply /orP ; right.
      apply fsubsetxx.
    Defined.

(*
  Check fsetUS.
  Locate ":|:".
  Unset Printing Notations.
  Check fset_cons.
  Search fsetU.
*)
    
  Lemma ra_prot_indist: 
    Att_prot_real ≈₀ Att_prot_ideal.
  Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  Admitted.
  
    
End Protocol.

