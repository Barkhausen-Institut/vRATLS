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

  Definition RA_locs_real := fset [:: pk_loc ; sk_loc ; chal_loc ; state_loc ; sign_loc ].
  Definition RA_locs_ideal := RA_locs_real :|: fset [:: attest_loc ].

  Definition att : nat := 50.

  Definition RA_prot_interface := 
    [interface #val #[att] : 'unit → 'pubkey × ('attest × 'bool) ].

  Definition Att_prot_real : package RA_locs_real 
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

  Definition Att_prot_ideal : package RA_locs_real 
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

  Definition Aux_locs := fset [:: pk_loc ; sk_loc ; state_loc ; chal_loc].

  Definition Aux_prot : package Aux_locs Sig_interface 
    RA_prot_interface :=
    [package
      #def  #[att] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
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

  Definition Aux_protp := {locpackage Aux_prot}.
  Definition Sig_realp := {locpackage Sig_real}.
  Definition Att_prot_real_p := {locpackage Att_prot_real}.
  
  Definition Comp_locs := fset [:: pk_loc; sk_loc ; state_loc; chal_loc ].
  
  
  Equations test : package Comp_locs Prim_interface RA_prot_interface :=
    test := {package Aux_protp ∘ Sig_realp}.
  Next Obligation.
    ssprove_valid.
    - rewrite /(locs Aux_protp)/Comp_locs.
      rewrite [X in fsubset _ X]fset_cons.
      unfold Aux_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - rewrite /(locs Sig_realp)/Comp_locs.
      rewrite [X in fsubset _ X]fset_cons.
      unfold Signature_locs_real.
      unfold Prim_locs_real.
      rewrite fset_cons.
      apply fsetUS.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsub0set.
    Defined.

  Lemma att_prot_to_sig_prot_real:
    Att_prot_real_p ≈₀ Att_prot_ideal_p.



  
  Lemma att_prot_to_sig_prot_real:
    Att_prot_real_p ≈₀ test.
   
(*
    Problem:
    In: Att_int  Out: [RA_Prot_interface]
    =
    In: Sig_interface  Out: RA_prot_interface
    ∘
    In: Prim_interface  Out: Sig_interface 
*)

  (* 
  New "the second"
  To have this Lemma, we want to base RA not on Att_primitives,
  but on sig primitives directly
  *)

  Definition Att_prot_real_sig : package RA_locs_real 
     Prim_interface RA_prot_interface
  := [package
    #def  #[attest] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
      #import {sig #[sign] : 'message → 'signature  } as sign ;;
      #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify_sig ;;

      (* Protocol *)
      pk ← get_pk tt ;;      
      state ← get state_loc ;;
      chal ← sample uniform i_chal ;;
      let msg := Hash state chal in
      att ← sign msg ;;
      bool ← verify_sig (att, msg) ;;
      ret (pk, ( att, bool ))
    } 
  ].

  Definition Att_prot_ideal_sig : package RA_locs_real 
    Prim_interface_f RA_prot_interface
  := [package
    #def  #[attest] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
      #import {sig #[sign_f] : 'message → 'signature  } as sign ;;
      #import {sig #[verify_sig_f] : ('signature × 'message) → 'bool } as verify_sig ;;

      (* Protocol *)
      pk ← get_pk tt ;;
      state ← get state_loc ;;
      chal ← sample uniform i_chal ;;
      let msg := Hash state chal in
      att ← sign msg ;;
      bool ← verify_sig (att, msg) ;;
      ret (pk, ( att, bool ))
    } 
  ].

  Definition Aux_protp := {locpackage Aux_prot}.
  Definition Sig_realp := {locpackage Sig_real}.

  Definition Comp_locs := fset [:: pk_loc; sk_loc ; state_loc; chal_loc ].


  Equations test : package Comp_locs Prim_interface RA_prot_interface :=
    test := {package Aux_protp ∘ Sig_realp}.
  Next Obligation.
  ssprove_valid.
  - rewrite /(locs Aux_protp)/Comp_locs.
    rewrite [X in fsubset _ X]fset_cons.
    unfold Aux_locs.
    rewrite fset_cons.
    apply fsetUS.
    rewrite [X in fsubset _ X]fset_cons.
    rewrite fset_cons.
    apply fsetUS.
    rewrite [X in fsubset _ X]fset_cons.
    rewrite fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsetUS.
    apply fsub0set.
  - rewrite /(locs Sig_realp)/Comp_locs.
    rewrite [X in fsubset _ X]fset_cons.
    unfold Signature_locs_real.
    unfold Prim_locs_real.
    rewrite fset_cons.
    apply fsetUS.
    rewrite [X in fsubset _ X]fset_cons.
    rewrite fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  Defined.
  (*
  Lemma att_prot_to_sig_prot_real:
    Att_prot_real ≈₀  test.
  *)

  Definition Att_prot_real_sigp := {locpackage Att_prot_real_sig}.

  
  Lemma att_prot_to_sig_prot_real:
   Att_prot_real_sigp ≈₀ test.




  
  


End Protocol.

