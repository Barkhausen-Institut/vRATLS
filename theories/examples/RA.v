(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.

REMOTE ATTESTATION:
------------------
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
From vRATLS Require Import extructurespp.ord.
From vRATLS Require Import extructurespp.fmap.
From vRATLS Require Import extructurespp.fset.

Module RemoteAttestationParams (π2 : SignatureParams).

  Import π2.

  Definition chState     : choice_type := 'fin (mkpos pos_n).
  Definition Attestation : choice_type := 'fin (mkpos pos_n).
  Definition chMessage   : choice_type := 'fin (mkpos pos_n).


End RemoteAttestationParams.

Module Type RemoteAttestationAlgorithms
  (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (* (Alg : SignatureAlgorithms π1 π2 KGc) *).

  Module π3 := RemoteAttestationParams π1.
  Import π1 π2 π3 KGc (* Alg *).
  Import KGc.KGP (* Alg.KG *).

  Local Open Scope package_scope.

  Notation " 'state "     := chState       (in custom pack_type at level 2).
  Notation " 'state "     := chState       (at level 2): package_scope.
  Notation " 'challenge " := chChallenge   (in custom pack_type at level 2).
  Notation " 'challenge " := chChallenge   (at level 2): package_scope.
  Notation " 'attest "    := Attestation    (in custom pack_type at level 2).

  Definition state_loc   : Location := ('state    ; 9%N).
  Definition attest_loc  : Location := ('set (chSignature × chMessage) ; 10%N).
  Definition verify_att  : nat := 11.
  Definition attest      : nat := 12.
  Definition get_pk_att  : nat := 13.

  Parameter Hash : chState -> chChallenge -> chMessage.
  Parameter Collision_Resistence: injective (uncurry Hash).

End RemoteAttestationAlgorithms.

Module Type RemoteAttestationHash
  (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KGc)
  (RAA : RemoteAttestationAlgorithms π1 π2 KGc).

  Module π3 := RemoteAttestationParams π1.
  Module SP := SignaturePrimitives π1 π2 KGc Alg.
  Import π1 π2 π3 KGc Alg RAA SP.
  Import KGc.KGP SP.KG.


  Definition attest_loc_long  : Location := ('set (chSignature × chState × chChallenge) ; 2%N).

  Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
  Definition Attestation_locs_ideal := Attestation_locs_real :|: fset [:: attest_loc_long ].

  Definition Att_interface := [interface
    #val #[get_pk_att] : 'unit → 'pubkey ;
    #val #[attest] : 'challenge → ('signature × 'message) ;
    #val #[verify_att] : ('challenge × 'signature) → 'bool
  ].

  Definition Att_real : package Attestation_locs_real KeyGen_ifce
      Att_interface := [package
      #def  #[get_pk_att] (_ : 'unit) : 'pubkey
      {
        #import {sig #[key_gen] : 'unit → ('seckey × 'pubkey) } as key_gen ;;
        '(sk,pk) ← key_gen tt ;;
        pk ← get pk_loc  ;;
        ret pk
      };
      #def #[attest] (chal : 'challenge) : ('signature × 'message)
      {
        sk ← get sk_loc  ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let att := Sign sk msg in
        ret (att, msg)
      };
      #def #[verify_att] ('(chal, att) : ('challenge × 'signature)) : 'bool
      {
        pk ← get pk_loc ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let bool := Ver_sig pk att msg in
        ret bool
      }
  ].

  Equations Att_ideal : package Attestation_locs_ideal KeyGen_ifce Att_interface :=
    Att_ideal := [package
      #def  #[get_pk_att] (_ : 'unit) : 'pubkey
      {
        #import {sig #[key_gen] : 'unit → ('seckey × 'pubkey) } as key_gen ;;
        '(sk,pk) ← key_gen tt ;;
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] (chal : 'challenge) : ('signature × 'message)
      {
        sk ← get sk_loc  ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let att := Sign sk msg in
        A ← get attest_loc_long ;;
        #put attest_loc_long := setm A (att, state, chal) tt ;;
        ret (att, msg)
      };

      #def #[verify_att] ('(chal, att) : ('challenge × 'signature)) : 'bool
      {
        A ← get attest_loc_long ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let b :=  (att, state, chal) \in domm A in
        ret b
      }
    ].
    (*
    Next Obligation.
      ssprove_valid; rewrite /Attestation_locs_ideal/Attestation_locs_real in_fsetU; apply /orP.
      1,5,6: right; auto_in_fset.
      all: left; auto_in_fset.
    Defined.
    *)
    Next Obligation.
      ssprove_valid; rewrite /Attestation_locs_ideal/Attestation_locs_real in_fsetU/Key_locs; apply /orP.
      1,5,6: right; auto_in_fset.
      all: left; auto_in_fset.
    Defined.

    (* We need a common interface, so we need to define an [AUX] for the
       signature scheme.*)
  Definition Aux_locs := fset [:: pk_loc  ; state_loc ].

  (*Definition Aux_locs := fset [:: pk_loc ; sk_loc ; sign_loc ; state_loc ]. *)

  Definition Aux : package Aux_locs Sig_ifce Att_interface :=
    [package
      #def #[get_pk_att] (_ : 'unit) : 'pubkey
      {
        #import {sig #[get_pk] : 'unit  → 'pubkey } as get_pk ;;
        pk ← get_pk tt ;;
        ret pk
      };

      #def #[attest] ( chal : 'challenge ) : ('signature × 'message)
      {
        #import {sig #[sign] : 'message  → 'signature } as sign ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        att ← sign msg ;;
        ret (att, msg)
      };

      #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
      {
        #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        b  ← verify (att,msg) ;;
        ret b
      }
    ].

  Equations Att_real_c : package Attestation_locs_real [interface] Att_interface :=
    Att_real_c := {package Att_real ∘ Key_Gen}.
  Next Obligation.
    ssprove_valid.
    - rewrite /Attestation_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    - rewrite /Key_locs/Attestation_locs_real/Key_locs.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsub0set.
  Qed.

  Equations Att_ideal_c : package Attestation_locs_ideal [interface] Att_interface :=
    Att_ideal_c := {package Att_ideal ∘ Key_Gen}.
  Next Obligation.
    ssprove_valid.
    - rewrite /Attestation_locs_ideal/Attestation_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    - rewrite /Key_locs/Attestation_locs_ideal/Attestation_locs_real/Key_locs.
      rewrite -fset_cat /cat.
      rewrite fset_cons.
      rewrite [X in fsubset X _]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset X _]fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsub0set.
  Qed.


  (* TODO Why do I need that at all?! *)
  Definition Comp_locs := fset [:: pk_loc ; sk_loc ; state_loc ; sign_loc ].

  (*
  Definition Aux_ideal : package Aux_locs Sig_ifce Att_interface :=
  [package
    #def #[get_pk_att] (_ : 'unit) : 'pubkey
    {
      #import {sig #[get_pk] : 'unit  → 'pubkey } as get_pk ;;
      pk ← get_pk tt ;;
      ret pk
    };

    #def #[attest] ( chal : 'challenge ) : ('signature × 'message)
    {
      #import {sig #[sign] : 'message  → 'signature } as sign ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      att ← sign msg ;;
      ret (att, msg)
    };

    #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
    {
      #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      b  ← verify (att,msg) ;;
      ret b
    }
  ].
   *)

  Definition Sig_real_locp  := {locpackage Sig_real ∘ Key_Gen}.
  Definition Sig_ideal_locp := {locpackage Sig_ideal ∘ Key_Gen}.
  Definition Att_real_locp  := {locpackage Att_real ∘ Key_Gen}.
  Definition Att_ideal_locp := {locpackage Att_ideal ∘ Key_Gen}.
  Definition Key_Gen_locp   := {locpackage Key_Gen}.

  Equations Aux_Sig_ideal : package Comp_locs KeyGen_ifce Att_interface :=
    Aux_Sig_ideal := {locpackage Aux ∘ Sig_ideal}.
  Next Obligation.
    ssprove_valid.
    - rewrite /Aux_locs/Comp_locs/Key_locs/Aux_locs.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite !fset_cons.
      apply fsubsetU ; apply /orP ; right.
      apply fsetUS.
      apply fsubsetU ; apply /orP ; right.
      apply fsubsetxx.
    - rewrite /(locs Sig_ideal_locp)/Comp_locs/Key_locs/Sig_ideal_locp/Sig_locs_ideal/Sig_locs_real/Key_locs.
      rewrite -fset_cat.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetU ; apply /orP ; right.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
  Defined.

  Definition Att_ideal_locp_heap := Attestation_locs_ideal.
  Definition Aux_prim_ideal_heap := Comp_locs.

  Definition attest_set := 'set (chSignature × chState × chChallenge).
  Definition sign_set := 'set ('signature × 'message).


End RemoteAttestationHash.
