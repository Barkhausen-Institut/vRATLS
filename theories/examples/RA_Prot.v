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

From vRATLS Require Import examples.Signature.
From vRATLS Require Import examples.RA.
From vRATLS Require Import examples.Sig_Prot. Print SignatureProt. 
(*Import SignatureProt. 
Export SignatureProt. *)

Module Type Protocol
    (π1 : SignatureParams)
    (π2 : SignatureConstraints)
    (RAP : RemoteAttestationParams π2)
    (KG : KeyGeneration π1 π2)
    (Alg : SignatureAlgorithms π1 π2 KG)
    (RAA : RemoteAttestationAlgorithms π1 π2 RAP KG Alg)
    (SP : SignaturePrimitives π1 π2 KG Alg)
    (RAH : RemoteAttestationHash π1 π2 RAP KG Alg RAA SP)

    (SigP: SignatureProt π1 π2 KG Alg SP)
    .

  Import π1 π2 RAP KG Alg RAA SP RAH SigP.

  Definition i_chal := #|Challenge|.
  Definition att : nat := 50.

  Definition RA_prot_interface := 
    [interface #val #[att] : 'unit → 'pubkey × ('attest × 'bool) ].

  Definition Att_prot : package Attestation_locs_real 
     Att_interface RA_prot_interface
  := [package
    #def  #[att] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      #import {sig #[get_pk_att] : 'unit →  'pubkey } as get_pk_att ;;
      #import {sig #[attest] : 'challenge → ('signature × 'message)  } as attest ;;
      #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;
  
      (* Protocol *)
      pk ← get_pk_att tt ;;
      chal ← sample uniform i_chal ;;
      '(att, msg) ← attest chal ;;
      bool ← verify_att (chal, att) ;;
      ret (pk, ( att, bool ))
    } 
  ].

  Equations Att_prot_real : package Attestation_locs_real 
     [interface] RA_prot_interface :=
    Att_prot_real := {package Att_prot ∘ Att_real_c }.
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
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    Defined.

    Equations Att_prot_ideal : package Attestation_locs_ideal [interface] RA_prot_interface :=
      Att_prot_ideal := {package Att_prot ∘ Att_ideal_c }.
    Next Obligation.
      ssprove_valid.
      - rewrite /Key_locs/Attestation_locs_ideal/Attestation_locs_real/Key_locs.
        rewrite -fset_cat /cat.
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
        apply fsub0set.
      - rewrite /Key_locs/Attestation_locs_ideal/Attestation_locs_real/Key_locs.
        rewrite -fset_cat /cat.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        apply fsubsetxx.
    Defined.

  (* This prop is different from the RA prop, because it has much more inputs *)
  Parameter RA_prop:
    ∀ (l: {fmap (Signature * chState * chChallenge ) -> 'unit}) 
      (s s' s'' : chState) (pk : PubKey) (sk : SecKey) (chal : chChallenge) (h  : chMessage),
    Ver_sig pk (Sign sk (Hash s chal)) (Hash s' chal) 
    = ((Sign sk (Hash s chal), s'', chal) \in domm l).

  Lemma ra_prot_indist: 
    Att_prot_real ≈₀ Att_prot_ideal.
  Proof.
  eapply (eq_rel_perf_ind_ignore (fset [:: attest_loc_long])).
  - rewrite /Attestation_locs_real/Attestation_locs_ideal/Attestation_locs_real.
    apply fsubsetU.
    apply/orP.
    right.
    auto_in_fset.
    rewrite fsetUC.
    rewrite -!fset_cat.
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  - simplify_eq_rel x.   (* [x] becomes the argument to the procedure. *)
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_code_simpl; simplify_linking.
    ssprove_sync.
    ssprove_sync.
    ssprove_sync => pk.
    ssprove_sync => chal.
    ssprove_sync => sk.
    ssprove_sync => state.
    apply r_get_remember_rhs => a.
    apply r_get_remember_lhs => pk'.
    apply r_get_remember_lhs => state'.
    eapply r_put_rhs.
    ssprove_restore_mem.
    -- ssprove_invariant.
    -- eapply r_get_remember_rhs => a'.
       apply r_get_remember_rhs => state''.
       eapply r_ret => s0 s1 pre //=.
       split.
    --- repeat f_equal.
        eapply RA_prop. intuition eauto. 
    ---move: pre.
       by repeat case.
    Qed.       
  
  Print Module Type SignatureProt.
  Print Sig_prot_ideal.
  Print Sig_prot_ifce.
  Print RA_prot_interface.

  (*Definition convert_signature_to_attest (s:'signature) : 'attest := sig : 'attest. *)

    Print attest. Print signature.

   (*Definition convert_signature_to_attest (sig : Signature) : 'attest := sig. *)

   (** attest is not a type here, So, I'll use Signature as both input and output type 
  Definition convert_signature_to_attest (sig : Signature) : Signature := sig. **)
  Definition convert_signature_to_attest (sig : Attestation) : 'signature := sig.

(*  Definition Aux := 
    [package
      #def #[att] (_ : 'unit) : ('pubkey) × (('attest) × ('bool))
      {
        #import {sig #[protocol] : 'unit →  ('pubkey) × (('signature) × ('bool)) } as prot_sig ;;

        '(pk, (sig, bool)) ←  prot_sig tt ;;
        let attest := convert_signature_to_attest sig in
        ret (pk, (attest, bool))
      }
    ]. *)

Check attest.

  (*
  I cannot define this because the Challenge space and the Message space
  are abstract.
  There is only a single connection between these two spaces:
  the [Hash] function.
  *)
  Fail Definition xxx : chChallenge -> chMessage := id.

  Equations Aux_ideal :   
    package 
      Attestation_locs_ideal 
      Sig_ifce 
      RA_prot_interface
      := 
    Aux_ideal :=
    [package

      #def #[att] (_ : 'unit) : 'pubkey × ('attest × 'bool) 
      {
        #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;

        chal ← sample uniform i_chal ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        '(pk, (sig, bool)) ←  prot_sig msg ;;
        ret (pk, (sig, bool))
      }
    ].
    Next Obligation.
    ssprove_valid.
    - unfold Attestation_locs_ideal, Attestation_locs_real. Print fsetU. Search fsetU.
    rewrite  in_fset; auto.
  

  Equations Aux_real :   
    package 
      Attestation_locs_real 
      Sig_ifce 
      RA_prot_interface
      := 
    Aux_real :=
    [package

      #def #[att] (_ : 'unit) : 'pubkey × ('attest × 'bool) 
      {
        #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;

        chal ← sample uniform i_chal ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        '(pk, (sig, bool)) ←  prot_sig msg ;;
        ret (pk, (sig, bool))
      }
    ].


  (* Definition pred (n:nat) : nat :=
      match n with
      | O => 0
      | S n' => n'
      end.

    Lemma xxx : forall n, pred n = n.
    Proof.
      destruct n eqn:E.
      Fail unfold pred.
      Abort.
    
    Equations pred' (n:nat) : nat :=
      pred' O      := O;
      pred' (S n') := n'. *)

  Equations? Aux_Sig_prot_ideal : package Attestation_locs_ideal [interface] RA_prot_interface :=
      Aux_Sig_prot_ideal := {package Aux ∘ Sig_prot_ideal }.
      ssprove_valid.
    
  Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ Aux_Sig_prot_ideal.


    Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ Sig_prot_ideal.


  Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Aux ∘ Att_prot_ideal ≈₀ Sig_prot_ideal.


    Proof.


End Protocol.


Print SignatureProt. Print Sig_Prot. 

Module Type Example
(π1 : SignatureParams)
(π2 : SignatureConstraints)
(RAP : RemoteAttestationParams π2)
(KG : KeyGeneration π1 π2)
(Alg : SignatureAlgorithms π1 π2 KG)
(RAA : RemoteAttestationAlgorithms π1 π2 RAP KG Alg)
(SP : SignaturePrimitives π1 π2 KG Alg)
(RAH : RemoteAttestationHash π1 π2 RAP KG Alg RAA SP)
(Prot : Protocol π1 π2 RAP KG Alg RAA SP RAH)
(SigIdeal: SignatureProt π1 π2 KG Alg SP)
.
Import π1 π2 RAP KG Alg RAA SP RAH  SigIdeal.

Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ Sig_prot_ideal.
  Proof.



  Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ vRATLS.examples.Sig_Prot.SignatureProt.Sig_prot_ideal.
  Proof.

