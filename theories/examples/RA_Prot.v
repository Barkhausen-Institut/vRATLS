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
    (π2 : SignatureConstraints)
    (RAP : RemoteAttestationParams π2)
    (KG : KeyGeneration π1 π2)
    (Alg : SignatureAlgorithms π1 π2 KG)
    (RAA : RemoteAttestationAlgorithms π1 π2 RAP KG Alg)
    (SP : SignaturePrimitives π1 π2 KG Alg)
    (RAH : RemoteAttestationHash π1 π2 RAP KG Alg RAA SP)
    .

  Import π1 π2 RAP KG Alg RAA SP RAH.

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
    
End Protocol.

