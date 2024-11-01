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

Module Protocol
  (π1 : SignatureParams)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KGc)
  (RAA : RemoteAttestationAlgorithms π1 π2  KGc)
  (RAH : RemoteAttestationHash π1 π2 KGc Alg RAA).

  Module π3 := RemoteAttestationParams π1.
  Module SP := SignaturePrimitives π1 π2 KGc Alg.
  Import π1 π2 π3 KGc Alg RAA SP RAH.
  Import KGc.KGP SP.KG.

  Definition i_chal := #|Challenge|.
  Definition att : nat := 50.

  Definition RA_prot_interface :=
    [interface #val #[att] : 'unit → 'pubkey × ('signature × 'bool) ].

  Definition Att_prot : package Attestation_locs_real
     Att_interface RA_prot_interface
  := [package
    #def  #[att] ( _ : 'unit) : 'pubkey × ('signature × 'bool)
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
    ∀ (l: {fmap (chSignature * chState * chChallenge ) -> 'unit}) 
      (s s' s'' : chState) (pk : 'pubkey) (sk : 'seckey) (chal : chChallenge) ,
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
    rewrite /cast_fun/eq_rect_r/eq_rect.
      simplify_linking.
      ssprove_code_simpl.
      eapply rsame_head_alt_pre.
      -- apply (rpost_weaken_rule _
      (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ heap_ignore (fset [:: attest_loc_long]) (s₀, s₁))).
        --- eapply r_reflexivity_alt.
          ---- instantiate (1:=Key_locs). destruct KeyGen. exact: prog_valid.
          ---- move => l.
          rewrite /Key_locs. unfold Key_locs => l_not_in_Key_locs. (* Why does rewrite fail? *)
          ssprove_invariant.                      
          move: l_not_in_Key_locs.
          rewrite fset_cons.
          apply/fdisjointP.
          rewrite fdisjointUl.
          apply/andP.
          split; 
          (( try rewrite -fset1E); rewrite fdisjoint1s; auto_in_fset). 
          ---- move => l v l_not_in_Key_locs. ssprove_invariant.
        --- case => a0 s0; case => a1 s1. case => l r. by [split].
    --intro a.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      destruct a.
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
    --- ssprove_invariant.
    --- eapply r_get_remember_rhs => a'.
       apply r_get_remember_rhs => state''.
       eapply r_ret => s2 s1 pre //=.
       split.
    ---- repeat f_equal.
         eapply RA_prop. 
    ---- move: pre.
         by repeat case.
    Qed.       
    
End Protocol.

