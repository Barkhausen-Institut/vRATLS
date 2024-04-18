(* so far, this is an abstract implementation of a signature scheme 
initially implemented for RA.v
Will be extended by actual signature implementations
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
  proofs with [ssprove_code_simpl] does not resolve properly.
 *)
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From vRATLS Require Import examples.Signature.

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.
Variable (n: nat).
Definition pos_n: nat := 2^n.
Definition chSet t := chMap t 'unit.
Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Module Type SignatureProt
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (KG : KeyGeneration π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KG)
  (Prim : SignaturePrimitives π1 π2 KG Alg).

  Import π1 π2 KG Alg Prim.

  Definition Sig_prot_ifce := 
    [interface #val #[sign] : 'message → 'pubkey × ('signature × 'bool) ].

  Definition Sig_prot : package Sig_locs_real Sig_ifce Sig_prot_ifce
    := [package
      #def  #[sign] (msg : 'message) : 'pubkey × ('signature × 'bool)
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
        #import {sig #[sign] : 'message → 'signature  } as sign ;;
        #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify_sig ;;
  
        (* Protocol *)
        pk ← get_pk tt ;;
        sig ← sign msg ;;
        bool ← verify_sig (sig, msg) ;;
        ret (pk, ( sig, bool ))
      } 
    ].
  

  Equations Sig_prot_real : package Sig_locs_real [interface] Sig_prot_ifce :=
    Sig_prot_real := {package Sig_prot ∘ Sig_real_c }.
  Next Obligation.
    ssprove_valid.
    - rewrite /Sig_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    - rewrite /Key_locs/Sig_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    Defined.

    Equations Sig_prot_ideal : package Sig_locs_ideal [interface] Sig_prot_ifce :=
      Sig_prot_ideal := {package Sig_prot ∘ Sig_ideal_c }.
    Next Obligation.
      ssprove_valid.
      - rewrite /Key_locs/Sig_locs_ideal/Sig_locs_real/Key_locs.
        rewrite -fset_cat /cat.
        rewrite fset_cons.
        rewrite [X in fsubset X _]fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        rewrite [X in fsubset X _]fset_cons.
        apply fsetUS.
        rewrite !fset_cons -fset0E.
        apply fsub0set.
      - rewrite /Key_locs/Sig_locs_ideal/Sig_locs_real/Key_locs.
        rewrite -fset_cat /cat.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        apply fsubsetxx.
    Defined.

  Lemma ext_unforge_sig_prot:
  Sig_prot_real ≈₀ Sig_prot_ideal.
  Proof.
    eapply (eq_rel_perf_ind_ignore (fset [:: sign_loc])).
    - rewrite /Sig_locs_real/Sig_locs_ideal.
      apply fsubsetU.
      apply/orP.
      right.
      rewrite !fset_cons.
      apply fsubsetU ; apply /orP ; right.
      apply fsetUS.
      apply fsubsetxx.
    - simplify_eq_rel m.
      simplify_linking.
      ssprove_sync. ssprove_sync.
      ssprove_sync => pk.
      ssprove_sync => sk.
      eapply r_get_remember_rhs => sig.
      eapply r_put_rhs.
      ssprove_restore_mem.
      -- ssprove_invariant.
      -- eapply r_get_remember_rhs => sig'.
         eapply r_get_remember_lhs => KG_pk.
         eapply r_ret => s0 s1 pre //=.
         split.
      ---- repeat f_equal.
           apply Signature_prop.
      ---- by [move: pre; rewrite /inv_conj; repeat case].
  Qed.
      
End SignatureProt.

