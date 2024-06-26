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

  Definition protocol := 30.
  Definition Sig_prot_ifce :=
    [interface #val #[protocol] : 'message → 'pubkey × ('signature × 'bool) ].

  Definition Sig_prot : package Sig_locs_real Sig_ifce Sig_prot_ifce
    := [package
      #def  #[protocol] (msg : 'message) : 'pubkey × ('signature × 'bool)
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

  Module Correctness.

    Definition prot_res := 100.

    Definition Prot_res_ifce :=
      [interface #val #[prot_res] : 'message → 'unit ].


    Equations prot_result (msg : 'message) : code Sig_locs_real Sig_prot_ifce 'bool :=
      prot_result msg := {code
        #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as protocol ;;
        '(pk, t) ← protocol msg;;
        let '(_, result) := t in
        ret result
    }.

    (* FIXME This just cannot simplify because it is not clear what the import is! *)
    Theorem prot_correct seed msg:
        Run sampler (prot_result msg) seed = Some true.
    Proof.
      simpl.
    Admitted.


    Equations prot_result_pkg : package Sig_locs_real Sig_prot_ifce Prot_res_ifce
      :=
      prot_result_pkg := [package
            #def  #[prot_res] (msg : 'message) : 'unit
            {
              #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as protocol ;;
              '(_, t) ← protocol msg;;
              let '(_, result) := t in
              ret tt
            }
        ].

    (* TODO Why do I need this cast here? *)
    Definition tt_ : chElement 'unit := tt.

    Equations prot_result_pkg' : package Sig_locs_real Sig_prot_ifce Prot_res_ifce
      :=
      prot_result_pkg' := [package
        #def  #[prot_res] (msg : 'message) : 'unit
        {
          #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as protocol ;;
          '(_, t) ← protocol msg;;
          let '(_, result) := t in
          #assert (result == true) ;;
          ret tt_
        }
        ].

    Equations prot_result_real : package Sig_locs_real [interface] Prot_res_ifce :=
      prot_result_real := {package prot_result_pkg ∘ Sig_prot ∘ Sig_real_c }.
    Next Obligation.
      ssprove_valid.
      all: by [apply: fsubsetxx].
    Defined.

    Equations prot_result_real' : package Sig_locs_real [interface] Prot_res_ifce :=
      prot_result_real' := {package prot_result_pkg' ∘ Sig_prot ∘ Sig_real_c }.
    Next Obligation.
      ssprove_valid.
      all: by [apply: fsubsetxx].
    Defined.

    Lemma fun_correct:
      prot_result_real ≈₀ prot_result_real'.
    Proof.
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel x.
      all: simplify_linking; ssprove_code_simpl.
      repeat ssprove_sync_eq.
      move => _.
      ssprove_sync_eq => sk.
      ssprove_sync_eq => pk.
      rewrite /tt_.
      rewrite (Signature_correct pk sk x) /=.
      apply r_ret => s0 s1 s0_eq_s1 //=.
    Qed.

  End Correctness.

End SignatureProt.

