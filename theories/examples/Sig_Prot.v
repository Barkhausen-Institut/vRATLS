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

Module SignatureProt
  (π1 : SignatureParams)
  (π2 : KeyGenParams π1)
  (π3 : KeyGen_code π1 π2)
  (π4 : SignatureAlgorithms π1 π2 π3).

  Module π5 := SignaturePrimitives π1 π2 π3 π4.
  Import π1 π2 π3 π4 π5.
  Import π3.KGP π5.KG.

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
      rewrite /cast_fun/eq_rect_r/eq_rect.
      simplify_linking.
      ssprove_code_simpl.
      eapply rsame_head_alt_pre.
      -- apply (rpost_weaken_rule _
      (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ heap_ignore (fset [:: sign_loc]) (s₀, s₁))).
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
      -- intro a.
         (*
         ssprove_code_simpl.
         ssprove_code_simpl_more.
          *)
         destruct a.
         ssprove_sync.
         ssprove_sync.
         ssprove_sync => pk.
         ssprove_sync => sk.
         eapply r_get_remember_rhs => sig.
         eapply r_put_rhs.
         ssprove_restore_mem.
         (*
           At this point, the proof looses the information about
           what is put into the [sign_loc].
           This is due to the [heap_ignore] invariant.
           What are basically saying that we do not care what is
           being stored in [sign_loc] for the proof.
          *)
         --- ssprove_invariant.
         --- eapply r_get_remember_rhs => sig'.
             eapply r_get_remember_lhs => KG_pk.
             eapply r_ret.
             intuition eauto.
             ---- repeat f_equal.
                  apply Signature_prop.
             ---- by [move: H; rewrite /inv_conj; repeat case].
  Qed.

  (* FIXME
     This is still insufficient!
     It misses the key generation evidence.
   *)
  Axiom Signature_correct_fail: forall pk sk msg, Ver_sig pk (Sign sk msg) msg == true.

  Lemma ext_unforge_sig_prot_full:
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
      rewrite /cast_fun/eq_rect_r/eq_rect.
      simplify_linking.
      ssprove_code_simpl.
      eapply rsame_head_alt_pre.
      -- apply (rpost_weaken_rule _
      (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ heap_ignore (fset [:: sign_loc]) (s₀, s₁))).
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
      -- intro a.
         (*
         ssprove_code_simpl.
         ssprove_code_simpl_more.
          *)
         destruct a.
         ssprove_sync.
         ssprove_sync.
         ssprove_sync => pk.
         ssprove_sync => sk.
         eapply r_get_remember_rhs => sig.
         eapply r_put_rhs.
         eapply r_get_remember_rhs => sig'.
         eapply r_get_remember_lhs => KG_pk.
         eapply r_ret.
         intuition eauto;
           move:H; do 3! case; move => x; do 2! case; move => h_ignore sign_loc_is_sig set_s1 sign_log_is_sig' _.
         --- repeat f_equal.
             move: sign_log_is_sig'; rewrite /rem_rhs set_s1.
             rewrite get_set_heap_eq.
             intros [=<-].
             rewrite mem_domm.
             rewrite setmE.
             rewrite ifT //=.
             apply/eqP.
             (* FIXME: even this is not correct.
                       the correctness property needs evidence that [(pk,sk) = KeyGen] *)
             exact: Signature_correct_fail.
         --- rewrite set_s1.
             rewrite /heap_ignore => l l_notin_sign_loc.
             specialize (h_ignore l l_notin_sign_loc).
             move: l_notin_sign_loc; rewrite -fset1E in_fset1 => l_neq_sig.
             by rewrite get_set_heap_neq.
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

    Lemma reshape_pair_id {T T0 T1 : Type} (f : T * T0 -> T1) : (fun '(pair x y) => f (pair x y)) = f.
  Proof.
    apply functional_extensionality; by [case].
  Qed.
  (* To DO: Get from RA.v, to import here and in RA.v *)

    Lemma fun_correct:
      prot_result_real ≈₀ prot_result_real'.
    Proof.
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel x.
      all: simplify_linking; ssprove_code_simpl.
      repeat ssprove_sync_eq.
      simplify_linking.
      ssprove_code_simpl.
      rewrite /cast_fun/eq_rect_r/eq_rect.
      simplify_linking.
      ssprove_code_simpl.
      eapply rsame_head_alt_pre.
      - set xxx := fun '(s0,s1) => s0 = s1. 
        rewrite -(reshape_pair_id xxx).
      apply (rpost_weaken_rule _
                       (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ (xxx (s₀, s₁)) )).
        -- eapply r_reflexivity_alt.
        --- instantiate (1:=Key_locs). destruct KeyGen. exact: prog_valid.
        --- move => l.
            rewrite /Key_locs/xxx. 
            unfold Key_locs => l_not_in_Key_locs. (* Why does rewrite fail? *)
            rewrite /get_pre_cond.
            by intros s0 s1 [=->].
        --- intros.
            rewrite /xxx/put_pre_cond.
            by intros s0 s1 [=->].

        -- intro a. 
           intro a1.
           simplify_linking.
           destruct a. destruct a1. intros H. destruct H.
           by split.
        - intros a.

           ssprove_code_simpl.
           ssprove_code_simpl_more.
           destruct a.
           ssprove_sync_eq.
           ssprove_sync_eq.
           ssprove_sync_eq => pk.
           ssprove_sync_eq => sk.
           ssprove_sync_eq => pk2.
           rewrite /tt_.
           rewrite (Signature_correct_fail pk2 sk x) /=.
           apply r_ret => s2 s1 s0_eq_s1 //=.
    Qed.

  End Correctness.

End SignatureProt.


