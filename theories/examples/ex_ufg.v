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

Require Import examples.Signature.

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.
Variable (n: nat).
Definition pos_n: nat := 2^n.
Definition chSet t := chMap t 'unit.
Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Module Type ExistentialUnforgeability
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (Alg : SignatureAlgorithms π1 π2)
  (Prim : SignaturePrimitives π1 π2 Alg).

  Import π1.
  Import π2.
  Import Alg.
  Import Prim.  

  (* 
  Why is this Lemma sufficient? 
  According to "The Joy of Crypto", we show that the real and fake primitives are
  indistinguishable, which then implies " By asking for the libraries to be 
  indistinguishable, we are reallyasking that the attacker cannot find any such 
  message-signature pair (forgery)." Hence, we prove the scheme to be strong
  unforgeable.
  *)    

  Lemma ext_unforge:
      Prim_real ≈₀ Prim_ideal.
  Proof.
  eapply (eq_rel_perf_ind_ignore (fset [:: sign_loc])).
  - rewrite /Prim_locs_real/Prim_locs_ideal.
    apply fsubsetU.
    apply/orP.
    right.
    rewrite !fset_cons.
    apply fsubsetU ; apply /orP ; right.
    apply fsubsetU ; apply /orP ; right.    
    apply fsetUS.
    apply fsubsetxx.
  - simplify_eq_rel x.
    -- ssprove_sync => pk. 
       eapply r_ret.
       intuition eauto.
    -- repeat ssprove_sync.
       eapply r_get_remember_rhs => sign_loc.
       eapply r_put_rhs.
       ssprove_restore_mem.
       --- ssprove_invariant.
       ---  eapply r_ret => s0 s1 pre //=.
    -- case x => s m.
       eapply r_get_remember_lhs => pk.
       eapply r_get_remember_rhs => S.
       eapply r_ret => s0 s1 pre //=.
       split.
       ---- eapply Signature_prop.
       ---- by [move: pre; rewrite /inv_conj; repeat case].
    Qed.

End ExistentialUnforgeability.