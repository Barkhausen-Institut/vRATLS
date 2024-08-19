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


Print Run_aux.

(* TODO new run function needed: [evalState] *)
Fail Theorem CEO seed :
  forall pk sk,
    Some (pk,sk) = Run sampler KeyGen seed ->
    forall msg sig,
      Some sig = Run_aux sampler (Sign msg) (λ l, if l == sk_loc then Some sk else Some NSUnit) ->
      forall pk',
        Some true = Run_aux sampler (Verify sig msg) (λ l, if l == pk_loc then Some pk' else Some NSUnit) ->
        pk = pk'.

Fail Definition Sign_me : package Sig_locs_real Sig_ifce Sig_prot_ifce
  := [package
        #def  #[sign_me] (msg : 'message) : 'pubkey × 'signature
        {
           #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
           #import {sig #[sign] : 'message → 'signature  } as sign ;;

           pk ← get_pk tt ;;
           sig ← sign msg ;;

           ret (pk, sig)
        }
  ].

Fail Definition Verify_me : package Sig_locs_real Sig_ifce Sig_prot_ifce
  := [package
        #def  #[verify_me] (sig : 'signature) (msg : 'message) : 'pubkey × 'bool
        {
           #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
           #import {sig #[sign] : 'message → 'signature  } as sign ;;

           pk ← get_pk tt ;;
           b ← verify msg sig ;;
           ret (pk, b)
        }
  ].


Fail Theorem CEO seed seed':
  forall pk pk' msg sig,
    Some (pk , sig ) = Run sampler (Sign_me msg)       seed ->
    Some (pk', true) = Run sampler (Verify_me sig msg) seed ->
    pk = pk'.

(* The below version holds for [KeyGen] implementations
   that dependent on the seed.
   That is, we need an additional property for [KeyGen]:
   [
     Some pk  = Run sampler KeyGen seed  ->
     Some pk' = Run sampler KeyGen seed' ->
     seed = seed' ->
     pk = pk'
   ]
 *)
Fail Theorem CEO' seed seed':
  forall pk pk' msg sig,
    Some (pk , sig ) = Run sampler (Sign_me msg)       seed  ->
    Some (pk', true) = Run sampler (Verify_me sig msg) seed' ->
    pk = pk' ->
    seed = seed'.
(*
  The proof is by case on [seed == seed'].
  The [true] case is straight-forward.
  The [false] case leads to a contradiction in the hypotheses because
  then [pk = pk'] does not hold anymore.
 *)


Fail Theorem DEO seed seed':
  forall pk pk' msg msg' sig,
    Some (pk, sig ) = Run sampler (Sign_me msg)        seed  ->
    Some (pk, true) = Run sampler (Verify_me sig msg') seed' ->
    seed != seed' ->
    pk = pk' ∧ msg = msg'.

Theorem Consistency_verify:
  forall pk seed sig msg r r',
    Some (pk, r ) = Run sampler (Verify_me sig msg) seed' ->
    Some (pk, r') = Run sampler (Verify_me sig msg) seed' ->
    r = r'.
