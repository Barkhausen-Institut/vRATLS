From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From extra Require Import rsa.

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

From vRATLS Require Import Signature.

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.

Module Type RSA_Key_Gen_params.

  (* currently useless *)
  Parameter Z_n : finType.
  Parameter Z_n_pos : Positive #|Z_n|.
  #[local] Existing Instance Z_n_pos.
  Definition chZ_n := 'fin #|Z_n|.
  Definition i_Z_n := #|Z_n|.

End RSA_Key_Gen_params.

Module Type RSA 
    (π1 : SignatureParams) 
    (π2 : SignatureConstraints) 
    (π3 : KeyGeneration π1 π2)
    (π4 : RSA_Key_Gen_params).

  Import π1 π2 π3 π4.

  Module rsa_alg <: SignatureAlgorithms.

  

  Definition sk := e.

  Definition Sign : ∀ (sk : SecKey) (m : chMessage), Signature :=
    encrypt (Hash m) sk.

  Parameter Ver_sig : ∀ (pk :  PubKey) (sig : Signature) (m : chMessage), 
   'bool.

  (* TODO: fmap (Signature * A * A ) -> (Signature * A * A )  triggert endless loop  *)

  (* Final proposition for a signature scheme to be indistinguishable *)
  Parameter Signature_prop:
    ∀ (l: {fmap (Signature  * chMessage ) -> 'unit}) 
      (s : Signature) (pk : PubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).

  End rsa_alg.

  

  (*
  Definition SecKey' := Datatypes_prod__canonical__choice_Choice.
  Definition PubKey' := Datatypes_prod__canonical__choice_Choice.

  Notation " 'pubkey2 "    := PubKey' (in custom pack_type at level 2).
  Notation " 'pubkey2 "    := PubKey' (at level 2): package_scope.
  Notation " 'seckey2 "    := SecKey' (in custom pack_type at level 2).
  Notation " 'seckey2 "    := SecKey' (at level 2): package_scope.

  Definition Key_Gen_rsa : package Key_locs [interface] KeyGen_ifce
    := [package
        #def  #[key_gen] (_ : 'unit) : ('seckey × 'pubkey)
        { 
            p ← sample uniform i_sk ;;
            q ← sample uniform i_sk ;;
            #assert (prime p == true) ;;
            #assert (prime q) ;;
            ret (p,q)
        }
      ].
  *)

  Definition SecKey' :choice_type := nat.
  Definition PubKey' := nat.

  Notation " 'pubkey2 "    := PubKey' (in custom pack_type at level 2).
  Notation " 'pubkey2 "    := PubKey' (at level 2): package_scope.
  Notation " 'seckey2 "    := SecKey' (in custom pack_type at level 2).
  Notation " 'seckey2 "    := SecKey' (at level 2): package_scope.

  Definition Key_Gen_rsa : package Key_locs [interface] KeyGen_ifce
  := [package
      #def  #[key_gen] (_ : 'unit) : ('seckey × 'pubkey)
      {           
        ret (d,e)
      }
    ].

End