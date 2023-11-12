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

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.

Variable (n: nat).
Definition pos_n: nat := 2^n.

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
 *)
Definition chSet t := chMap t 'unit.
Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Module Type SignatureParams.

    Definition SecKey : choice_type := chFin(mkpos pos_n).
    Definition PubKey : choice_type := chFin(mkpos pos_n).
    Definition Signature : choice_type := chFin(mkpos pos_n).

End SignatureParams.

Module Type SignatureConstraints.
  Definition chMessage : choice_type := 'fin (mkpos pos_n).
End SignatureConstraints.

(** |  SIGNATURE  |
    |   SCHEME    | **)

Module Type SignatureAlgorithms (π1 : SignatureParams) (π2 : SignatureConstraints).

  Import π1 π2.
  
  (* currently not used *)
  Parameter KeyGen_monadic : ∀ {L : {fset Location}},
     code L [interface] (SecKey × PubKey).

  Parameter KeyGen : (SecKey × PubKey).

(*
The following holds:
[KeyGen] is just some Coq function. That is, it returns some Coq type. It also states that it is pure.
[KeyGen_monadic] is a function in the monad of SSProve. That is, it may alter the state. As a result, it cannot be left unspecified when doing a proof!
We need to specify an implementation in RA and then the weird cast error should disappear.
That still does not explain the weird error that we see when using the union of sets for locations. Maybe this does not go well with a monadic function used in the code.
*)

  Parameter Sign : ∀ (sk : SecKey) (m : chMessage), Signature.

  Parameter Ver_sig : ∀ (pk : PubKey) (sig : Signature) (m : chMessage), 'bool.

End SignatureAlgorithms.

Module Type SignaturePrimitives
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (Alg : SignatureAlgorithms π1 π2).

  Import π1.
  Import π2.
  Import Alg.

  (* #[local] Open Scope package_scope. *)

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey      (at level 2): package_scope.
  Notation " 'signature " := Signature   (in custom pack_type at level 2).
  Notation " 'signature " := Signature   (at level 2): package_scope.
  Notation " 'message "   := chMessage     (in custom pack_type at level 2).
  Notation " 'message "   := chMessage     (at level 2): package_scope.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition sign_loc    : Location := ('set ('signature × 'message); 2%N).

  Definition get_pk      : nat := 42. (* routine to get the public key *)
  Definition sign        : nat := 44. (* routine to sign a message *)
  Definition verify_sig  : nat := 45. (* routine to verify the signature *)
  Definition sign_f      : nat := 46. (* routine to sign a message *)
  Definition verify_sig_f: nat := 47. (* routine to verify the signature *)

  (* The signature scheme requires a heap location to store the seen signatures. *)
  Definition Prim_locs_real := fset [:: pk_loc ; sk_loc].
  Definition Prim_locs_ideal := fset [:: pk_loc ; sk_loc ; sign_loc].
  (*
  Definition Prim_locs_ideal := Prim_locs_real :|: fset [:: sign_loc ].
  *) 

  Definition Prim_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : 'message → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
  ].

  Definition Prim_interface_f := [interface
  #val #[get_pk] : 'unit → 'pubkey ;
  #val #[sign_f] : 'message → 'signature ;
  #val #[verify_sig_f] : ('signature × 'message) → 'bool
].

  Definition Prim_real : package Prim_locs_real [interface] Prim_interface
  := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    } ;

    #def #[sign] ( 'msg : 'message ) : 'signature
    {
      let (sk,pk) := KeyGen in
      (*
      '(sk,pk) ← KeyGen ;;
      *)
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let sig := Sign sk msg in
      ret sig
    };

    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      pk ← get pk_loc  ;;
      let bool := Ver_sig pk sig msg in
      ret bool
    }
  ].

  Equations Prim_ideal : package Prim_locs_ideal [interface] Prim_interface_f :=
  Prim_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };

    #def #[sign_f] ( 'msg : 'message ) : 'signature
    {
    let (sk,pk) := KeyGen in
    (*
    '(sk,pk) ← KeyGen ;;
    *)
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let sig := Sign sk msg in
      S ← get sign_loc ;;
      let S' := setm S (sig, msg) tt in
      #put sign_loc := S' ;;
      ret sig
    };

    #def #[verify_sig_f] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      S ← get sign_loc ;;
      ret ( (sig,msg) \in domm S)
    }
  ].
  (*
  Next Obligation.
    ssprove_valid; rewrite /Prim_locs_ideal/Prim_locs_real in_fsetU; apply /orP.
    2,3,6: left;auto_in_fset.
    all: right; auto_in_fset.
  Defined.
  *)


End SignaturePrimitives.

Module Type SignatureProt
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (Alg : SignatureAlgorithms π1 π2)
  (Prim : SignaturePrimitives π1 π2 Alg).

  Import π1.
  Import π2.
  Import Alg.
  Import Prim.
  (* NEW VERSION *)

  Definition Signature_locs_real := Prim_locs_real.
  Definition Signature_locs_ideal := Prim_locs_ideal.

  Definition Sig_interface := 
    [interface #val #[sign] : 'message → 'pubkey × ('signature × 'bool) ].

(* pure definition relying on primitives *)

  Definition Sig_real : package Signature_locs_real 
    Prim_interface Sig_interface
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
  
    Equations Sig_ideal : package Signature_locs_ideal Prim_interface_f 
      Sig_interface :=
    Sig_ideal := [package
      #def  #[sign] (msg : 'message) : 'pubkey × ('signature × 'bool)
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
        #import {sig #[sign_f] : 'message → 'signature  } as sign ;;
        #import {sig #[verify_sig_f] : ('signature × 'message) → 'bool } as verify_sig ;;
        (* Protocol *)
        pk ← get_pk tt ;;
        sig ← sign msg ;;
        bool ← verify_sig (sig, msg) ;;
        ret (pk, ( sig, bool ))
      } 
    ].



End SignatureProt.

  (* 
  Currently not needed
  Semi-old version, 50:50 prims and protocol 
  *)


  (*

  Definition Sig_real2 : package Signature_locs_real Prim_interface Sig_interface
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

  Equations Sig_ideal2 : package Signature_locs_ideal Prim_interface_f Sig_interface :=
  Sig_ideal2 := [package
    #def  #[sign] (msg : 'message) : 'pubkey × ('signature × 'bool)
    {
      #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
      #import {sig #[sign_f] : 'message → 'signature  } as sign ;;
      #import {sig #[verify_sig_f] : ('signature × 'message) → 'bool } as verify_sig ;;
      (* Protocol *)
      pk ← get_pk tt ;;
      sig ← sign msg ;;
      S ← get sign_loc ;;
      let S' := setm S (sig, msg) tt in
      #put sign_loc := S' ;;   
      let bool := ( (sig,msg) \in domm S) in
      ret (pk, ( sig, bool ))
    } 
  ].

*)
 (* 
 Next Obligation.
 ssprove_valid; rewrite /Signature_locs_ideal/Signature_locs_real in_fsetU; apply /orP.
    all: right; auto_in_fset.
  Defined.  
  *)

