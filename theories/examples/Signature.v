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

(** |     KEY      |
    |  GENERATION  | **)

Module Type KeyGeneration 
    (π1 : SignatureParams) 
    (π2 : SignatureConstraints).

  Import π1 π2.

   (* currently not used *)
  Parameter KeyGenM: ∀ {L : {fset Location}},
   code L [interface] (SecKey × PubKey).

  Parameter KeyGen : (SecKey × PubKey).

  (*
  The following holds:
  [KeyGen] is just some Coq function. That is, it returns some Coq type. It also states that it is pure.
  [KeyGen_monadic] is a function in the monad of SSProve. That is, it may alter the state. As a result, 
  it cannot be left unspecified when doing a proof!
  We need to specify an implementation in RA and then the weird cast error should disappear.
  That still does not explain the weird error that we see when using the union of sets for locations. 
  Maybe this does not go well with a monadic function used in the code.
  *)

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey      (at level 2): package_scope.
  Notation " 'seckey "    := SecKey      (in custom pack_type at level 2).
  Notation " 'seckey "    := SecKey      (at level 2): package_scope.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).

  Definition key_gen : nat := 1.  (* Routine for initial key generation. *)
  Definition Key_locs := fset [:: pk_loc ; sk_loc]. (* Heap location for the keys. *)

  Definition KeyGen_interface := [interface #val #[key_gen] : 'unit → ('seckey ×'pubkey)].

  Definition Key_Gen : package Key_locs [interface] KeyGen_interface
  := [package
    #def  #[key_gen] (_ : 'unit) : ('seckey ×'pubkey)
    { 
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      ret (sk, pk)
    } 
  ].
  
End KeyGeneration.

(** |  SIGNATURE  |
    |   SCHEME    | **)

Module Type SignatureAlgorithms 
    (π1 : SignatureParams) 
    (π2 : SignatureConstraints) 
    (π3 : KeyGeneration π1 π2).

  Import π1 π2 π3.

  Parameter Sign : ∀ (sk : SecKey) (m : chMessage), Signature.

  Parameter Ver_sig : ∀ (pk : PubKey) (sig : Signature) (m : chMessage), 'bool.

  (* TODO: fmap (Signature * A * A ) -> (Signature * A * A )  triggert endless loop  *)

  (* Final proposition for a signature scheme to be indistinguishable *)
  Parameter Signature_prop:
    ∀ (l: {fmap (Signature  * chMessage ) -> 'unit}) 
      (s : Signature) (pk : PubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).

End SignatureAlgorithms.

Module Type SignaturePrimitives
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (KG : KeyGeneration π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KG).  

  Import π1 π2 KG Alg.

  Notation " 'signature " := Signature   (in custom pack_type at level 2).
  Notation " 'signature " := Signature   (at level 2): package_scope.
  Notation " 'message "   := chMessage     (in custom pack_type at level 2).
  Notation " 'message "   := chMessage     (at level 2): package_scope.

  Definition sign_loc    : Location := ('set ('signature × 'message); 2%N).

  Definition get_pk      : nat := 42. (* routine to get the public key *)
  Definition sign        : nat := 44. (* routine to sign a message *)
  Definition verify_sig  : nat := 45. (* routine to verify the signature *)

  (* The signature scheme requires a heap location to store the seen signatures. *)
  Definition Prim_locs_real := fset [:: pk_loc ; sk_loc].
  Definition Prim_locs_ideal := Prim_locs_real :|: fset [:: sign_loc ]. 

  Definition Prim_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : 'message → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
  ].

  Definition Prim_real : package Prim_locs_real KeyGen_interface Prim_interface
  := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    { 
      #import {sig #[key_gen] : 'unit → ('seckey ×'pubkey) } as key_gen ;;
      '(sk,pk) ← key_gen tt ;;
      pk ← get pk_loc  ;;
      ret pk
    } ;
    #def #[sign] ( 'msg : 'message ) : 'signature
    {
      sk ← get sk_loc  ;;
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

  Equations Prim_ideal : package Prim_locs_ideal KeyGen_interface Prim_interface :=
  Prim_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      #import {sig #[key_gen] : 'unit → ('seckey ×'pubkey) } as key_gen ;;
      '(sk,pk) ← key_gen tt ;;
      pk ← get pk_loc  ;;
      ret pk
    };
    #def #[sign] ( 'msg : 'message ) : 'signature
    {
      sk ← get sk_loc  ;;
      let sig := Sign sk msg in
      S ← get sign_loc ;;
      let S' := setm S (sig, msg) tt in
      #put sign_loc := S' ;;
      ret sig
    };
    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      S ← get sign_loc ;;
      ret ( (sig,msg) \in domm S)
    }
  ].
  Next Obligation.
    ssprove_valid; rewrite /Prim_locs_ideal/Prim_locs_real in_fsetU; apply /orP.
    1,3,4: right;auto_in_fset.
    all: left; auto_in_fset.
  Defined.

  Lemma ext_unforge:
  Prim_real ∘ Key_Gen ≈₀ Prim_ideal ∘ Key_Gen.
  Proof.
    eapply (eq_rel_perf_ind_ignore (fset [:: sign_loc])).
    Check (_ :|: _).
    - rewrite /Prim_locs_real/Prim_locs_ideal/Key_locs/Prim_locs_real.
    apply fsubsetU.
    apply/orP.
    right.
    rewrite !fset_cons.
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

(*

Definition Prim_real : package Prim_locs_real [interface] Prim_interface
Definition Aux : package Aux_locs Prim_interface Att_interface :=

Definition KG : package Prim_locs_real [interface] KeyGen_interface
Definition Prim_real' : package Prim_locs_real KeyGen_interface Prim_interface

left in = right out

Lemma sig_real_vs_att_real:
    Att_real ≈₀ Aux ∘ Prim_real.
  Proof.


*)

(* Old Definitions *)

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

  Equations Prim_ideal : package Prim_locs_ideal [interface] Prim_interface :=
  Prim_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };
    #def #[sign] ( 'msg : 'message ) : 'signature
    {
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let sig := Sign sk msg in
      S ← get sign_loc ;;
      let S' := setm S (sig, msg) tt in
      #put sign_loc := S' ;;
      ret sig
    };
    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      S ← get sign_loc ;;
      ret ( (sig,msg) \in domm S)
    }
  ].
  Next Obligation.
    ssprove_valid; rewrite /Prim_locs_ideal/Prim_locs_real in_fsetU; apply /orP.
    1,4,5: right;auto_in_fset.
    all: left; auto_in_fset.
  Defined.





End SignaturePrimitives.