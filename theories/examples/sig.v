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

Module Type SignatureAlgorithms 
  (π1 : SignatureParams) 
  (π2 : SignatureConstraints).

  Import π1 π2.

  (**********************)
  (***** Primitives *****)
  (**********************)

  Parameter KeyGen : (SecKey × PubKey).
  Parameter Sign : ∀ (sk : SecKey) (m : chMessage), Signature.
  Parameter Ver_sig : ∀ (pk : PubKey) (sig : Signature) (m : chMessage), 'bool.

  (* Final proposition for a signature scheme to be indistinguishable *)
  Parameter Signature_prop:
    ∀ (l: {fmap (Signature  * chMessage ) -> 'unit}) 
    (s : Signature) (pk : PubKey) (m  : chMessage),
    Ver_sig pk s m = ((s,m) \in domm l).

End SignatureAlgorithms.

Module Type SignaturePrimitives
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (Alg : SignatureAlgorithms π1 π2).

  Import π1.
  Import π2.
  Import Alg.

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey      (at level 2): package_scope.
  Notation " 'seckey "    := SecKey      (in custom pack_type at level 2).
  Notation " 'seckey "    := SecKey      (at level 2): package_scope.
  Notation " 'signature " := Signature   (in custom pack_type at level 2).
  Notation " 'signature " := Signature   (at level 2): package_scope.
  Notation " 'message "   := chMessage     (in custom pack_type at level 2).
  Notation " 'message "   := chMessage     (at level 2): package_scope.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition sign_loc    : Location := ('set ('signature × 'message); 2%N).
  Definition init        : nat := 1.  (* routine for key initialization *)
  Definition get_pk      : nat := 42. (* routine to get the public key *)
  Definition sign        : nat := 44. (* routine to sign a message *)
  Definition verify_sig  : nat := 45. (* routine to verify the signature *)

  Definition Prim_locs_real := fset [:: pk_loc ; sk_loc].
  Definition Prim_locs_ideal := fset [:: pk_loc ; sk_loc ; sign_loc].

  Definition Prim_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : 'message → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
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

  
  Definition Signature_locs_real := Prim_locs_real.
  Definition Signature_locs_ideal := Prim_locs_ideal.

  Definition Sig_interface := 
    [interface #val #[sign] : 'message → 'pubkey × ('signature × 'bool) ].

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
  
    Equations Sig_ideal : package Signature_locs_ideal Prim_interface 
      Sig_interface :=
    Sig_ideal := [package
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
         --- eapply r_ret => s0 s1 pre //=.
         -- case x => s m.
            eapply r_get_remember_lhs => pk.
            eapply r_get_remember_rhs => S.
            eapply r_ret => s0 s1 pre //=.
            split.
         ---- eapply Signature_prop.
         ---- by [move: pre; rewrite /inv_conj; repeat case].
  Qed.
   
End SignatureProt.