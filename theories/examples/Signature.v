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

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
 *)
Definition chSet t := chMap t 'unit.
Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Module Type SignatureParams.

    Parameter fSecKey : finType.
    Parameter SecKey_pos : Positive #|fSecKey|.
    #[local] Existing Instance SecKey_pos.
    Definition SecKey := 'fin #|fSecKey|.
    Definition i_sk := #|fSecKey|.
    Lemma pos_i_sk : Positive i_sk.
    Proof.
    rewrite /i_sk. apply SecKey_pos.
    Qed.

    Definition PubKey := SecKey.
    Definition Signature : choice_type := chFin(mkpos pos_n).
    (*
    Definition SecKey    : choice_type := chFin(mkpos pos_n).
    Definition PubKey    : choice_type := chFin(mkpos pos_n).
    *)

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

  Notation " 'pubkey "    := PubKey (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey (at level 2): package_scope.
  Notation " 'seckey "    := SecKey (in custom pack_type at level 2).
  Notation " 'seckey "    := SecKey (at level 2): package_scope.

  Parameter KeyGen : (SecKey × PubKey).

  Definition pk_loc : Location := ('pubkey ; 0%N).
  Definition sk_loc : Location := ('seckey ; 1%N).

  Definition key_gen : nat := 2.  (* Routine for initial key generation. *)
  Definition apply   : nat := 3.
  Definition Key_locs := fset [:: pk_loc ; sk_loc].

  (*
  "failed attempt to define apply function as enclave
  for secret key"

  Context (T : choice_type).
  Notation " 't " := T (in custom pack_type at level 2).
  Notation " 't " := T (at level 2): package_scope.

  Context (L : {fset Location}).
  Definition M L T := code L [interface] T.
  Notation " 'm " := M (in custom pack_type at level 2).
  Notation " 'm " := M (at level 2): package_scope.

  Definition Apply := mkopsig apply ('m L 'seckey) ('m L T).

  Definition KeyGen_ifce T := fset (cons
    (*(pair key_gen (pair 'unit 'pubkey)) *)

    (pair apply (pair Apply T))
    (*#val #[apply] : ('m L 'seckey → 'm L 't) → 't *)
  nil).
  *)

  Definition KeyGen_ifce := [interface
    #val #[key_gen] : 'unit → ('seckey × 'pubkey)
  ].

  Definition Key_Gen : package Key_locs [interface] KeyGen_ifce
  := [package
       #def  #[key_gen] (_ : 'unit) : ('seckey × 'pubkey)
       {
         let (sk, pk) := KeyGen in
         #put sk_loc := sk ;;
         #put pk_loc := pk ;;

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

  Parameter Ver_sig : ∀ (pk :  PubKey) (sig : Signature) (m : chMessage),
   'bool.

  (* TODO: fmap (Signature * A * A ) -> (Signature * A * A )  triggert endless loop  *)

  (* Final proposition for a signature scheme to be indistinguishable *)
  Parameter Signature_prop:
    ∀ (l: {fmap (Signature  * chMessage ) -> 'unit})
      (s : Signature) (pk : PubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).

  (* Functional correctness property for signatures *)
  Parameter Signature_correct: forall pk sk msg, Ver_sig pk (Sign sk msg) msg == true.

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

  Definition sign_loc : Location := ('set ('signature × 'message); 4%N).

  Definition get_pk     : nat := 5. (* routine to get the public key *)
  Definition sign       : nat := 6. (* routine to sign a message *)
  Definition verify_sig : nat := 7. (* routine to verify the signature *)
  Definition init       : nat := 8. (* routine to initialize the keys *)

  (* The signature scheme requires a heap location to store the seen signatures. *)
  Definition Sig_locs_real := Key_locs.
  Definition Sig_locs_ideal := Sig_locs_real :|: fset [:: sign_loc ].

  Definition Sig_ifce := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : 'message → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
  ].

  Definition Sig_real : package Sig_locs_real KeyGen_ifce Sig_ifce
  := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      #import {sig #[key_gen] : 'unit → ('seckey × 'pubkey) } as key_gen ;;
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

  Equations Sig_ideal : package Sig_locs_ideal KeyGen_ifce Sig_ifce :=
  Sig_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      #import {sig #[key_gen] : 'unit → ('seckey × 'pubkey) } as key_gen ;;
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
    ssprove_valid; rewrite /Sig_locs_ideal/Sig_locs_real in_fsetU; apply /orP.
    1,3,4: right;auto_in_fset.
    all: left; auto_in_fset.
  Defined.

  Equations Sig_real_c : package Sig_locs_real [interface] Sig_ifce :=
    Sig_real_c := {package Sig_real ∘ Key_Gen}.
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
  Qed.

  Equations Sig_ideal_c : package Sig_locs_ideal [interface] Sig_ifce :=
    Sig_ideal_c := {package Sig_ideal ∘ Key_Gen}.
  Next Obligation.
    ssprove_valid.
    - rewrite /Sig_locs_ideal/Sig_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
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
  Qed.

  Lemma ext_unforge:
  Sig_real_c ≈₀ Sig_ideal_c.
  Proof.
    eapply (eq_rel_perf_ind_ignore (fset [:: sign_loc])).
    - rewrite /Sig_locs_real/Sig_locs_ideal/Key_locs/Sig_locs_real/Key_locs.
      apply fsubsetU.
      apply/orP; right.
      apply fsubsetU.
      apply/orP; right.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    - simplify_eq_rel x.
    -- simplify_linking.
       ssprove_sync.
       ssprove_sync.
       ssprove_sync => pk_loc.
       eapply r_ret.
       intuition eauto.
    -- repeat ssprove_sync.
       intros.
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

End SignaturePrimitives.
