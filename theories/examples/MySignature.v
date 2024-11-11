(* This practice is for the signature for the paper *)


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

(*From vRATLS Require Import examples.Signature. *)

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.
Variable (n: nat).
Definition pos_n: nat := 2^n.
Definition chSet t := chMap t 'unit.
Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.


(** Extracted from the Signature file **)
(** Parameters **)
Module Type SignatureParams.
  Parameter SecKey PubKey Signature Message Challenge : finType.
End SignatureParams.

(** |     KEY      |
    |  GENERATION  | **)

Module Type KeyGenParams (π1 : SignatureParams).
  Import π1.

  Parameter SecKey_pos : Positive #|SecKey|.
  Parameter PubKey_pos : Positive #|PubKey|.
  Parameter Signature_pos : Positive #|Signature|.
  Parameter Message_pos : Positive #|Message|.
  Parameter Challenge_pos : Positive #|Challenge|.

End KeyGenParams.


Module KeyGenParams_extended (π1 : SignatureParams) (π2 : KeyGenParams π1).
  Import π1 π2.

  #[local] Existing Instance SecKey_pos.
  #[local] Existing Instance PubKey_pos.
  #[local] Existing Instance Signature_pos.
  #[local] Existing Instance Message_pos.
  #[local] Existing Instance Challenge_pos.

  Definition chSecKey    := 'fin #|SecKey|.
  Definition chPubKey    := 'fin #|PubKey|.
  Definition chSignature := 'fin #|Signature|.
  Definition chMessage   := 'fin #|Message|.
  Definition chChallenge := 'fin #|Challenge|.

  Notation " 'pubkey "    := chPubKey (in custom pack_type at level 2).
  Notation " 'pubkey "    := chPubKey (at level 2): package_scope.
  Notation " 'seckey "    := chSecKey (in custom pack_type at level 2).
  Notation " 'seckey "    := chSecKey (at level 2): package_scope.

  Definition pk_loc : Location := ('pubkey ; 0%N).
  Definition sk_loc : Location := ('seckey ; 1%N).

  Definition key_gen : nat := 2.  (* Routine for initial key generation. *)
  Definition apply   : nat := 3.


  Definition Key_locs := fset [:: pk_loc ; sk_loc].

End KeyGenParams_extended.

Module Type KeyGen_code (π1 : SignatureParams) (π2 : KeyGenParams π1).
  Import π1 π2.
  Module KGP := KeyGenParams_extended π1 π2.
  Import KGP.

  Parameter KeyGen :
      code Key_locs [interface] (chPubKey × chSecKey).

End KeyGen_code.

Module KeyGen
  (π1 : SignatureParams)
  (π2 : KeyGenParams π1)
  (π3 : KeyGen_code π1 π2).

  Import π1 π2 π3.
  Import π3.KGP.

  Definition KeyGen_ifce := [interface
    #val #[key_gen] : 'unit → ('seckey × 'pubkey)
  ].

  Definition Key_Gen : package Key_locs [interface] KeyGen_ifce
  := [package
      #def  #[key_gen] (_ : 'unit) : ('seckey × 'pubkey)
      {
        '(pk, sk) ← KeyGen ;;
        #put sk_loc := sk ;;
        #put pk_loc := pk ;;
        ret (sk, pk)
      }
    ].

End KeyGen.

(** |  SIGNATURE  |
    |   SCHEME    | **)

    Module Type SignatureAlgorithms
    (π1 : SignatureParams)
    (π2 : KeyGenParams π1)
    (π3 : KeyGen_code π1 π2).

  Import π3 π3.KGP.

  (*Parameter KeyGen : (chSecKey × chPubKey). *)


  Parameter Sign : ∀ (sk : chSecKey) (m : chMessage), chSignature.

  Parameter Ver_sig : ∀ (pk :  chPubKey) (sig : chSignature) (m : chMessage),
   'bool.

  (* Functional correctness property for signatures *)
  Parameter Signature_correct : ∀ pk sk msg seed,
    Some (pk,sk) = Run sampler KeyGen_code seed ->
    Ver_sig pk (Sign sk msg) msg == true.

End SignatureAlgorithms.






(*****************************************************)
(** Extracted from the Signature file **)
(** Parameters **)
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


(** Constraints **)
Module Type SignatureConstraints.
  Definition chMessage : choice_type := 'fin (mkpos pos_n).
End SignatureConstraints.


(** KeyGen **)
Module Type KeyGeneration
    (π1 : SignatureParams)
    (π2 : SignatureConstraints).
  Import π1 π2.

  Notation " 'pubkey "    := PubKey (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey (at level 2): package_scope.
  Notation " 'seckey "    := SecKey (in custom pack_type at level 2).
  Notation " 'seckey "    := SecKey (at level 2): package_scope.

 (* Parameter KeyGen : (SecKey × PubKey). *)

  Definition pk_loc : Location := ('pubkey ; 0%N).
  Definition sk_loc : Location := ('seckey ; 1%N).

  (*
  Definition key_gen : nat := 2.  (* Routine for initial key generation. *)
  Definition apply   : nat := 3.
  *)

  Definition Key_locs := fset [:: pk_loc ; sk_loc].

  (* Define KeyGen_code as a sampler *)
  

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


(** SIGNATURE   SCHEME    **)
Module Type SignatureAlgorithms
    (π1 : SignatureParams)
    (π2 : SignatureConstraints)
    (π3 : KeyGeneration π1 π2).

  Import π1 π2 π3.

  (*Parameter Kgen : ∀ (pk: PubKey)  (sk: SecKey), pair. *)
  (*Parameter KGen : ∀ (l : nat), ((pk: PubKey) * (sk: SecKey)). *)
  Parameter KeyGen : (SecKey × PubKey).
  Parameter Sign : ∀ (sk : SecKey) (m : chMessage), Signature.
(*Parameter Ver_sig : ∀ (pk :  PubKey) (m : chMessage)  (sig : Signature), 'bool.*)
  Parameter Ver_sig : ∀ (pk :  PubKey) (sig : Signature) (m : chMessage), 'bool.


  (* Final proposition for a signature scheme to be indistinguishable *)
  Parameter Signature_prop:
    ∀ (l: {fmap (Signature  * chMessage ) -> 'unit})
      (s : Signature) (pk : PubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).

  (* Functional correctness property for signatures *)
  (*** It ensures that a signature generated by signing algo can be successfully verified
  by the veri algo using the corresponding pk. ***)
  Parameter Signature_correc0: 
  forall pk sk msg, Ver_sig pk (Sign sk msg) msg == true.

    (** Something from RSA.v
    Theorem Signature_prop:
    ∀ (l: {fmap (chSignature  * chMessage ) -> 'unit})
      (s : chSignature) (pk : chPubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).
---------------------------------------------------------------
      Theorem Signature_prop':
    ∀ (l: {fmap (chSignature  * chMessage ) -> 'unit})
      (pk : chPubKey)
      (sk : chSecKey)
      (m  : chMessage),
      Ver_sig pk (Sign sk m) m = ((Sign sk m, m) \in domm l).
  **)

(*******
Usually correctness means that for any valid key pair (pk, sk), and any msg m,
the verification of the signature should succeed?
So, 
Module type SignatureScheme := {
  KeyGen : Comp (publicKey * privateKey);
  Sign : privateKey -> message -> Comp signature;
  VerSig : publicKey -> message -> signature -> bool
}.
Module signature_correct (ss : SignatureScheme) : Prop :=
  forall (pk : publicKey) (sk : privateKey) (m : message),
    let (pk, sk) := KeyGen ss in
    Pr[VerSig ss pk m (Sign ss sk m)] = 1.
*********)
  Parameter Signature_correct2 :
  forall (pk : PubKey) (sk : SecKey) (msg : chMessage),
  Ver_sig pk (Sign sk msg) msg = true.

  Parameter Signature_correct3 : 
  forall (msg : chMessage),
  let (pk, sk) := KeyGen in 
  Ver_sig pk (Sign sk msg) msg = true.

  Parameter Signature_correct:
  forall (pk : PubKey) (sk : SecKey) (msg : chMessage),
  let (pk, sk) := KeyGen in 
  Ver_sig pk (Sign sk msg) msg = true.

  Theorem Signature_correctness pk sk msg seed :
    Some (sk, pk) = Run sampler KeyGen seed ->
    Ver_sig pk (Sign sk msg) msg = true. 


  (*Axiom correctness :
  forall (pk : PubKey) (sk : SecKey) (msg : chMessage), 
  (pk, sk) = KGen ->
  Ver_sig pk (Sign sk msg) msg = true. *)



End SignatureAlgorithms.


(** Signature Paramatives **)
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



Module SignatureProt
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (KG : KeyGeneration π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KG)
  (Prim : SignaturePrimitives π1 π2 KG Alg).

  Import π1 π2 KG Alg Prim.

  Definition protocol := 30.
  Definition Sig_prot_ifce :=
    [interface #val #[protocol] : 'message → 'pubkey × ('signature × 'bool) ]. Print Sig_prot_ifce. Print opsig.

  Definition Sig_prot : 
  package 
  Sig_locs_real 
  Sig_ifce 
  Sig_prot_ifce
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
      apply fsubsetxx. Print fsubsetxx.
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

