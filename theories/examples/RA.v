

(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.
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

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

(** REMOTE ATTESTATION
    VERIFIER                             PROVER
Generates a chal-
  lenge 'chal'
                   -----chal----->    
                                       Attestation
                                       (using TPM) 
                   <-----res------
Validity check
  of proof
** ATTESTATION
Input: 'chal'
--------------
TPM generates 'quoted' information
sig = Sign(chal,key,quoted)
--------------
Output: '(sig,quoted)'
**)

(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.
*)

Module Type SignatureParams.

    Variable (n: nat). 
    Definition pos_n: nat := 2^n.
    Definition SecKey : choice_type := chFin(mkpos pos_n).
    Definition PubKey : choice_type := chFin(mkpos pos_n).
    Definition State : choice_type := chFin(mkpos pos_n).
    Definition Challenge : choice_type := chFin(mkpos pos_n).
    Definition Attestation : choice_type := chFin(mkpos pos_n).
    Definition Message : choice_type := chFin(mkpos pos_n).
    Definition Signature : choice_type := chFin(mkpos pos_n).
    Definition Seed : choice_type := chFin(mkpos pos_n).

    Parameter Challenge_pos : Positive #|Challenge|.

End SignatureParams.
  
(** |  SIGNATURE  |
    |   SCHEME    | **)

Module Type SignatureAlgorithms (π : SignatureParams).
  
  Import π.
  
  #[local] Open Scope package_scope.

(* Key Generation *)
  Parameter KeyGen :
  ∀ {L : {fset Location}} (sd : Seed),
    code L [interface] (SecKey × PubKey).

  Parameter KeyGen2 : ∀ (sd : Seed), (SecKey × PubKey).

  (* Siganture algorithm *)
  Parameter Sign :
  ∀ {L : {fset Location}} (sk : SecKey) (m : Message),
    code L [interface] Signature.

  (* Verification algorithm *)
  Parameter Ver_sig :
  ∀ {L : {fset Location}} (pk : PubKey) (sig : Signature) (m : Message),
    code L [interface] 'bool.

    Parameter Attest :
    ∀ {L : {fset Location}} (sk : SecKey) ( c : Challenge ) (s : State),
       code L [interface] Signature.
     
  (* Decryption algorithm *)
  Parameter Ver_att :
    ∀ {L : {fset Location}} (pk : PubKey) (att : Attestation)
                   ( c : Challenge) ( s : State),
       code L [interface] 'bool.

  Parameter Hash :
    	State -> Challenge ->
      Message.

  Parameter Hash_refl : 
    forall s1 c1 , Hash s1 c1 = Hash s1 c1.

  Parameter Hash_bij :
    forall s1 c1 s2 c2, s1 != s2 \/ c1 != c2  -> Hash s1 c1 != Hash s2 c2.
    
End SignatureAlgorithms.

Module RemoteAttestation (π : SignatureParams)
  (Alg : SignatureAlgorithms π).

  Import π.
  Import Alg.

  #[local] Open Scope package_scope.

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey      (at level 2): package_scope.
  Notation " 'signature " := Signature   (in custom pack_type at level 2).
  Notation " 'signature " := Signature   (at level 2): package_scope.
  Notation " 'state "     := State       (in custom pack_type at level 2).
  Notation " 'state "     := State       (at level 2): package_scope.
  Notation " 'challenge " := Challenge   (in custom pack_type at level 2).
  Notation " 'challenge " := Challenge   (at level 2): package_scope.
  Notation " 'message "   := Message     (in custom pack_type at level 2).
  Notation " 'message "   := Message     (at level 2): package_scope.  
  Notation " 'seed "      := Seed        (in custom pack_type at level 2).
  Notation " 'seed "      := Seed        (at level 2): package_scope.
  Notation " 'att "       := Attestation (in custom pack_type at level 2).
  Notation " 'att "       := Attestation (at level 2): package_scope.

  (**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
  *)
  Definition chSet t := chMap t 'unit.
  Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
  Notation " 'set t " := (chSet t) (at level 2): package_scope.

  Definition tt := Datatypes.tt.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition message_loc : Location := (Message   ; 2%N).   
  Definition sign_loc    : Location := ('set ('signature × 'message); 3%N).
  Definition state_loc   : Location := (State    ; 4%N).
  Definition chal_loc    : Location := (Challenge ; 5%N).
  Definition attest_loc  : Location := ('set ('challenge × 'state × 'att ) ; 6%N).

  Definition get_pk    : nat := 42. (* routine to get the public key *)
  Definition get_state : nat := 43. (* routine to get the state to be attested *)
  Definition sign      : nat := 44. (* routine to sign a message *)
  Definition verify_sig: nat := 45. (* routine to verify the signature *)
  Definition verify_att: nat := 46.

  Definition Signature_locs := fset [:: pk_loc ; sk_loc ; sign_loc ].

  Notation " 'attest "    := Attestation    (in custom pack_type at level 2).  
  Definition attest    : nat := 47. (* routine to attest *)  

  Definition Attestation_locs := fset [:: pk_loc ; sk_loc; attest_loc ].
  
  Definition Sign_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : ('message × 'seed) → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
  ].

  Definition Att_interface := [interface
  #val #[get_pk] : 'unit → 'pubkey ;
  #val #[attest] : ('challenge × ('state × 'seed)) → 'signature ;
  #val #[verify_att] : ( ('challenge × 'state) × 'signature) → 'bool
  ].

  Definition Sig_real :
  package Signature_locs
    [interface]
    Sign_interface
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    } ;

    #def #[sign] ( '(msg,sd) : 'message × 'seed) : 'signature
    {
      (*'(sk, pk) ← KeyGen2 sd ;;*)
      let (sk,pk) := KeyGen2 sd in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      sig ← Sign sk msg ;;
      (*#put sign_loc := ( sig , msg ) ;; *)
      ret sig 
    };
    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      pk ← get pk_loc  ;;
      bool ← Ver_sig pk sig msg ;;
      ret bool
    }
  ].

  Definition Sig_ideal :
  package Signature_locs
    [interface]
    Sign_interface
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;
    #def #[sign] ( '(msg,sd) : 'message × 'seed) : 'signature
    {
      (*'(sk, pk) ← KeyGen2 sd ;;*)
      let (sk,pk) := KeyGen2 sd in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;      
      sig ← Sign sk msg ;; 
      S ← get sign_loc ;; 
      #put sign_loc := setm S (sig, msg) tt ;;
      ret sig
    };
    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      S ← get sign_loc ;;
      ret ( (sig,msg) \in domm S)      
    }
  ].

  Definition ɛ_sig A := AdvantageE Sig_real Sig_ideal A. 

  Definition i_challenge := #|Challenge|.
  Definition i_challenge_pos : Positive i_challenge.
  Proof.
    unfold i_challenge.
    apply Challenge_pos.
  Qed.

  Definition Aux :
  package (fset [:: sign_loc ; pk_loc ; attest_loc ])
  [interface
  #val #[get_pk] : 'unit → 'pubkey ;
  #val #[sign] : ('message × 'seed)  → 'signature ;
  #val #[verify_sig] : ('signature × 'message) → 'bool
  ]
  [interface
  #val #[get_pk] : 'unit → 'pubkey ;
  #val #[attest] : ('challenge × ('state × 'seed)) → 'signature ;
  #val #[verify_att] : ( ('challenge × 'state) × 'signature) → 'bool
  ]
  :=
  [package
    #def #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;
    #def #[attest] ( '(chal,(state,sd)) : ('challenge × ('state × 'seed))) : 'signature
    {
      #import {sig #[sign] : ('message  × 'seed) → 'signature } as sign ;;
      let msg := Hash state chal in
      att ← sign (msg,sd) ;;
      (*#put attest_loc := att ;;*)
      ret att
    } ;
    #def #[verify_att] ('(chal, state, att) : ('challenge × 'state) × 'signature) : 'bool
    {
      #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
      let msg := Hash state chal in
      pk ← get pk_loc ;;
      verify (att,msg) 
    }
  ].

(* Encryption algorithm *)
  Definition Att_real :
  package Attestation_locs
    Sign_interface
    Att_interface
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    } ;
    #def #[attest] ( '(chal,(state,sd)) : 'challenge × ('state × 'seed)) : 'signature
    {
      #import {sig #[sign] : ('message  × 'seed) → 'signature } as sign ;;
      (*'(sk, pk) ← KeyGen2 sd ;;*)
      let (sk,pk) := KeyGen2 sd in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let msg := Hash state chal in
      att ← sign (msg, sd) ;;
      ret att
    } ;
    #def #[verify_att] ('(chal, state, att) : ('challenge × 'state) × 'signature) : 'bool
    {
      #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
      pk ← get pk_loc  ;;
      let msg := Hash state chal in
      bool ← verify (att, msg) ;;
      ret bool
    }
  ].

  Definition Att_ideal :
  package Attestation_locs
    Sign_interface
    Att_interface
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;
    #def #[attest] ( '(chal,(state,sd)) : 'challenge × ('state × 'seed)) : 'attest
    {
    #import {sig #[sign] : ('message  × 'seed) → 'signature } as sign ;;
      A ← get attest_loc ;;
      (*'(sk, pk) ← KeyGen2 sd ;;*)
      let (sk,pk) := KeyGen2 sd in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let msg := Hash state chal in
      att ← sign (msg, sk) ;;
      #put attest_loc := setm A ( chal, state, att ) tt ;;
      ret att
    };
    #def #[verify_att] ('(chal, state, att) : ('challenge × 'state) × 'attest) : 'bool
    {
      A ← get attest_loc ;;
      ret ( (chal, state, att) \in domm A )
    }
  ].

  Definition mkpair {Lt Lf E}
    (t: package Lt [interface] E) (f: package Lf [interface] E): loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.

  Equations mkpair' {Lt Lf E} (t: package Lt Sign_interface E) (f: package Lf Sign_interface E) (b:bool): loc_package Sign_interface E :=
    mkpair' t _ true  := {locpackage t};
    mkpair' _ f false := {locpackage f}.

  (*
  Definition mkpair' {Lt Lf E}
    (t: package Lt Sign_interface E) (f: package Lf Sign_interface E): loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.
   *)

  Definition Sig_unforg := @mkpair Signature_locs Signature_locs Sign_interface Sig_real Sig_ideal.

  Definition ɛ_att A := AdvantageE Att_real Att_ideal A.

  Definition Att_unforg := @mkpair' Attestation_locs Attestation_locs Att_interface Att_real Att_ideal.

  Lemma sig_real_vs_att_real_true :
    Att_unforg true ≈₀ Aux ∘ Sig_unforg true.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl. 
    - eapply rpost_weaken_rule.
      1: eapply rreflexivity_rule.
      move => [a1 h1] [a2 h2] [Heqa Heqh]. 
      intuition auto.
    - (*rewrite !cast_fun_K.*)
      destruct x.
      destruct s0.
      ssprove_sync_eq.
      ssprove_sync_eq.
      ssprove_code_simpl_more.
      eapply rpost_weaken_rule.
      1:{  
         
        }
      2:{ intros. }



      eapply rreflexivity_rule.
      ssprove_sync_eq.
      ssprove_code_simpl_more.
      eapply rsame_head_alt.          
      ssprove_sync.  
      ssprove_sync_eq. 
      
    ssprove_swap_lhs 0%N. 
    Admitted.
  (*Qed.*)

  Lemma sig_ideal_vs_att_ideal_true :
  Att_ideal ≈₀ Aux ∘ Sig_ideal.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    Admitted.
  (*Qed.*)

  Theorem RA_unforg LA A :
  ∀ LA A,
    ValidPackage LA [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : ('challenge × 'state) → 'attest ;
    #val #[verify_sig] : ( ('challenge × 'state) × 'attest) → 'bool
    ] A_export A →
    fdisjoint LA (sig_real_vs_att_real_true).(locs) →
    fdisjoint LA (sig_ideal_vs_att_ideal_true).(locs) →
    Advantage Att_unforg <= Advantage Sig_unforg.
Proof.
  
