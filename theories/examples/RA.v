

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

End SignatureParams.
  
(** |  SIGNATURE  |
    |   SCHEME    | **)

Module Type SignatureAlgorithms (π : SignatureParams).
  
  Import π.
  
  #[local] Open Scope package_scope.

(* Key Generation *)
  Parameter KeyGen :
  ∀ {L : {fset Location}},
    code L [interface] (SecKey × PubKey).

  (* Siganture algorithm *)
  Parameter Sign :
  ∀ {L : {fset Location}} (sk : SecKey) (m : Message),
    code L [interface] Signature.

  (* Verification algorithm *)
  Parameter Ver_sig :
  ∀ {L : {fset Location}} (pk : PubKey) (sig : Signature) (m : Message),
    code L [interface] 'bool.

  Notation " 'pubkey "    := PubKey    (in custom pack_type at level 2).
  Notation " 'signature " := Signature (in custom pack_type at level 2).
  Notation " 'state "     := State     (in custom pack_type at level 2).
  Notation " 'challenge " := Challenge (in custom pack_type at level 2).
  Notation " 'message "   := Message   (in custom pack_type at level 2).

  (**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
  *)
  Definition chSet t := chMap t 'unit.
  Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
  Notation " 'set t " := (chSet t) (at level 2): package_scope.

  Definition tt := Datatypes.tt.

  Notation " 'pk "    := (PubKey)      (in custom pack_type at level 2).
  Notation " 'pk "    := (PubKey)      (at level 2): package_scope.
  Notation " 'sk "    := (SecKey)      (in custom pack_type at level 2).
  Notation " 'sk "    := (SecKey)      (at level 2): package_scope.
  Notation " 'sig "   := (Signature)   (in custom pack_type at level 2).
  Notation " 'sig "   := (Signature)   (at level 2): package_scope.
  Notation " 'msg "   := (Message)     (in custom pack_type at level 2).
  Notation " 'msg "   := (Message)     (at level 2): package_scope.
  Notation " 'chal "  := (Challenge)   (in custom pack_type at level 2).
  Notation " 'chal "  := (Challenge)   (at level 2): package_scope.
  Notation " 'state " := (State)       (in custom pack_type at level 2).
  Notation " 'state " := (State)       (at level 2): package_scope.
  Notation " 'att "   := (Attestation) (in custom pack_type at level 2).
  Notation " 'att "   := (Attestation) (at level 2): package_scope.
  
  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition message_loc : Location := (Message   ; 2%N).   
  Definition sign_loc    : Location := ('set ('sig × 'msg); 3%N).
  Definition state_loc   : Location := (State    ; 4%N).
  Definition chal_loc    : Location := (Challenge ; 5%N).
  Definition attest_loc  : Location := ('set ('chal × 'state × 'att) ; 6%N).

  Definition get_pk    : nat := 42. (* routine to get the public key *)
  Definition get_state : nat := 43. (* routine to get the state to be attested *)
  Definition sign      : nat := 44. (* routine to sign a message *)
  Definition verify: nat := 45. (* routine to verify the signature *)

  Definition Signature_locs := fset [:: pk_loc ; sk_loc ; sign_loc ].

  Definition Sig_real :
  package Signature_locs
    [interface]
    [interface
      #val #[get_pk] : 'unit → 'pubkey ;
      #val #[sign] : 'message → 'signature ;
      #val #[verify] : ('signature × 'message) → 'bool
    ]
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    } ;

    #def #[sign] ( msg : 'message) : 'signature
    {
      '(sk, pk) ← KeyGen ;;
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      sig ← Sign sk msg ;;
      (*#put sign_loc := ( sig , msg ) ;; *)
      ret sig 
    };
    #def #[verify] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      '(sk, pk) ← KeyGen ;;
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      bool ← Ver_sig pk sig msg ;;
      ret bool
    }
  ].

  Definition Sig_ideal :
  package Signature_locs
    [interface]
    [interface
      #val #[get_pk] : 'unit → 'pubkey ;
      #val #[sign] : 'message → 'signature ;
      #val #[verify] : ('signature × 'message) → 'bool
    ]
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;
    #def #[sign] ( msg : 'message) : 'signature
    {
      '(sk, pk) ← KeyGen ;;
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;      
      sig ← Sign sk msg ;; 
      S ← get sign_loc ;; 
      #put sign_loc := setm S (sig, msg) tt ;;
      ret sig
    };
    #def #[verify] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      S ← get sign_loc ;;
      ret ( (sig,msg) \in domm S)      
    }
  ].

  Definition ɛ_sig A := AdvantageE Sig_real Sig_ideal A. 

  Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

  Definition Sig_unforg := mkpair Sig_real Sig_ideal.

End SignatureAlgorithms.

(** |    REMOTE   |
    | ATTESTATION | **)

Module Type AttestationAlgorithms (π : SignatureParams) 
                                (Alg : SignatureAlgorithms π). 

  Import π.
  Import Alg.

(* Encryption algorithm *)
  Parameter Attest :
  ∀ {L : {fset Location}} (sk : SecKey) ( c : Challenge ) (s : State),
     code L [interface] Attestation.
   
(* Decryption algorithm *)
  Parameter Ver_att :
  ∀ {L : {fset Location}} (pk : PubKey) (att : Attestation)
                 ( c : Challenge) ( s : State),
     code L [interface] 'bool.
      
  Notation " 'attest "    := Attestation    (in custom pack_type at level 2).  
  Definition attest    : nat := 46. (* routine to attest *)  

  Definition Attestation_locs := fset [:: pk_loc ; sk_loc; attest_loc ].

  Definition Att_real :
  package Attestation_locs
    [interface]
    [interface
      #val #[get_pk] : 'unit → 'pubkey ;
      #val #[sign] : ('challenge × 'state) → 'attest ;
      #val #[verify] : ( ('challenge × 'state) × 'attest) → 'bool
    ]
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    } ;
    #def #[sign] ( '(chal,state) : 'challenge × 'state) : 'attest
    {
      '(sk, pk) ← KeyGen ;;
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      att ← Attest sk chal state ;;
      ret att
    };
    #def #[verify] ('(chal, state, att) : ('challenge × 'state) × 'attest) : 'bool
    {
      '(sk, pk) ← KeyGen ;;
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      bool ← Ver_att pk att chal state ;;
      ret bool
    }
  ].

  Definition Att_ideal :
  package Attestation_locs
    [interface]
    [interface
      #val #[get_pk] : 'unit → 'pubkey ;
      #val #[sign] : ('challenge × 'state) → 'attest ;
      #val #[verify] : ( ('challenge × 'state) × 'attest) → 'bool
    ]
  :=
  [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;
    #def #[sign] ( '(chal,state) : 'challenge × 'state) : 'attest
    {
      A ← get attest_loc ;;
      '(sk, pk) ← KeyGen ;;
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      att ← Attest sk chal state ;;      
      #put attest_loc := setm A ( chal, state, att ) tt ;; 
      ret att
    };
    #def #[verify] ('(chal, state, att) : ('challenge × 'state) × 'attest) : 'bool
    {
      A ← get attest_loc ;;
      ret ( (chal, state, att) \in domm A )
    }
  ].

  Definition ɛ_att A := AdvantageE Att_real Att_ideal A.

  Definition Att_unforg := mkpair Att_real Att_ideal.

  Lemma sig_real_vs_att_real_true :
  ∀ {L₀ L₁ E} (Att_real Sig_real : raw_package) (inv : precond)
  `{ValidPackage L₀ Game_import E Att_real}
  `{ValidPackage L₁ Game_import E Sig_real},
  Invariant L₀ L₁ inv →
  eq_up_to_inv E inv Att_real Sig_real →
  Att_real ≈₀ Sig_real.
  Proof.
    intros. revert H2.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    ssprove_code_simpl. 
    Admitted.
  (*Qed.*)

  Lemma sig_ideal_vs_att_ideal_true :
  ∀ {L₀ L₁ E} (Att_ideal Sig_ideal : raw_package) (inv : precond)
  `{ValidPackage L₀ Game_import E Att_ideal}
  `{ValidPackage L₁ Game_import E Sig_ideal},
  Invariant L₀ L₁ inv →
  eq_up_to_inv E inv Att_ideal Sig_ideal →
  Att_ideal ≈₀ Sig_ideal.
  Proof.
    (*intros A B c s d a w f e i k l.
    eapply eq_rel_perf_ind_eq.
    1: simplify_eq_rel m.
    ssprove_code_simpl. *)
    Admitted.
  (*Qed.*)

  Theorem RA_unforg LA A :
  ∀ LA A,
    ValidPackage LA [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : ('challenge × 'state) → 'attest ;
    #val #[verify] : ( ('challenge × 'state) × 'attest) → 'bool
    ] A_export A →
    fdisjoint LA (sig_real_vs_att_real_true).(locs) →
    fdisjoint LA (sig_ideal_vs_att_ideal_true).(locs) →
    Advantage Att_unforg <= Advantage Sig_unforg.
Proof.
  