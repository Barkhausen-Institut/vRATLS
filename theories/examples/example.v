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

Module Type SignatureDefs.

    Variable (n: nat). 
    Definition pos_n: nat := 2^n.
    Definition Seed : choice_type := chFin(mkpos pos_n).
    Definition SecKey : choice_type := chFin(mkpos pos_n).
    Definition PubKey : choice_type := chFin(mkpos pos_n).

End SignatureDefs.

Module Type SignatureAlgorithms (π : SignatureDefs).
  
  Import π.  
  #[local] Open Scope package_scope.

  Parameter KeyGen : ∀ (sd : Seed), (SecKey × PubKey).
    
End SignatureAlgorithms.

Module RemoteAttestation (π : SignatureDefs)
  (Alg : SignatureAlgorithms π).

  Import π.
  Import Alg.
  #[local] Open Scope package_scope.

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey      (at level 2): package_scope.
  Notation " 'seckey "    := SecKey      (in custom pack_type at level 2).
  Notation " 'seckey "    := SecKey      (at level 2): package_scope.  
  Notation " 'seed "      := Seed        (in custom pack_type at level 2).
  Notation " 'seed "      := Seed        (at level 2): package_scope.

  Definition chSet t := chMap t 'unit.
  Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
  Notation " 'set t " := (chSet t) (at level 2): package_scope.

  Definition tt := Datatypes.tt.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).

  Definition key_gen   : nat := 42. (* routine to get the public key *)

  Definition KeyGen_locs := fset [:: pk_loc ; sk_loc ]. 

  Definition Ideal_interface := [interface
  #val #[key_gen] : 'unit → 'pubkey 
  ].

  Definition Key_Gen_real :
  package KeyGen_locs
    [interface]
    [interface #val #[key_gen] : 'unit → 'pubkey ].
  :=
  [package
    #def  #[key_gen] (_ : 'unit) : 'pubkey
    {
    let (sk,pk) := KeyGen2 sd in
    #put pk_loc := pk ;;
    #put sk_loc := sk ;;
    ret pk
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

  Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.  

  Definition Sig_unforg := @mkpair Signature_locs Signature_locs Sign_interface Sig_real Sig_ideal.

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
    [interface]
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
      (*'(sk, pk) ← KeyGen2 sd ;;*)
      let (sk,pk) := KeyGen2 sd in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      att ← Attest sk chal state ;;
      ret att
    };
    #def #[verify_att] ('(chal, state, att) : ('challenge × 'state) × 'signature) : 'bool
    {
      pk ← get pk_loc  ;;
      bool ← Ver_att pk att chal state ;;
      ret bool
    }
  ].

  Definition Att_ideal :
  package Attestation_locs
    [interface]
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
      A ← get attest_loc ;;
      (*'(sk, pk) ← KeyGen2 sd ;;*)
      let (sk,pk) := KeyGen2 sd in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      att ← Attest sk chal state ;;      
      #put attest_loc := setm A ( chal, state, att ) tt ;; 
      ret att
    };
    #def #[verify_att] ('(chal, state, att) : ('challenge × 'state) × 'attest) : 'bool
    {
      A ← get attest_loc ;;
      ret ( (chal, state, att) \in domm A )
    }
  ].

  Definition ɛ_att A := AdvantageE Att_real Att_ideal A.

  Definition Att_unforg := mkpair Att_real Att_ideal.

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
      eapply rsame_head_alt. 
      simpl.
      eapply rreflexivity_rule.



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
  