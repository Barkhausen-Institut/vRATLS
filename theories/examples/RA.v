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
Require Import Lia.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

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


(** |  SIGNATURE  |
    |   SCHEME    | **)

  
Module Type SignatureParams.

    Parameter SecKey PubKey State Challenge Attest : finType.
    (* seed = input key gen
       State = state of device to be attested, called quoted in specification
       Challenge = send by verifier to attester
       Attest = signature (maybe signature || message?)
    *)  
    Parameter SecKey_pos : Positive #|SecKey|.
    Parameter PubKey_pos : Positive #|PubKey|.
    Parameter State_pos : Positive #|State|.
    Parameter Challenge_pos : Positive #|Challenge|.
    Parameter Attest_pos : Positive #|Attest|.
    Parameter Bool_pos : Positive #|bool_choiceType|.
  
End SignatureParams.
  
Module Type SignatureAlgorithms (π : SignatureParams).
  
  Import π.
  
  #[local] Open Scope package_scope.  
   
  #[local] Existing Instance State_pos. 
  #[local] Existing Instance Challenge_pos. 
  #[local] Existing Instance Attest_pos. 
  #[local] Existing Instance Bool_pos.
  #[local] Existing Instance SecKey_pos.
  #[local] Existing Instance PubKey_pos.
  
  (* defining the instances again*)
  Definition ch_state := 'fin #|State|.  (* using "choice" because of choice_type *)
  Definition ch_challenge := 'fin #|Challenge|.      (* "'fin" is their own finite set definition with n>0, not n >= 0 *)
  Definition ch_attest := 'fin #|Attest|.  
  Definition ch_Bool := 'fin #|bool_choiceType|.
  Definition ch_sec_key := 'fin #|SecKey|.
  Definition ch_pub_key := 'fin #|PubKey|.
  Definition choice_Transcript :=
    chProd (chProd ch_challenge ch_state) ch_attest.
    
  Parameter Sign_locs : {fset Location}.     (* | Defining a finite set (fset) of elements of type Location*)
  Parameter Sign_Simul_locs : {fset Location}.
  
  Parameter Sig_Sign :
    ∀ (sk : ch_sec_key) (c : ch_challenge) (s : ch_state),
    code Sign_locs [interface] ch_attest.
  
  Parameter Sig_Verify :
  ∀ (pk : ch_pub_key) (c : ch_challenge) (s : ch_state) (a : ch_attest),
    code Sign_locs [interface] ch_Bool.

  Parameter Sig_Simulate :
    ∀ (c : ch_challenge) (s : ch_state),
    code Sign_Simul_locs [interface] choice_Transcript.

  Parameter KeyGen : forall (sk : ch_sec_key), ch_pub_key.
  
  End SignatureAlgorithms.
  
  
  Module Type Signature (π : SignatureParams)
  (Alg : SignatureAlgorithms π).
  
      Import π.
      Import Alg.
  
      Definition TRANSCRIPT : nat := 0.
      Definition choice_Input :=  
        chProd (chProd ch_challenge ch_state) ch_sec_key.
      Notation " 'chInput' " := 
        choice_Input (in custom pack_type at level 2).
      Notation " 'chTranscript' " :=
        choice_Transcript (in custom pack_type at level 2).     
  
      Definition Sign_real:
        package Sign_locs
          [interface] (** No procedures from other packages are imported. *)
          [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
        :=
        [package
          #def #[ TRANSCRIPT ] (cqsk : chInput) : chTranscript 
          {
            let '(c,q,sk) := cqsk in
            m ← Sig_Sign sk c q ;;
            @ret choice_Transcript (c,q,m) 
          }
        ].
      
      Definition Sign_ideal:
      package Sign_Simul_locs
          [interface] (** No procedures from other packages are imported. *)
          [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
        :=
        [package
          #def #[ TRANSCRIPT ] (cqsk : chInput) : chTranscript 
          {
            let '(c,q,sk) := cqsk in
            t ← Sig_Simulate c q ;;
            ret t
          }
          ].

      Definition ɛ_sign A := AdvantageE Sign_real Sign_ideal A.  

(** |    REMOTE   |
    | ATTESTATION | **)

    Section RemoteAttestation.

    Definition ATTEST : nat := 5.
    Definition GET_sk : nat := 6.
    Definition GET_pk : nat := 7.
    Definition INIT : nat := 8.

    Definition challenge_loc : Location := ('option ch_challenge; 7%N).
    Definition response_loc : Location := ('option ch_attest; 8%N).

    Definition Com_locs : {fset Location} := 
      fset [:: challenge_loc ; response_loc ].

    Definition setup_loc : Location := ('bool; 10%N).
    Definition sk_loc : Location := (ch_sec_key; 11%N).
    Definition pk_loc : Location := (ch_pub_key; 12%N).
    Definition KEY_locs : {fset Location} := 
      fset [:: setup_loc; sk_loc ; pk_loc].

     Lemma in_fset_left l (L1 L2 : {fset Location}) :
      is_true (l \in L1) →
      is_true (l \in (L1 :|: L2)).
    Proof.
      intros H.
      apply /fsetUP.
      left. assumption.
    Qed.

    Definition i_sk := #|SecKey|.
    Definition i_sk_pos : Positive i_sk.
    Proof.
      unfold i_sk.
      apply SecKey_pos.
    Qed.
  
    #[local] Existing Instance i_sk_pos.

    Hint Extern 20 (is_true (_ \in (_ :|: _))) =>
      apply in_fset_left; solve [auto_in_fset]
      : typeclass_instances ssprove_valid_db.

    Notation " 'chSecKey' " :=
        ch_sec_key (in custom pack_type at level 2).        
    Notation " 'chPubKey' " :=
        ch_pub_key (in custom pack_type at level 2).
    Notation " 'chAttest' " :=
        ch_attest (in custom pack_type at level 2).

    Definition KEY:
      package KEY_locs
        [interface]
        [interface
           #val #[ INIT ] : 'unit → 'unit ;
           #val #[ GET_sk ] : 'unit → chSecKey ;
           #val #[ GET_pk ] : 'unit → chPubKey
        ]
      :=
      [package
         #def #[ INIT ] (_ : 'unit) : 'unit
         {
           b ← get setup_loc ;;
           #assert (negb b) ;;
           sk ← sample uniform i_sk ;;
           let pk := KeyGen sk in
           #put setup_loc := true ;;
           #put sk_loc := sk ;;
           #put pk_loc := pk ;;
           @ret 'unit Datatypes.tt
         }
         ;
         #def #[ GET_sk ] (_ : 'unit) : chSecKey
         {
           b ← get setup_loc ;;
           if b then
             sk ← get sk_loc ;;
             pk ← get pk_loc ;;
             ret sk
           else
             fail
         }
         ;
         #def #[ GET_pk ] (_ : 'unit) : chPubKey
         {
           b ← get setup_loc ;;
           if b then
             sk ← get sk_loc ;;
             pk ← get pk_loc ;;
             ret pk
           else
             fail
         }
      ].

    Definition Sigma_to_Com_locs := (Com_locs :|: Sign_Simul_locs).
    
    #[tactic=notac] Equations? Sigma_to_Com:
    package Sigma_to_Com_locs
      [interface
        #val #[ INIT ] : 'unit → 'unit ;
        #val #[ GET_sk ] : 'unit → chSecKey ;
        #val #[ GET_pk ] : 'unit → chPubKey
      ]
      [interface
        #val #[ ATTEST ] : 'unit → chAttest ;
        #val #[ VER ] : chTranscript → 'bool
      ]
    := Sigma_to_Com :=
    [package
      #def #[ ATTEST ] (_ : 'unit) : chAttest
      {
        #import {sig #[ INIT ] : 'unit → 'unit } as key_gen_init ;;
        #import {sig #[ GET_sk ] : 'unit → chStatement } as key_gen_get_sk ;;
        #import {sig #[ GET_pk ] : 'unit → chStatement } as key_gen_get_pk ;;
        _ ← key_gen_init Datatypes.tt ;;
        sk ← key_gen_get_sk Datatypes.tt ;;
        pk ← key_gen_get_pk Datatypes.tt ;;

        ∀ (c : ch_challenge) (s : ch_state),
        code Sign_Simul_locs [interface] choice_Transcript.

        '(c,s,a) ← Sig_Simulate c s ;;
        #put challenge_loc := Some e ;;
        #put response_loc := Some z ;;
        ret a
      }
     ;
      #def #[ OPEN ] (_ : 'unit) : chOpen
      {
        o_e ← get challenge_loc ;;
        o_z ← get response_loc ;;
        match (o_e, o_z) with
        | (Some e, Some z) => @ret choiceOpen (e, z)
        | _ => fail
        end
      }
      ;
      #def #[ VER ] (t : chTranscript) : 'bool
      {
        let '(h,a,e,z) := t in
        ret (otf (Verify h a e z))
      }
    ].
  Proof.
    unfold Sigma_to_Com_locs.
    ssprove_valid.
    eapply valid_injectLocations.
    1: apply fsubsetUr.
    eapply valid_injectMap.
    2: apply (Simulate x1 x).
    rewrite -fset0E.
    apply fsub0set.
  Qed.

  End Signature.



Module Type RemoteAttestationParams.

  Parameter lt_key attest_token state_device output sec_param : finType.

  Parameter lt_key_pos : Positive #|lt_key|.
  Parameter attest_token_pos : Positive #|attest_token|.
  Parameter state_device_pos : Positive #|state_device|.
  Parameter output_pos : Positive #|output|.
  Parameter sec_param_pos : Positive #|sec_param|.

End RemoteAttestationParams.


Module Type RemoteAttestationAlgorithms (π : RemoteAttestationParams).

  Import π.

  #[local] Open Scope package_scope.   (* sort of global definition (variables, func., ...), defined in the project*)

  #[local] Existing Instance lt_key_pos.         (*| calling instances from the SigmaProtocolParams Module above*)
  #[local] Existing Instance attest_token_pos.   (*| *)
  #[local] Existing Instance state_device_pos.   (*| *)
  #[local] Existing Instance output_pos.         (*| *) 
  #[local] Existing Instance sec_param_pos.         (*| *) 
  (*#[local] Existing Instance choice_challenge.*)


  Definition choice_lt_key := 'fin #|lt_key|.      (* defining the instances again*)
  Definition choice_attest_token := 'fin #|attest_token|.  (* using "choice" because of choice_type *)
  Definition choice_state_device := 'fin #|state_device|.      (* "'fin" is their own finite set definition with n>0, not n >= 0 *)
  Definition choice_output := 'fin #|output|.
  Definition choice_sec_param := 'fin #|sec_param|.
  Definition choiceTranscript :=
      chProd choice_lt_key choice_attest_token.  

  Parameter RA_locs : {fset Location}.     (* | Defining a finite set (fset) of elements of type Location*)
  Parameter RA_Simul_locs : {fset Location}.

  Parameter RA_Setup :
  ∀ (i : choice_sec_param), 
  code RA_locs [interface] choice_lt_key.

  Parameter RA_Attest :
  ∀ (k : choice_lt_key) (s : choice_state_device),
    code RA_locs [interface] choice_attest_token.

  Parameter RA_Verify :
  ∀ (k : choice_lt_key) (s : choice_state_device)
  (a : choice_attest_token),
    code RA_locs [interface] choice_output.

  Parameter RA_Simulate :
  ∀ (i : choice_sec_param) (s : choice_state_device),
    code RA_Simul_locs [interface] choiceTranscript.

End RemoteAttestationAlgorithms.


Module RemoteAttestation (π : RemoteAttestationParams)
(Alg : RemoteAttestationAlgorithms π).

    Import π.
    Import Alg.

    Definition TRANSCRIPT : nat := 0.
    Definition choiceInput :=  (chProd choice_sec_param choice_state_device).
    Notation " 'chInput' " := 
      choiceInput (in custom pack_type at level 2).
    Notation " 'chTranscript' " :=
      choiceTranscript (in custom pack_type at level 2).
   

    Definition RA_real:
      package RA_locs
        [interface] (** No procedures from other packages are imported. *)
        [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
      :=
      [package
        #def #[ TRANSCRIPT ] (si : chInput) : chTranscript 
        {
          let '(i,s) := si in
          k ← RA_Setup i ;;
          a ← RA_Attest k s ;;
          @ret choiceTranscript (k,a) 
        }
        ].
    
    Definition RA_ideal:
      package RA_Simul_locs
        [interface] (** No procedures from other packages are imported. *)
        [interface #val #[ TRANSCRIPT ] : chInput → chTranscript]
      :=
      [package
        #def #[ TRANSCRIPT ] (si : chInput) : chTranscript 
        {
          let '(i,s) := si in
          t ← RA_Simulate i s ;;
          ret t 
        }
      ].

  Definition ɛ_RA A := AdvantageE RA_real RA_ideal A.