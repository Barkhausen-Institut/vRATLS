(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.

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
  *)

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
  proofs with [ssprove_code_simpl] do not resolve properly.
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

Require Import Signature. 

(* Sadly, this approach being polymorphic about the heap location
   did not work out.
   I was unable to create a message of type [choice_type] in the RA part.
 *)
Module Type RemoteAttestationParamsFail <: SignatureConstraintsFail.

  (*
    Internally, ['fin (mkpos pos_n] creates [ordinal of pos_n] which is [I_(pos_n)].
    It would just be nice to find a way to derive [chState] from [State].
   *)
  Definition State : finType := [finType of 'I_(pos_n)].
  Definition chState : choice_type := 'fin (mkpos pos_n). (* ordinal_choiceType (pos_n). *)
  Definition Challenge : finType := [finType of 'I_(pos_n)].
  Definition chChallenge : choice_type := 'fin (mkpos pos_n). (* ordinal_choiceType pos_n. *)
  (*Definition chChallenge : choice_type := 'fin (mkpos pos_n). *)
  Definition Attestation : choice_type := 'fin (mkpos pos_n).
  Notation " 'chal " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Definition i_chal : nat := 2^n.

  Definition Message := prod_finType Challenge State.
  #[export] Instance Message_pos : Positive #|Message|.
  Admitted.
  Definition chMessage := 'fin #|Message|. 
  (*
  J: Not sure if we still need this. 
  --> can't rewrite, because then the "End RemmoteAttestationParamsFail" command gives:
  Error: 'Signature components for label chMessage do not match:
   the body of definitions differs.'

   Now everything is defined
  *)
  Definition Message' : finType := [finType of 'I_(pos_n)].
  Definition chMessage' : choice_type := 'fin (mkpos pos_n).
  #[export] Instance Message_pos' : Positive #|Message|.
  Admitted.
  

End RemoteAttestationParamsFail.

(*
  The below specification is complete but insufficient.
  See the comments on the [Hash] function.
 *)
Module HeapHash.

  Module Type RemoteAttestationParams <: SignatureConstraints.

    Definition chState : choice_type := 'fin (mkpos pos_n).
    Definition chChallenge : choice_type := 'fin (mkpos pos_n).
    Definition Attestation : choice_type := 'fin (mkpos pos_n).

    Definition chMessage := 'fin (mkpos pos_n).

  End RemoteAttestationParams.

  Module Type RemoteAttestationAlgorithms
    (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2).
    Import π1.
    Import π2.
    Import π3.

    Local Open Scope package_scope.

    Notation " 'state "     := chState       (in custom pack_type at level 2).
    Notation " 'state "     := chState       (at level 2): package_scope.
    Notation " 'challenge " := chChallenge   (in custom pack_type at level 2).
    Notation " 'challenge " := chChallenge   (at level 2): package_scope.

    Definition state_loc   : Location := ('state    ; 4%N).
    Definition attest_loc  : Location := ('set (Signature × chMessage) ; 2%N).

    Definition verify_att: nat := 46.

    Notation " 'attest "    := Attestation    (in custom pack_type at level 2).
    Definition attest    : nat := 47. (* routine to attest *)

    (*
      FIXME this hash function spec is insufficient.
      It allows to discard one of the arguments and just return the other as message!
     *)
    Parameter Hash : chState -> chChallenge -> chMessage.

  End RemoteAttestationAlgorithms.

  Module RemoteAttestation
    (π1 : SignatureParams)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2)
    (π4 : RemoteAttestationAlgorithms π1 π2 π3)
    (π5 : SignatureScheme π1 π2 π3).

    Import π1 π2 π3 π4 π5.


    (* The remote attestation protocol does the same as the signature scheme, i.e.,
       it stores the attestations handed out.
     *)
    Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
    Definition Attestation_locs_fake := Attestation_locs_real :|: fset [:: attest_loc ].

    (*
      The key challenge: relate [sign_loc] and [attest_loc].
      There are 2 approaches:
      1) we compute a [message] (Signature Scheme) from the [state] and the [challenge] of the
         remote attestation algorithm.
      2) we make the type of the [sign_loc] in the Signature Scheme polymorph.

      This is the second approach.
     *)


    Definition Att_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[attest] : 'challenge → 'signature ;
    #val #[verify_att] : ('challenge × 'signature) → 'bool
    ].

    (* OLD VERION, NEW VERSION underneath *)
    Definition Att_real : package Attestation_locs_real [interface] Att_interface
    := [package
      #def  #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc  ;;
        ret pk
      };

      #def #[attest] (chal : 'challenge) : 'signature
      {
        state ← get state_loc ;;
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash state chal in
        let att := Sign sk msg in
        ret att
      };

      #def #[verify_att] ('(chal, att) : ('challenge × 'signature)) : 'bool
      {
        pk ← get pk_loc ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let bool := Ver_sig pk att msg in
        ret bool
      }
    ].

    Equations Att_ideal : package Attestation_locs_fake [interface] Att_interface :=
    Att_ideal := [package
      #def  #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] (chal : 'challenge) : 'attest
      {
        A ← get attest_loc ;;
        s ← get state_loc ;;
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash s chal in
        let att := Sign sk msg in
        #put attest_loc := setm A ( att, msg ) tt ;;
        ret att
      };

      #def #[verify_att] ('(chal, att) : ('challenge × 'attest)) : 'bool
      {
        A ← get attest_loc ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let b :=  (att, msg) \in domm A in
        ret b
      }
    ].
    Next Obligation.
      ssprove_valid; rewrite /Attestation_locs_fake/Attestation_locs_real in_fsetU; apply /orP.
      1,3,7: right;auto_in_fset.
      all: left; auto_in_fset.
    Defined.

 (* THIS IS THE NEW VERSION (with sampling the challenge) 
    incl. defining all sorts of stuff *)

    Definition chChal : choice_type := 'fin ((2^n)%N).
    Notation " 'chal "     := chChal       (in custom pack_type at level 2).
    Notation " 'chal "     := chChal       (at level 2): package_scope.
    Definition i_chal : nat := 2^n.

    Parameter Hash' : chState -> chChal -> chMessage.

    Definition chal_loc    : Location := ('chal ; 5%N).

    Definition Attestation_locs_real_new := fset [:: pk_loc ; sk_loc; state_loc ; chal_loc ].
    Definition Attestation_locs_fake_new := Attestation_locs_real_new :|: fset [:: attest_loc ].
   
    Definition Att_interface_new := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[attest] : 'unit → 'signature ;
    #val #[verify_att] : 'signature → 'bool
    ].

    Definition Att_real_sample_chal : package Attestation_locs_real_new 
              [interface] Att_interface_new
    := [package
      #def  #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc  ;;
        ret pk
      };

      #def #[attest] (_ : 'unit) : 'signature
      {
        chal ←  sample uniform i_chal ;;
        #put chal_loc := chal ;;
        state ← get state_loc ;;
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash' state chal in
        let att := Sign sk msg in
        ret att
      };

      #def #[verify_att] ( att : 'signature) : 'bool
      {
        pk ← get pk_loc ;;
        chal ← get chal_loc ;;
        state ← get state_loc ;;
        let msg := Hash' state chal in
        let bool := Ver_sig pk att msg in
        ret bool
      }
    ].

    Equations Att_ideal : package Attestation_locs_fake_new 
         [interface] Att_interface_new :=
    Att_ideal := [package
      #def  #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] (_ : 'unit) : 'attest
      {
        chal ←  sample uniform i_chal ;;
        #put chal_loc := chal ;;
        A ← get attest_loc ;;
        s ← get state_loc ;;
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash' s chal in
        let att := Sign sk msg in
        #put attest_loc := setm A ( att, msg ) tt ;;
        ret att
      };

      #def #[verify_att] ('(chal, att) : ('challenge × 'attest)) : 'bool
      {
        A ← get attest_loc ;;
        chal ← get chal_loc ;;
        state ← get state_loc ;;
        let msg := Hash' state chal in
        let b :=  (att, msg) \in domm A in
        ret b
      }
    ].
    Next Obligation.
      ssprove_valid; rewrite /Attestation_locs_fake_new/Attestation_locs_real_new in_fsetU; apply /orP.
      1,3,7: right;auto_in_fset.
      all: left; auto_in_fset.
    Defined.


    (*
      TODO:
      Currently, these descriptions do not facilitate an actual protocol.
      A protocol really is where I call [attest] and [verify_att] in one single piece of code.
      The thing that happens then is that there need to be two locations for the state:
      one in the client and the other in the server.
     *)

    (* We need a common interface, so we need to define an [AUX] for the
       signature scheme.
     *)
    Definition Aux_locs := fset [:: pk_loc ; state_loc ].

    Definition Aux : package Aux_locs Sign_interface Att_interface :=
    [package
      #def #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] ( chal : 'challenge ) : 'signature
      {
        #import {sig #[sign] : 'message  → 'signature } as sign ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        att ← sign msg ;;
        ret att
      };

      #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
      {
        #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        b  ← verify (att,msg) ;;
        ret b
        (* When I just write:
           [verify (att,msg)]
           Then SSProve errors out and cannot validate the package. Why?
         *)
      }
    ].

    (* Explicit definition of an attacker/distinguisher

    Definition Dist :
      package
        Dist_locs Att_interface
        [interface
           #val #[RUN] : 'unit → 'bool ]
    :=
    [package
      #def #[RUN] (_ : 'unit) : 'bool
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk
        #import {sig #[attest] : 'challenge → 'signature } as attest
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att

        (* distinguisher code -- attack *)
        let pk := get_pk () in
        ...
      };

    ].

    *)

    Definition mkpair {Lt Lf E}
      (t: package Lt [interface] E) (f: package Lf [interface] E): loc_GamePair E :=
      fun b => if b then {locpackage t} else {locpackage f}.

    Definition Sig_unforg := @mkpair Signature_locs_real Signature_locs_fake Sign_interface Sig_real Sig_ideal.
    Definition Att_unforg := @mkpair Attestation_locs_real Attestation_locs_fake Att_interface Att_real Att_ideal.

    Lemma sig_real_vs_att_real_true:
      Att_unforg true ≈₀  Aux ∘ Sig_unforg true.
    Proof.
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel x.
      all: ssprove_code_simpl.
      - eapply rpost_weaken_rule.
        1: eapply rreflexivity_rule.
        move => [a1 h1] [a2 h2] [Heqa Heqh].
        intuition auto.
      - destruct x.
        ssprove_sync_eq => state.
        do 2! ssprove_sync_eq.
        by [apply r_ret].
      - case x => s s0.
        case s => s1 s2.
        ssprove_swap_lhs 0.
        ssprove_sync_eq => state.
        ssprove_sync_eq => pk.
        by [apply r_ret].
    Qed.

    Lemma sig_ideal_vs_att_ideal_false :
      Att_unforg false ≈₀ Aux ∘ Sig_unforg false.
    Proof.
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel x.
      all: ssprove_code_simpl.
      - ssprove_sync_eq => pk_loc.
        by [apply r_ret].
      - ssprove_swap_lhs 0; ssprove_sync_eq => state.
        do 2! (ssprove_swap_lhs 0; ssprove_sync_eq).
        ssprove_sync_eq => sig.
        ssprove_sync_eq.
        by [apply r_ret].
      - case x => a b.
        ssprove_swap_lhs 0; ssprove_sync_eq => state.
        ssprove_sync_eq => sig.
        by [apply r_ret].
    Qed.

    Theorem RA_unforg LA A :
        ValidPackage LA Att_interface A_export A →
        fdisjoint LA (Sig_unforg true).(locs) →
        fdisjoint LA (Sig_unforg false).(locs) →
        fdisjoint LA Aux_locs →
        fdisjoint LA (Att_unforg true).(locs) →
        fdisjoint LA (Att_unforg false).(locs) →
        (Advantage Att_unforg A <= AdvantageE Sig_ideal Sig_real (A ∘ Aux))%R.
    Proof.
      move => va H1 H2 H3 H4 H5.
      rewrite Advantage_E Advantage_sym.
      simpl in H1.
      simpl in H2.
      simpl in H3.
      simpl in H4.
      simpl in H5.
      ssprove triangle (Att_unforg true) [::
        Aux ∘ Sig_unforg true ;
        Aux ∘ Sig_unforg false
        ] (Att_unforg false) A as ineq.
      eapply le_trans.
      1: { exact: ineq. }
      clear ineq.
      rewrite sig_real_vs_att_real_true.
      2: simpl; exact: H4.
      2: {
        simpl.
        rewrite fdisjointUr.
        apply/andP; split; assumption.
      }
      rewrite GRing.add0r.
      rewrite [X in (_ + X <= _)%R]Advantage_sym.
      rewrite sig_ideal_vs_att_ideal_false.
      2: { simpl; exact: H5. }
      2: { rewrite fdisjointUr; apply/andP; split; assumption. }
      rewrite GRing.addr0.
      by [rewrite -Advantage_link Advantage_sym].
    Qed.

  End RemoteAttestation.
End HeapHash.

(** We need a specification for remote attestation that
    carves out the properties of the [Hash] function.

   Two approaches (may) exist:
   [HeapHashAltAlgo] We leave the heap structures equal with respect to the
      signature scheme and try to change the spec of the algorithms
      such as [verify_att] in the ideal case accordingly.
   [NoHeapHash] We write the attestation spec pretending that
      we are not aware of the heaps of the signature scheme.
      That is, we store the [(challenge,state)] tuple insted of the
      already hashed [msg].
 *)



