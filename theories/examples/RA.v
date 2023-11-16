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

Require Import examples.Signature.

Module HeapHash.

  Module Type RemoteAttestationParams <: SignatureConstraints.

    Definition chState     : choice_type := 'fin (mkpos pos_n).
    Definition Attestation : choice_type := 'fin (mkpos pos_n).

    Definition chMessage   : choice_type := 'fin (mkpos pos_n).

    Parameter Challenge : finType.
     Parameter Challenge_pos : Positive #|Challenge|.
     #[local] Existing Instance Challenge_pos.
     Definition chChallenge := 'fin #|Challenge|.
     

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
    Notation " 'attest "    := Attestation    (in custom pack_type at level 2).
    
    Definition state_loc   : Location := ('state    ; 4%N).
    Definition attest_loc  : Location := ('set (Signature × chMessage) ; 2%N).

    Definition verify_att   : nat := 46.
    Definition verify_att_f : nat := 47.

    Definition attest       : nat := 48. 
    Definition attest_f     : nat := 49.

    Parameter Hash : chState -> chChallenge -> chMessage.

  End RemoteAttestationAlgorithms.

  Module Type RemoteAttestation
    (π1 : SignatureParams)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2)
    (π4 : RemoteAttestationAlgorithms π1 π2 π3)
    (π5 : SignaturePrimitives π1 π2 π3).

    Import π1 π2 π3 π4 π5.

    (* The remote attestation protocol does the same as the signature scheme, i.e.,
       it stores the attestations handed out.
     *)
    Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
    Definition Attestation_locs_ideal := Attestation_locs_real :|: fset [:: attest_loc ].


    Definition Att_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[attest] : 'challenge → ('signature × 'message) ;
    #val #[verify_att] : ('challenge × 'signature) → 'bool
    ].

    Definition Att_real : package Attestation_locs_real [interface] 
      Att_interface
    := [package
      #def  #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc  ;;
        ret pk
      };

      #def #[attest] (chal : 'challenge) : ('signature × 'message)
      {
        state ← get state_loc ;;
        let (sk,pk) := KeyGen in
      (*
      '(sk,pk) ← KeyGen ;;
      *)
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash state chal in
        let att := Sign sk msg in
        ret (att, msg)
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

    Equations Att_ideal : package Attestation_locs_ideal [interface] Att_interface :=
    Att_ideal := [package

      #def  #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] (chal : 'challenge) : ('signature × 'message)
      {
        A ← get attest_loc ;;
        s ← get state_loc ;;
        let (sk,pk) := KeyGen in
        (*
        '(sk,pk) ← KeyGen ;;
        *)
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash s chal in
        let att := Sign sk msg in
        #put attest_loc := setm A ( att, msg ) tt ;;
        (* #put attest_loc := setm A ( att, (chal, s) ) tt ;; *)
        ret (att, msg)
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
      ssprove_valid; rewrite /Attestation_locs_ideal/Attestation_locs_real in_fsetU; apply /orP.
      1,3,7: right;auto_in_fset.
      all: left; auto_in_fset.
    Defined.



    (* We need a common interface, so we need to define an [AUX] for the
       signature scheme.
     *)
     (* can remove sk_loc and sign_loc, they are used in prove below, 
     but that sould also work without *)
    Definition Aux_locs := fset [:: pk_loc ; sk_loc ; sign_loc ; state_loc ].

    Definition Aux : package Aux_locs Prim_interface Att_interface :=
    [package
      #def #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] ( chal : 'challenge ) : ('signature × 'message)
      {
        #import {sig #[sign] : 'message  → 'signature } as sign ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        att ← sign msg ;;
        ret (att, msg)
      };

      #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
      {
        #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        b  ← verify (att,msg) ;;
        ret b
      }
    ].

    Lemma sig_real_vs_att_real:
      Att_real ≈₀ Aux ∘ Prim_real.
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

    Definition Comp_locs := fset [:: pk_loc; sk_loc ; sign_loc ; state_loc ].

    (* You need to redefine [Aux] to match the import interface of [Aux] to
       the export interface of [Prim_ideal]  *)
    Definition Aux_ideal : package Aux_locs Prim_interface_f Att_interface :=
    [package
      #def #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] ( chal : 'challenge ) : ('signature × 'message)
      {
        #import {sig #[sign_f] : 'message  → 'signature } as sign ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        att ← sign msg ;;
        ret (att, msg)
      };

      #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
      {
        #import {sig #[verify_sig_f] : ('signature × 'message) → 'bool } as verify ;;
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

    Definition Prim_real_locp := {locpackage Prim_real}.
    Definition Prim_ideal_locp := {locpackage Prim_ideal}.
    Definition Att_real_locp := {locpackage Att_real}.
    Definition Att_ideal_locp := {locpackage Att_ideal}.


    Equations Aux_Prim_ideal : package Comp_locs [interface] Att_interface :=
      Aux_Prim_ideal := {package Aux_ideal ∘ Prim_ideal_locp}.
    Next Obligation.
      ssprove_valid.
      - rewrite /Aux_locs/Comp_locs.
        rewrite [X in fsubset _ X]fset_cons.
        rewrite fset_cons.
        apply fsetUS.
        rewrite [X in fsubset _ X]fset_cons.
        rewrite fset_cons.
        apply fsetUS.
        rewrite [X in fsubset _ X]fset_cons.
        rewrite fset_cons.
        apply fsetUS.
        rewrite !fset_cons -fset0E.
        apply fsetUS.
        apply fsub0set.
      - rewrite /(locs Prim_ideal_locp)/Comp_locs. 
        rewrite [X in fsubset _ X]fset_cons.
        unfold Prim_locs_ideal.
        rewrite fset_cons.
        apply fsetUS.
        rewrite [X in fsubset _ X]fset_cons.
        rewrite fset_cons.
        apply fsetUS.
        rewrite !fset_cons -fset0E.
        apply fsetUS.
        apply fsub0set.
    Defined.

    Lemma sig_ideal_vs_att_ideal :
      Att_ideal_locp ≈₀ Aux_Prim_ideal.
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
        fdisjoint LA (Prim_real_locp).(locs) →
        fdisjoint LA (Prim_ideal_locp).(locs) →
        fdisjoint LA Aux_locs →
        fdisjoint LA (Att_real_locp).(locs) →
        fdisjoint LA (Att_ideal_locp).(locs) →
        (AdvantageE Att_ideal_locp Att_real_locp A <= AdvantageE Aux_Prim_ideal (Aux ∘ Prim_real_locp) A)%R.
    Proof.
      move => va H1 H2 H3 H4 H5.
      rewrite Advantage_sym.
      simpl in H1.
      simpl in H2.
      simpl in H3.
      simpl in H4.
      simpl in H5.
      ssprove triangle (Att_real_locp) [::
        Aux ∘ Prim_real_locp ;
        Aux_ideal ∘ Prim_ideal_locp
        ] (Att_ideal_locp) A as ineq.
      eapply le_trans.
      1: { exact: ineq. }
      clear ineq.
      rewrite sig_real_vs_att_real.
      2: simpl; exact: H4.
      2: {
        simpl.
        rewrite fdisjointUr.
        apply/andP; split; assumption.
      }
      rewrite GRing.add0r.
      rewrite [X in (_ + X <= _)%R]Advantage_sym.

      (* Set Typeclasses Debug Verbosity 2. *)

      rewrite sig_ideal_vs_att_ideal.
      (* Type class resolution failed because of the [Att_interface_f].
         Both advantages need to be on the same interface!
       *)
      2: { simpl; exact: H5. }
      2: { rewrite /Comp_locs.
           rewrite /Aux_locs in H3. exact H3.
           (* rewrite fdisjointUr; apply/andP; split; assumption.*) }
      rewrite GRing.addr0.
      rewrite /Aux_Prim_ideal.
      by [rewrite (* -Advantage_link *) Advantage_sym].
    Qed.

  End RemoteAttestation.

  (* ############################################################################################## *)
  (* ############################################################################################## *)
  (* ############################################################################################## *)

  Module Type RemoteAttestationHash
  (π1 : SignatureParams)
  (π2 : RemoteAttestationParams)
  (π3 : SignatureAlgorithms π1 π2)
  (π4 : RemoteAttestationAlgorithms π1 π2 π3)
  (π5 : SignaturePrimitives π1 π2 π3).

  Import π1 π2 π3 π4 π5.

  Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
  Definition Attestation_locs_ideal := Attestation_locs_real :|: fset [:: attest_loc ].

  Definition Att_interface := [interface
  #val #[get_pk] : 'unit → 'pubkey ;
  #val #[attest] : 'challenge → ('signature × 'message) ;
  #val #[verify_att] : ('challenge × 'signature) → 'bool
  ].

  Definition Att_real : package Attestation_locs_real [interface] 
    Att_interface
  := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    };

    #def #[attest] (chal : 'challenge) : ('signature × 'message)
    {
      state ← get state_loc ;;
      let (sk,pk) := KeyGen in
    (*
    '(sk,pk) ← KeyGen ;;
    *)
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let msg := Hash state chal in
      let att := Sign sk msg in
      ret (att, msg)
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
  
  Definition attest_loc  : Location := ('set (Signature × chMessage × chState × chChallenge) ; 2%N).


  Equations Att_ideal : package Attestation_locs_ideal [interface] Att_interface :=
  Att_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };

    #def #[attest] (chal : 'challenge) : ('signature × 'message)
    {
      A ← get attest_loc ;;
      state ← get state_loc ;;
      let (sk,pk) := KeyGen in
      (*
      '(sk,pk) ← KeyGen ;;
      *)
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let msg := Hash state chal in
      let att := Sign sk msg in
      #put attest_loc := setm A (att, msg, state, chal) tt ;;
      ret (att, msg)
    };

    #def #[verify_att] ('(chal, att) : ('challenge × 'attest)) : 'bool
    {
      A ← get attest_loc ;;
      state ← get state_loc ;;
      let msg := Hash state chal in 
      let b :=  (att, msg, state, chal) \in domm A in
      ret b
    }
  ].
  Next Obligation.
    ssprove_valid; rewrite /Attestation_locs_ideal/Attestation_locs_real in_fsetU; apply /orP.
    1,3,7: right; auto_in_fset.
    all: left; auto_in_fset.
  Defined.

  (* We need a common interface, so we need to define an [AUX] for the
     signature scheme.
  Definition Aux_locs := fset [:: pk_loc  ; state_loc ]. *)

  Definition Aux_locs := fset [:: pk_loc ; sk_loc ; sign_loc ; state_loc ].

  Definition Aux : package Aux_locs Prim_interface Att_interface :=
  [package
    #def #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };

    #def #[attest] ( chal : 'challenge ) : ('signature × 'message)
    {
      #import {sig #[sign] : 'message  → 'signature } as sign ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      att ← sign msg ;;
      ret (att, msg)
    };

    #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
    {
      #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      b  ← verify (att,msg) ;;
      ret b
    }
  ].

  Lemma sig_real_vs_att_real:
    Att_real ≈₀ Aux ∘ Prim_real.
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

  Definition Comp_locs := fset [:: pk_loc; sk_loc ; sign_loc ; state_loc ].

  (* You need to redefine [Aux] to match the import interface of [Aux] to
     the export interface of [Prim_ideal]  *)
  Definition Aux_ideal : package Aux_locs Prim_interface_f Att_interface :=
  [package
    #def #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };

    #def #[attest] ( chal : 'challenge ) : ('signature × 'message)
    {
      #import {sig #[sign_f] : 'message  → 'signature } as sign ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      att ← sign msg ;;
      ret (att, msg)
    };

    #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
    {
      #import {sig #[verify_sig_f] : ('signature × 'message) → 'bool } as verify ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      b  ← verify (att,msg) ;;
      ret b
    }
  ].

  Definition Prim_real_locp := {locpackage Prim_real}.
  Definition Prim_ideal_locp := {locpackage Prim_ideal}.
  Definition Att_real_locp := {locpackage Att_real}.
  Definition Att_ideal_locp := {locpackage Att_ideal}.


  Equations Aux_Prim_ideal : package Comp_locs [interface] Att_interface :=
    Aux_Prim_ideal := {package Aux_ideal ∘ Prim_ideal_locp}.
  Next Obligation.
    ssprove_valid.
    - rewrite /Aux_locs/Comp_locs.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - rewrite /(locs Prim_ideal_locp)/Comp_locs. 
      rewrite [X in fsubset _ X]fset_cons.
      unfold Prim_locs_ideal.
      rewrite fset_cons.
      apply fsetUS.
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
  Defined.

  Lemma sig_ideal_vs_att_ideal :
    Att_ideal_locp ≈₀ Aux_Prim_ideal.
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
      fdisjoint LA (Prim_real_locp).(locs) →
      fdisjoint LA (Prim_ideal_locp).(locs) →
      fdisjoint LA Aux_locs →
      fdisjoint LA (Att_real_locp).(locs) →
      fdisjoint LA (Att_ideal_locp).(locs) →
      (AdvantageE Att_ideal_locp Att_real_locp A <= AdvantageE Aux_Prim_ideal (Aux ∘ Prim_real_locp) A)%R.
  Proof.
    move => va H1 H2 H3 H4 H5.
    rewrite Advantage_sym.
    simpl in H1.
    simpl in H2.
    simpl in H3.
    simpl in H4.
    simpl in H5.
    ssprove triangle (Att_real_locp) [::
      Aux ∘ Prim_real_locp ;
      Aux_ideal ∘ Prim_ideal_locp
      ] (Att_ideal_locp) A as ineq.
    eapply le_trans.
    1: { exact: ineq. }
    clear ineq.
    rewrite sig_real_vs_att_real.
    2: simpl; exact: H4.
    2: {
      simpl.
      rewrite fdisjointUr.
      apply/andP; split; assumption.
    }
    rewrite GRing.add0r.
    rewrite [X in (_ + X <= _)%R]Advantage_sym.

    (* Set Typeclasses Debug Verbosity 2. *)

    rewrite sig_ideal_vs_att_ideal.
    (* Type class resolution failed because of the [Att_interface_f].
       Both advantages need to be on the same interface!
     *)
    2: { simpl; exact: H5. }
    2: { rewrite /Comp_locs.
         rewrite /Aux_locs in H3. exact H3.
         (* rewrite fdisjointUr; apply/andP; split; assumption.*) }
    rewrite GRing.addr0.
    rewrite /Aux_Prim_ideal.
    by [rewrite (* -Advantage_link *) Advantage_sym].
  Qed.

End RemoteAttestationHash.



End HeapHash.




