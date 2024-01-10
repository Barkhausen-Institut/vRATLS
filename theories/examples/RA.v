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
Require Import extructurespp.ord.
Require Import extructurespp.fmap.

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

    Parameter Collision_Resistence: injective (uncurry Hash).

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
    Definition Aux_locs := fset [:: pk_loc ; state_loc ].


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
    Definition Aux_ideal : package Aux_locs Prim_interface Att_interface :=
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
        rewrite !fset_cons.
        apply fsubsetU ; apply /orP ; right.
        rewrite fsubUset ; apply /andP ; split.
        -- apply fsubsetU ; apply /orP ; right.
           apply fsubsetU ; apply /orP ; left.
           apply fsubsetxx.
        -- apply fsubsetU ; apply /orP ; right.
           apply fsubsetU ; apply /orP ; right.
           apply fsubsetxx.
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
           rewrite /Aux_locs in H3.
           rewrite /Prim_locs_real in H1.
           rewrite /Prim_locs_ideal in H2.
           move: H3; rewrite fset_cons fdisjointUr; move/andP; case => disjoint_pk_loc disjoint_state_loc.
           move: H2; rewrite fset_cons fdisjointUr; move/andP; case => _.
           rewrite fset_cons fdisjointUr; move/andP; case => disjoint_sk_loc disjoint_sign_loc.
           repeat (rewrite fset_cons fdisjointUr; apply/andP; split; try assumption).
           rewrite fset1E; assumption.
      }
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

    Definition attest_loc_long  : Location := ('set (Signature × chState × chChallenge) ; 2%N).

    Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
    Definition Attestation_locs_ideal := Attestation_locs_real :|: fset [:: attest_loc_long ].

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
        state ← get state_loc ;;
        let (sk,pk) := KeyGen in
        (*
        '(sk,pk) ← KeyGen ;;
        *)
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash state chal in
        let att := Sign sk msg in
        A ← get attest_loc_long ;;
        #put attest_loc_long := setm A (att, state, chal) tt ;;
        ret (att, msg)
      };

      #def #[verify_att] ('(chal, att) : ('challenge × 'attest)) : 'bool
      {
        A ← get attest_loc_long ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        let b :=  (att, state, chal) \in domm A in
        ret b
      }
    ].
    Next Obligation.
      ssprove_valid; rewrite /Attestation_locs_ideal/Attestation_locs_real in_fsetU; apply /orP.
      1,6,7: right; auto_in_fset.
      all: left; auto_in_fset.
    Defined.

    (* We need a common interface, so we need to define an [AUX] for the
       signature scheme.*)
    Definition Aux_locs := fset [:: pk_loc  ; state_loc ].

    (*Definition Aux_locs := fset [:: pk_loc ; sk_loc ; sign_loc ; state_loc ]. *)

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
  
    Definition Comp_locs := fset [:: pk_loc; sk_loc ; state_loc ; sign_loc ].

    (* You need to redefine [Aux] to match the import interface of [Aux] to
       the export interface of [Prim_ideal]  *)
    Definition Aux_ideal : package Aux_locs Prim_interface Att_interface :=
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
        rewrite !fset_cons.
        apply fsubsetU ; apply /orP ; right.
        apply fsetUS.
        apply fsubsetU ; apply /orP ; right.
        apply fsubsetxx.
      - rewrite /(locs Prim_ideal_locp)/Comp_locs.
        rewrite [X in fsubset _ X]fset_cons.
        unfold Prim_locs_ideal.
        rewrite fset_cons.
        apply fsetUS.
        rewrite [X in fsubset _ X]fset_cons.
        rewrite !fset_cons.
        apply fsetUS.
        apply fsubsetU ; apply /orP ; right.
        apply fsetUS.
        apply fsubsetxx.
    Defined.

    Definition Att_ideal_locp_heap := Attestation_locs_ideal.
    Definition Aux_prim_ideal_heap := Comp_locs.

    Definition attest_set := 'set (Signature × chState × chChallenge).
    Definition sign_set := 'set ('signature × 'message).

    (* Normally, this would be located in a Functor.
       This is just [fmap] on a tuple.
     *)
    Definition pair_fmap {S T T':Type} (f: T -> T') : (T * S) -> (T' * S) :=
      λ '(t,s), (f t,s).

    Lemma second_id : forall S T T' (f: T -> T') (t:T * S), snd (pair_fmap f t) = snd t.
    Proof.
      by [move => S T T' f; case => a b].
    Qed.

    Require Import extructures.fmap.

    Definition fmap_kmap' {S} {T T':ordType} (f: T->T') (m:{fmap T -> S}) : {fmap T' -> S} :=
      mapm2 f id m.

    Definition hash_eq (a_loc : Value attest_loc_long.π1) (s_loc : Value sign_loc.π1) : Prop :=
      (fmap_kmap'
         (fun t =>
            match t with
            | (sig, state, challenge) => (sig, Hash state challenge)
            end)
         a_loc) = s_loc.

    Definition full_heap_eq : precond  :=
      λ '(s0, s1),
        get_heap s0 pk_loc = get_heap s1 pk_loc /\
          get_heap s0 sk_loc = get_heap s1 sk_loc /\
          get_heap s0 state_loc = get_heap s1 state_loc /\
          hash_eq (get_heap s0 attest_loc_long) (get_heap s1 sign_loc) /\
          (forall {l:Location}, l \notin Attestation_locs_ideal → l \notin Comp_locs → get_heap s0 l = get_heap s1 l).

  (*
    Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
    tion Attestation_locs_ideal := Attestation_locs_real :|: fset [:: attest_loc ].

    Definition attest_loc_long  : Location := ('set (Signature × chState × chChallenge) ; 2%N).
    Definition sign_loc    : Location := ('set ('signature × 'message); 2%N).
  *)
  (*
  ch_Message (from sign_loc) = Hash(State, Challenge) (from att_long_loc)
  *)

    Lemma disjoint_noteq:
      forall {T:ordType} {l0} {L0: {fset T}}, l0 \notin L0 -> forall {l0'}, l0' \in L0 -> l0 != l0'.
    Proof.
      move => T l L H l'.
      move: H; elim/fset_ind: L.
      - by [].
      - move => x s x_notin_s iH.
        move/fsetU1P.
        rewrite boolp.not_orP.
        case; move/eqP => l_not_x.
        move/negP => l_notin_s.
        move/fsetU1P. case.
        + by [move => l'_eq_x; rewrite l'_eq_x].
        + move => l'_in_s; apply: (iH l_notin_s l'_in_s).
    Qed.


  Lemma INV'_full_heap_eq:
    INV' Attestation_locs_ideal Comp_locs full_heap_eq.
  Proof.
    split.
    - rewrite /full_heap_eq;
        case => pk_loc_eq;
        case => sk_loc_eq;
        case => state_loc_eq;
        case => attest_loc_eq other_eq l notin_att_locs notin_comp_locs.
      case in_att_locs: (l \in Attestation_locs_ideal).
      + move: in_att_locs; move/idP => in_att_locs.
        move: notin_att_locs; move/negP => //=.
      + case in_comp_locs: (l \in Comp_locs).
        * move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
        * clear in_att_locs; clear in_comp_locs.
          apply (other_eq _ notin_att_locs notin_comp_locs).
    - rewrite /full_heap_eq;
        case => pk_loc_eq;
        case => sk_loc_eq;
        case => state_loc_eq;
        case => attest_loc_eq other_eq l v notin_att_locs notin_comp_locs.
      repeat split.
      + case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have pk_loc_in_att_locs: pk_loc \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               left; auto_in_fset.
             }
             have pk_not_eq_l: pk_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs pk_loc_in_att_locs). }
             by [do 2! rewrite (get_set_heap_neq _ _ _ _ pk_not_eq_l)].
      + (* same as above but for  [sk_loc] *)
        case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have sk_loc_in_att_locs: sk_loc \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               left; auto_in_fset.
             }
             have sk_not_eq_l: sk_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs sk_loc_in_att_locs). }
             by [do 2! rewrite (get_set_heap_neq _ _ _ _ sk_not_eq_l)].
      + (* same as above but for  [state_loc] *)
        case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have state_loc_in_att_locs: state_loc \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               left; auto_in_fset.
             }
             have state_not_eq_l: state_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs state_loc_in_att_locs). }
             by [do 2! rewrite (get_set_heap_neq _ _ _ _ state_not_eq_l)].
      + (* same as above but for [attest_loc_long] and [sign_loc] *)
        case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have attest_loc_in_att_locs: attest_loc_long \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               right; auto_in_fset.
             }
             have attest_not_eq_l: attest_loc_long != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs attest_loc_in_att_locs). }
             have sign_loc_in_comp_locs: sign_loc \in Comp_locs.
             { clear; rewrite /Comp_locs; auto_in_fset. }
             have sign_not_eq_l: sign_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_comp_locs sign_loc_in_comp_locs). }
             by [rewrite (get_set_heap_neq _ _ _ _ attest_not_eq_l) (get_set_heap_neq _ _ _ _ sign_not_eq_l)].
      + move => l' l'_notin_att_locs l'_notin_comp_locs.
        case E: (l==l').
        * move: E; move/eqP => l_eq_l'.
          rewrite -l_eq_l'.
          by [do 2! (rewrite get_set_heap_eq)].
        * move: E; move/negP/idP; rewrite eqtype.eq_sym => l_neq_l'.
          do 2! rewrite (get_set_heap_neq _ _ _ _ l_neq_l').
          apply: (other_eq l' l'_notin_att_locs l'_notin_comp_locs).
  Qed.

  Lemma Invariant_heap_eq_ideal:
    Invariant Attestation_locs_ideal Comp_locs full_heap_eq.
  Proof.
    split.
    - by [apply INV'_full_heap_eq].
    - by [].
  Qed.

  #[export] Hint Extern 10 (Invariant Attestation_locs_ideal Comp_locs full_heap_eq) =>
    eapply Invariant_heap_eq_ideal
    : typeclass_instances ssprove_invariant.

  Definition full_heap_eq' : precond  :=
    λ '(s0, s1),
        hash_eq (get_heap s0 attest_loc_long) (get_heap s1 sign_loc) /\
          (forall {l:Location}, l \notin (fset [:: attest_loc_long ; sign_loc]) → get_heap s0 l = get_heap s1 l).

  Lemma att_loc_in : attest_loc_long \in fset [:: attest_loc_long; sign_loc].
  Proof. auto_in_fset. Qed.

  Lemma sign_loc_in : sign_loc \in fset [:: attest_loc_long; sign_loc].
  Proof. auto_in_fset. Qed.

  (* TODO generalize *)
  Lemma not_in_diff: forall l,
      l \notin Attestation_locs_ideal ->
      l \notin Comp_locs ->
      l \notin (fset [:: attest_loc_long ; sign_loc]).
  Proof.
    move => l h1 h2.
    rewrite -fdisjoints1.
    apply (@fdisjoint_trans _
             (fset [:: attest_loc_long; sign_loc])
             (Attestation_locs_ideal :|: Comp_locs)
             (fset1 l)
          ).
    2: {
      rewrite fdisjointC fdisjointUr.
      apply/andP; split; by [rewrite fdisjoint1s].
    }
    rewrite fset_cons.
    apply fsetUSS.
    - rewrite /Attestation_locs_ideal fset1E.
      apply fsubsetUr.
    - rewrite /Comp_locs -fset1E fsub1set.
      auto_in_fset.
  Qed.

  Lemma INV'_full_heap_eq'_get : forall s1 s2,
      full_heap_eq' (s1, s2) ->
      ∀ l : tag_ordType (I:=choice_type_ordType) (λ _ : choice_type, nat_ordType),
        l \notin Attestation_locs_ideal ->
        l \notin Comp_locs ->
        get_heap s1 l = get_heap s2 l.
  Proof.
    move => s1 s2.
    rewrite /full_heap_eq;
      case => attest_loc_eq other_eq l notin_att_locs notin_comp_locs.
    case in_att_locs: (l \in Attestation_locs_ideal).
    + move: in_att_locs; move/idP => in_att_locs.
      move: notin_att_locs; move/negP => //=.
    + case in_comp_locs: (l \in Comp_locs).
      * move: in_comp_locs; move/idP => in_comp_locs.
        move: notin_comp_locs; move/negP => //=.
      * clear in_att_locs; clear in_comp_locs.
        apply (other_eq _ (not_in_diff _ notin_att_locs notin_comp_locs)).
  Qed.

  Lemma INV'_full_heap_eq'_get_set : forall s1 s2,
      full_heap_eq' (s1, s2) ->
      ∀ (l : tag_ordType (I:=choice_type_ordType) (λ _ : choice_type, nat_ordType)) (v : Value l.π1),
        l \notin Attestation_locs_ideal ->
        l \notin Comp_locs ->
        full_heap_eq' (set_heap s1 l v, set_heap s2 l v).
  Proof.
    move => s1 s2.
    rewrite /full_heap_eq';
        case => attest_loc_eq other_eq l v notin_att_locs notin_comp_locs.
      repeat split.
      + case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have attest_loc_in_att_locs: attest_loc_long \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               right; auto_in_fset.
             }
             have attest_not_eq_l: attest_loc_long != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs attest_loc_in_att_locs). }
             have sign_loc_in_comp_locs: sign_loc \in Comp_locs.
             { clear; rewrite /Comp_locs; auto_in_fset. }
             have sign_not_eq_l: sign_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_comp_locs sign_loc_in_comp_locs). }
             by [rewrite (get_set_heap_neq _ _ _ _ attest_not_eq_l) (get_set_heap_neq _ _ _ _ sign_not_eq_l)].
      + move => l' l'_notin_diff_locs.
        case E: (l==l').
        * move: E; move/eqP => l_eq_l'.
          rewrite -l_eq_l'.
          by [do 2! (rewrite get_set_heap_eq)].
        * move: E; move/negP/idP; rewrite eqtype.eq_sym => l_neq_l'.
          do 2! rewrite (get_set_heap_neq _ _ _ _ l_neq_l').
          apply: (other_eq l' l'_notin_diff_locs).
  Qed.

  Lemma INV'_full_heap_eq':
    INV' Attestation_locs_ideal Comp_locs full_heap_eq'.
  Proof.
    split.
    - apply INV'_full_heap_eq'_get.
    - apply INV'_full_heap_eq'_get_set.
  Qed.

  Lemma Invariant_heap_eq_ideal':
    Invariant Attestation_locs_ideal Comp_locs full_heap_eq'.
  Proof.
    split.
    - by [apply INV'_full_heap_eq'].
    - by [].
  Qed.

  #[export] Hint Extern 10 (Invariant Attestation_locs_ideal Comp_locs full_heap_eq') =>
    eapply Invariant_heap_eq_ideal'
    : typeclass_instances ssprove_invariant.

  Lemma get_pre_cond_full_heap:
    ∀ (ℓ : tag_ordType (I:=choice_type_ordType) (λ _ : choice_type, nat_ordType))
      (L: {fset Location}),
      (fdisjoint (fset [:: attest_loc_long; sign_loc]) L) ->
      ℓ \in L ->
      get_pre_cond ℓ full_heap_eq'.
  Proof.
    move => ℓ L h_disjoint l_in_L.
    rewrite /get_pre_cond => s₀ s₁ h_full_heap_eq.
    apply h_full_heap_eq.
    move: h_disjoint; rewrite fdisjointC; move/fdisjointP; move => h_disjoint.
    apply (h_disjoint ℓ l_in_L).
  Qed.

  #[export] Hint Extern 10 (get_pre_cond _ full_heap_eq') =>
    eapply get_pre_cond_full_heap
    : ssprove_invariant.


  Lemma put_pre_cond_full_heap:
    ∀ (ℓ : tag_ordType (I:=choice_type_ordType) (λ _ : choice_type, nat_ordType))
      (v : Value ℓ.π1)
      (L: {fset Location}),
      (fdisjoint (fset [:: attest_loc_long; sign_loc]) L) ->
      ℓ \in L -> put_pre_cond ℓ v full_heap_eq'.
  Proof.
    move => ℓ v L h_disjoint l_in_L.
    rewrite /put_pre_cond/full_heap_eq' => s₀ s₁ h_full_heap_eq.
    have h_disjoint' := h_disjoint.
    move: h_disjoint'; rewrite fdisjointC; move/fdisjointP; move => h_notin.
    have l_in_L' := l_in_L.
    move: l_in_L'; move/h_notin. move/disjoint_noteq => l_neq_att_sign.
    case: h_full_heap_eq => full_heap_left full_heap_right.
    split.
    - have l_neq_att_loc := l_neq_att_sign attest_loc_long att_loc_in.
      rewrite eqtype.eq_sym in l_neq_att_loc.
      rewrite (get_set_heap_neq _ _ _ _ l_neq_att_loc).

      have l_neq_sign_loc := l_neq_att_sign sign_loc sign_loc_in.
      rewrite eqtype.eq_sym in l_neq_sign_loc.
      rewrite (get_set_heap_neq _ _ _ _ l_neq_sign_loc).

      apply full_heap_left.
    - move => l l_notin_att_sign.
      case E: (ℓ == l).
      + move/eqP in E.
        by [rewrite -E; repeat rewrite get_set_heap_eq].
      + move/eqP in E.
        (* Why is the below so hard?! *)
        have X: ℓ <> l /\ (true = true) := conj E erefl.
        move/predD1P in X.
        rewrite Bool.andb_true_r eqtype.eq_sym in X.

        repeat rewrite (get_set_heap_neq _ _ _ _ X).
        apply: (full_heap_right _ l_notin_att_sign).
  Qed.

  #[export] Hint Extern 10 (put_pre_cond _ _ full_heap_eq') =>
    eapply put_pre_cond_full_heap
    : ssprove_invariant.

  Lemma size_length_eq: forall A (l: seq.seq A),
      size l = length l.
  Proof.
    by [].
  Qed.

  Lemma map_size T T' (f: T->T') (l: seq.seq T):
      size (map f l) = size l.
  Proof.
    repeat rewrite size_length_eq; apply: map_length.
  Qed.

  Lemma fmap_kmap_setm {S} {T T': ordType}:
    forall (f: T -> T') (k:T) (v:S) (m: {fmap T -> S}),
      (* k \notin domm m -> *)
      injective f -> (* if this is bijective then I would not end up in omap! *)
      fmap_kmap' f (setm m k v) = setm (fmap_kmap' f m) (f k) v.
  Proof.
    Print fmap_kmap'.
    move => f k v m inj_f.
    rewrite /fmap_kmap'.
    Fail rewrite [X in _ = setm _ X]mapm2E.
    (* TODO *)
    Check eq_fmap.
    (* rewrite -eq_fmap. *)
    Locate "=1".
    Print eqfun.

   (** * Approach 1:

    elim/fmap_ind H: (setm m k v) => [|m0 iH k0 v0 k0_notin].
    - admit.
    - rewrite -iH. f_equal.

      Using the
        [iH : mapm2 (T:=T) (T':=T') f id m0 = setm (T:=T') (mapm2 (T:=T) (T':=T') f id m) (f k) v]
      works here but the [iH] looks strange and so does the goal then:
        [setm (T:=T) m0 k0 v0 = m0]
      I can only prove this if I would have that
        [m0 k0 = v0].
      But that is certainly not the case:
        [k0_notin : k0 \notin domm (T:=T) (S:=S) m0].
      *)

    (** * Approach 2:

    move: k v.
    elim/fmap_ind H: m => [|m0 iH k0 v0 k0_notin].
    - by [].
    - move => k v.

      The induction hypothesis looks good:
       [iH : ∀ (k : T) (v : S),
         mapm2 (T:=T) (T':=T') f id (setm (T:=T) m0 k v) = setm (T:=T') (mapm2 (T:=T) (T':=T') f id m0) (f k) v]
      but I did not really gain anything towards my goal:
       [mapm2 (T:=T) (T':=T') f id (setm (T:=T) (setm (T:=T) m0 k0 v0) k v) =
          setm (T:=T') (mapm2 (T:=T) (T':=T') f id (setm (T:=T) m0 k0 v0)) (f k) v]
      I just added another [setm].
      I could say now that [case: k0 == k].
      But even that would not buy me anything because
        [k0_notin : k0 \notin domm (T:=T) (S:=S) m0]
      only talks about [m0] so I would have to cover both cases.
     *)


    (** * Possible inductions via [seq]: *)

    rewrite /mapm2.

    (** * Approach 3:

    elim: (FMap.fmval m).
    2 goals (ID 30990)

    S : Type
    T, T' : ordType
    f : T -> T'
    k : T
    v : S
    m : {fmap T -> S}
    inj_f : injective f
    ============================
    mkfmap (T:=T') [seq (f p.1, p.2) | p <- setm (T:=T) m k v] =
    setm (T:=T') (mkfmap (T:=T') [seq (f p.1, p.2) | p <- [::]]) (f k) v

  goal 2 (ID 30991) is:
   ∀ (a : T * S) (l : seq.seq (T * S)),
     mkfmap (T:=T') [seq (f p.1, p.2) | p <- setm (T:=T) m k v] =
     setm (T:=T') (mkfmap (T:=T') [seq (f p.1, p.2) | p <- l]) (f k) v ->
     mkfmap (T:=T') [seq (f p.1, p.2) | p <- setm (T:=T) m k v] =
     setm (T:=T') (mkfmap (T:=T') [seq (f p.1, p.2) | p <- a :: l]) (f k) v

     This does not work either because it covers only the RHS of the equality.
     The LHS has [FMap.fmval (setm (T:=T) m k v)].

     *)

    (** * Approach 4:
        I get around the problem of approach 3 using the path
        of the proof for [mapm2E] which basically throws away the ordering proof by destructuring the map [m].
        Then, I can just do the induction on the sequence [m] and it works on both sides of the equality.
     *)

    case: m => [/= m _].
    move: k v.
    elim: m => [k v |[x' y] m IH k v].
    - by [].
    - (* Unset Printing Notations. *)

      rewrite [in RHS]/seq.map.
      move => //=.
      rewrite -/(setm_def (T:=T) ((x', y) :: m) k v).
      rewrite -[in RHS]/(seq.map _ m).
      case E: (x' == k).
      + move: E; move/eqP => E.
        rewrite E.
        rewrite setmxx.
        rewrite -IH.

        (* TODO move into own lemmas *)

        rewrite (@setm_def_seq_cons_eq' _ _ _ _ y).
        move => //=.
        rewrite ifF /=.
        * rewrite ifT //= ifF /=.
          ** rewrite ifT //=.
          ** apply: Ord.ltxx.
        * apply: Ord.ltxx.
      + move: E; move/eqP => E.
        move => //=.
        case k_lt_x': (k < x')%ord.
        * by [].
        * move/eqP/negPf: E; rewrite eqtype.eq_sym => E; rewrite ifF //=.
          rewrite setmC.
          ** f_equal. exact: IH.
          ** rewrite /injective in inj_f.
             (* TODO lift/move into lemma *)
             have neq_inj a b (inj_f': injective f) (a_neq_b: a != b) : f a != f b.
             1: {
               case H: (f a == f b) => //=.
               move/eqP/(inj_f' a b):H => a_eq_b.
               rewrite a_eq_b in a_neq_b.
               move/negPf: a_neq_b => b_neq_b; rewrite -b_neq_b //=.
             }
             move/eqP/eqP: E; rewrite eqtype.eq_sym => x'_neq_k.
             exact: (neq_inj x' k inj_f x'_neq_k).
  Qed.

  Definition prod_dist (A B C : Type) (n: A*B*C) : (A*(B*C)) :=
    let (m,c) := n in let (a,b) := m in (a,(b,c)).

  Lemma pair_dist_eq {A B C : Type} {a0 a1: A} {b0 b1: B} {c0 c1: C}:
    (a0,(b0,c0)) = (a1,(b1,c1)) ->
    (a0,b0,c0) = (a1,b1,c1).
  Proof.
    move/pair_equal_spec; case => a0_eq_a1.
    move/pair_equal_spec => [b0_eq_b1 c0_eq_c1].
    have x := conj a0_eq_a1 b0_eq_b1.
    rewrite -pair_equal_spec in x.
    have y := conj x c0_eq_c1.
    rewrite -pair_equal_spec in y.
    exact: y.
  Qed.

  Lemma preserve_mem_full_heap_eq:
    forall {sign_loc_val: Value sign_loc.π1} {att_loc_val: Value attest_loc_long.π1} state x y,
      preserve_update_mem
        [::
           hpv_r sign_loc
             (setm sign_loc_val (y, Hash state x) tt);
           hpv_l attest_loc_long
             (setm att_loc_val (y, state, x) tt)
        ]
        [:: hpv_r sign_loc sign_loc_val; hpv_l attest_loc_long att_loc_val]
        full_heap_eq'.
    move => sign_loc_val att_loc_val state x y.
    rewrite /preserve_update_mem/remember_pre => s0 s1 h.
    rewrite /full_heap_eq' //=.
    split.
    - move: h; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; move => hasheq heq att_loc_mem sign_loc_mem.
      do 2! rewrite get_set_heap_eq.
      rewrite /hash_eq.
      (* At this point, we are at the core of the whole proof.
         we need to reason now about the map function.
         [hasheq] is my precondition which says:
         The values stored at [attest_loc_long] and [sign_loc] are [hash_eq] equal.
         Now I need to show that this property is preserved when adding new values.
         The proof is by induction on the values of [att_loc_val] and [sign_loc].
         This becomes clear when unfolding [map].
       *)
      Fail elim: (setm att_loc_val (y,state, x) tt).
      (* The challenge is to cancel the empty map case because the map
         is obviously not empty!
       *)

      (*
      TODO: I need to find a way to rewrite the LHS into
      [ [:: (y, state,x , tt); att_loc_val] ].
      If I managed to do that then I can unfold [map] and simplify.

      This is not possible because the sequence is ordered.
      Hence it is not clear at which position [(y,state,x,tt) is located. ]
       *)

      (* Preserved. *)
      move: att_loc_mem.
      elim/fmap_ind H: att_loc_val => [|m iH key value].
      + move => att_loc_mem //=.
        (* Now I have to show that [sign_loc_val] is also empty. *)
        rewrite /rem_lhs in att_loc_mem.
        move: hasheq; rewrite /hash_eq att_loc_mem //= => hasheq.
        rewrite /rem_rhs in sign_loc_mem; rewrite sign_loc_mem in hasheq.
        by [rewrite -hasheq].
      + move => key_notin att_loc_mem.
        move: m iH H key_notin att_loc_mem  => initial_set iH H key_notin att_loc_mem.

        rewrite /rem_lhs in iH.
        rewrite /rem_lhs in att_loc_mem.

        (*
          At this point I'm stuck.
          I will never be able to use the [iH] because of [att_loc_mem].

          Another question is then:
          Can I even use the induction over fmap then?!
         *)

        Restart.

    move => sign_loc_val att_loc_val state x y.
    rewrite /preserve_update_mem/remember_pre => s0 s1 h.
    rewrite /full_heap_eq' //=.
    split.
    - move: h; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; move => hasheq heq att_loc_mem sign_loc_mem.
      rewrite /rem_lhs in att_loc_mem.
      move: hasheq; rewrite /hash_eq att_loc_mem //= => att_loc_sign_loc_eq.
      rewrite /rem_rhs in sign_loc_mem; rewrite sign_loc_mem in att_loc_sign_loc_eq.
      do 2! rewrite get_set_heap_eq.
      rewrite -att_loc_sign_loc_eq.

      apply: fmap_kmap_setm.
      move => [[sig1 state1] chal1] [[sig2 state2] chal2] //=.
      move => h.
      have Hash_inj_pair := Collision_Resistence (state1,chal1) (state2,chal2).
      move/pair_equal_spec:h => [sig1_eq_sig2 hash1_eq_hash2].
      apply: pair_dist_eq.
      apply/pair_equal_spec; split.
      + exact: sig1_eq_sig2.
      + exact: (Hash_inj_pair hash1_eq_hash2).
    - move => l l_notin.
      rewrite (get_set_heap_neq _ _ _ _ (disjoint_noteq l_notin att_loc_in)).
      rewrite (get_set_heap_neq _ _ _ _ (disjoint_noteq l_notin sign_loc_in)).
      move:h; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; move => _ other_heap_eq _ _.
      exact: (other_heap_eq l l_notin).
  Qed.

  Lemma l_in_lSet {l:Location}: l \in (fset [:: l]).
  Proof.
    auto_in_fset.
  Qed.

  Lemma get_eq_loc {l: Location} {t} {c1 c2: Value l.π1 -> raw_code t} :
    l \notin fset [:: attest_loc_long; sign_loc] ->
    (forall x:Value l.π1,
        ⊢ ⦃ full_heap_eq' ⦄
          c1 x ≈ c2 x
          ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀, s₁) ⦄) ->
    ⊢ ⦃ full_heap_eq' ⦄
    x1 ← get l ;; c1 x1 ≈ x2 ← get l ;; c2 x2
  ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀, s₁) ⦄.
  Proof.
    move => l_notin.
    eapply (rsame_head_cmd_alt (cmd_get l)).
    eapply (cmd_get_preserve_pre l full_heap_eq').
    ssprove_invariant.
    2: { apply (@l_in_lSet l). }
    rewrite -fset1E fdisjoints1.
    exact: l_notin.
  Qed.

  Ltac sync_sig_att :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
        lazymatch c with
(*        | x ← sample ?op ;; _ => eapply (rsame_head_cmd_alt (cmd_sample op)); [ eapply cmd_sample_preserve_pre |  ] *)
        | #put ?ℓ := ?v ;;  _ => eapply (rsame_head_cmd_alt (cmd_put ℓ v));
                                 [ eapply (cmd_put_preserve_pre ℓ full_heap_eq')
                                 | intros [] ]
                                   (* TODO look for the hypothesis in the context. *)
        | x ← get ?ℓ ;;  _ => eapply (@get_eq_loc ℓ)
(*        | x ← cmd ?c ;;     _ => eapply (rsame_head_cmd_alt c) *)
(*        | assertD ?b        _ => eapply (r_assertD_same A b) *)
        | _ => fail "No head found"
        end
    | |- _ => fail "The goal should be a syntactic judgment"
  end.

  (* To rewrite the post condition I need to "rewrite under binders".
     I could do so with setoid_rewrite: https://coq.inria.fr/refman/addendum/generalized-rewriting.html
     But the SSReflect approach to this seems once more much more intuitive to me:
     https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#rewriting-under-binders
   *)

  Import FunctionalExtensionality.
  Lemma post_eq:
    forall {t} {pre: precond} {l r: raw_code t} {post post' : postcond t t},
      (forall a b, post a b = post' a b) ->
      ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄ = ⊢ ⦃ pre ⦄ l ≈ r ⦃ post' ⦄.
  Proof.
    move => t pre l r post post' post_eq_post'.
    f_equal.
    do 2! apply functional_extensionality => ?.
    apply post_eq_post'.
  Qed.

  Lemma reshape_pair_id {T T0 T1 : Type} (f : T * T0 -> T1) : (fun '(pair x y) => f (pair x y)) = f.
  Proof.
    apply functional_extensionality; by [case].
  Qed.

  Lemma put_bind:
    forall (t : Choice.type) (l : Location) (v : l) (c : raw_code t),
      putr l v c = bind (putr l v (ret tt)) (fun (x:unit_choiceType) => c).
  Proof. by[]. Qed.

  Lemma sig_ideal_vs_att_ideal :
    Att_ideal_locp ≈₀ Aux_Prim_ideal.
  Proof.
    eapply eq_rel_perf_ind with (full_heap_eq').
    1: { apply: Invariant_heap_eq_ideal'. }
    simplify_eq_rel x.
    all: ssprove_code_simpl;
      rewrite -/full_heap_eq';
      (** approach 1:
       [ under @post_eq => [a b] do [ case: a => b₀ s₀; case: b => b₁ s₁; rewrite -/(full_heap_eq (s₀,s₁))]. ]
       *)
      (** approach 2:
      [under @post_eq => a b.
       1:{ case: a => b₀ s₀; case: b => b₁ s₁.
          rewrite -/(full_heap_eq (s₀,s₁)).
          by rewrite over. }]
       *)
      (* Both of the above approaches fail because the [over] tactic expects just rewrites.
         So we do it the slightly more inconvenient way and have to state what we want.
       *)
      rewrite (@post_eq _ _ _ _ _
                 (λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀,s₁))).
      2:{ case => b₀ s₀; case  => b₁ s₁. by [rewrite -/(full_heap_eq' (s₀,s₁))]. }
    - Fail ssprove_sync.
      sync_sig_att. 1: { auto_in_fset. }
      move => a; by [apply r_ret].
    - sync_sig_att. 1: { auto_in_fset. }
      move => state.
      rewrite put_bind.
      rewrite [in X in ⊢ ⦃ _ ⦄ _ ≈ X ⦃ _ ⦄ ]put_bind.
      (* The below fails because the post condition is [b₀ = b₁ /\ pre (s₀, s₁)]
         instead of [pre (s₀, s₁) /\ b₀ = b₁].
       *)
      Fail eapply (@rsame_head_cmd_alt
                     unit_choiceType
                     (tgt (attest, ('challenge, 'signature × 'message)))
                     _
                     _
                     (cmd_put pk_loc (nsnd KeyGen))
                     full_heap_eq post).
      eapply (rsame_head_alt_pre _ _ (λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀, s₁))).
      + eapply (rpost_weaken_rule _ (λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀,s₁))). (* Yet another way of rewriting the post condition. *)
        * eapply (@r_reflexivity_alt _ (fset [:: pk_loc]) full_heap_eq').
          ** ssprove_valid.
          ** move => l l_in_pk_loc; ssprove_invariant.
             rewrite -fset1E fdisjoints1; auto_in_fset.
          ** move => l l_in_pk_loc; ssprove_invariant.
             rewrite -fset1E fdisjoints1; auto_in_fset.
        * case => b0 s0; case => b1 s1.
          case => b_eq fh_eq; exact: (conj fh_eq b_eq).
      + (* TODO automation for puts is needed *)
        move => _.
        (*
        rewrite (@post_eq _ _ _ _ _
                   (λ '(b₀, s₀) '(b₁, s₁), full_heap_eq' (s₀,s₁) /\ b₀ = b₁)).
        2:{ case => b0 s0; case => b1 s1.
            rewrite [LHS]and_comm.
        }
        Sadly this fails for some strange setoid rewrite reason.
         *)
        eapply (rpost_weaken_rule _ (λ '(b₀, s₀) '(b₁, s₁), full_heap_eq' (s₀,s₁) /\ b₀ = b₁)).
        2: {case => b0 s0; case => b1 s1.
            case => b_eq fh_eq; exact: (conj fh_eq b_eq).
        }

        (* It is not clear to me why this still fails.
           Why do I need to take such a long way? *)
        Fail eapply (rsame_head_cmd_alt (cmd_put sk_loc (nfst KeyGen))).

        rewrite put_bind.
        rewrite [in X in ⊢ ⦃ _ ⦄ _ ≈ X ⦃ _ ⦄ ]put_bind.

        eapply rsame_head_alt_pre.
        1: { eapply (cmd_put_preserve_pre sk_loc _ full_heap_eq').
             ssprove_invariant; [ | apply (@l_in_lSet sk_loc) ].
             rewrite -fset1E fdisjoints1; auto_in_fset.
        }
        move => _.
        (* put done *)

        (* gets *)
        Fail eapply r_get_remember_lhs.
        (* I have to reshape the precondition into:
           [λ '(s0, s1), full_heap_eq' (s0, s1)]
         *)
        rewrite -(reshape_pair_id full_heap_eq').
        eapply r_get_remember_lhs => att_loc_val.
        eapply r_get_remember_rhs => sign_loc_val.
        (* gets done *)

        (* puts *)
        eapply r_put_lhs.
        eapply r_put_rhs.
        (* puts done *)

        ssprove_restore_mem.
        2: { eapply r_ret => s0 s1 set_vals.
             exact: (conj set_vals erefl).
        }

        (* normally: [ssprove_invariant] TODO *)
        rewrite /preserve_update_mem/remember_pre/update_heaps.
        apply: preserve_mem_full_heap_eq.
    - by [].
    - case: x => chal sig.
      ssprove_swap_lhs 0.

      sync_sig_att.
      1: { auto_in_fset. }
      move => state.

      rewrite -(reshape_pair_id full_heap_eq').
      eapply r_get_remember_lhs => att_loc_val.
      eapply r_get_remember_rhs => sign_loc_val.

      eapply r_ret => s0 s1 pre.
      split.
      + move:pre; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; rewrite /rem_lhs; case => [heq other_eq att_loc_val_eq].
        rewrite /rem_rhs => sign_loc_val_eq.
        repeat rewrite mem_domm.
        (* rewrite -att_loc_val_eq -sign_loc_val_eq. *)
        move: heq; rewrite /hash_eq/fmap_kmap'/mapm2.
        rewrite att_loc_val_eq sign_loc_val_eq.
        rewrite -eq_fmap /eqfun => heq.
        have heq' := (heq (sig, Hash state chal)).
        move: heq'; rewrite mkfmapE /=; move => heq'.

        (*
        have xxx:
          injective f ->
          getm_def [seq (f p.1, p.2) | p <- s] (f x) = getm_def [seq (p.1, p.2) | p <- s] x.

        have yyy:
          getm_def [seq (p.1, p.2) | p <- s] x = getm_def s x.
         *)

        admit.
      + admit.
    - by [].
  Admitted.


  (* TODO *)
  Lemma sig_ideal_vs_att_ideal_old :
    Att_ideal_locp ≈₀ Aux_Prim_ideal.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    - ssprove_sync_eq => pk_loc.
      by [apply r_ret].
    - ssprove_swap_lhs 0; ssprove_sync_eq => state.
      do 2! (ssprove_swap_lhs 0; ssprove_sync_eq).
      (*
      Definition attest_loc_long  : Location := ('set (Signature × chMessage × chState × chChallenge) ; 2%N).
      Definition sign_loc    : Location := ('set ('signature × 'message); 2%N).
      *)
      ssprove_sync_eq => sig.
      ssprove_sync_eq.
      by [apply r_ret].
    - case x => a b.
      ssprove_swap_lhs 0; ssprove_sync_eq => state.
      ssprove_sync_eq => sig.
      by [apply r_ret].
  Qed.

  (*
  Lemma sig_ideal_vs_att_ideal :
     Att_ideal_locp ≈₀ Aux_Prim_ideal. 
  Proof.
    apply eq_rel_perf_ind_ignore with (fset [:: attest_loc_long] ). 
    1: { 
    apply: fsubset_trans.
    - by apply fsubsetUl.
    - rewrite -fset1E / Comp_locs / Attestation_locs_ideal / Attestation_locs_real.

      rewrite -fset1E / locpackage Att_ideal.
    (*
    We have:
    "fsubset (fset [:: attest_loc_long] :|: ?s2)
       (locs Att_ideal_locp :|: Comp_locs)"
    where
    )
      Definition Att_ideal_locp := {locpackage Att_ideal}.
    where Att_ideal uses
      Definition Attestation_locs_ideal 
          := Attestation_locs_real :|: fset [:: attest_loc_long ].
    where:
      Definition attest_loc_long  : Location 
          := ('set (Signature × chMessage × chState × chChallenge) ; 2%N).
      Definition Attestation_locs_real 
          := fset [:: pk_loc ; sk_loc; state_loc ].
    ------------------------------------------------------------------
    => it is a subset
    *)
    }
    
    - rewrite -fset1E / Comp_locs /attest_loc_long. rewrite !fset_cons.
      rewrite fsub1set.
  Qed.
  *)

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

  *)

End RemoteAttestationHash.
End HeapHash.




