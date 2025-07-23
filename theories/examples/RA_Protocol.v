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

From vRATLS Require Import examples.Signature.
From vRATLS Require Import examples.RA.
From vRATLS Require Import examples.Sig_Prot.
From vRATLS Require Import examples.RA_Facts.
(*Import SignatureProt.
Export SignatureProt. *)

Module Protocol
  (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KGc)
  (RAA : RemoteAttestationAlgorithms π1 π2 KGc)
  (RAH : RemoteAttestationHash π1 π2 KGc Alg RAA).

  Module π3 := RemoteAttestationParams π1.
  Module SP := SignaturePrimitives π1 π2 KGc Alg.
  Module SigProt := SignatureProt π1 π2 KGc Alg.
  Module Unforge := Unforgability π1 π2 KGc Alg RAA RAH.
  Import π1 π2 π3 KGc Alg RAA RAH SP SigProt Unforge.
  Import KGc.KGP SP.KG.
 
  Definition i_chal := #|Challenge|.
  Definition ra_protocol : nat := 50.
  
  Definition RA_prot_interface := 
    [interface #val #[ra_protocol] : 'challenge → 'pubkey × ('signature × 'bool) ].

  Definition Aux_locs_prot := fset [:: state_loc].
  
(****** For Ideal *******)
Definition AuxPrim_ideal : 
  package 
    Aux_locs_prot
    Sig_ifce 
    Att_interface :=
    [package
      #def #[get_pk_att] (_ : 'unit) : 'pubkey
      {
        #import {sig #[get_pk] : 'unit  → 'pubkey } as get_pk ;;
        pk ← get_pk tt ;;
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


(** The "Att_prot_ideal" is defined in a way that the adv has access & 
    can selecet the chall or we can say that it can influnce the protocol. 
    So that's why chall is derived from the adversary's input msg  **)

Definition Att_prot_locs_real := Sig_locs_real :|: Aux_locs_prot.
Definition Att_prot_locs_ideal := Sig_locs_ideal :|: Aux_locs_prot.


(****** For Real *******)

Definition AuxPrim_real : 
  package 
    Aux_locs_prot
    Sig_ifce 
    Att_interface :=
    [package
      #def #[get_pk_att] (_ : 'unit) : 'pubkey
      {
        #import {sig #[get_pk] : 'unit  → 'pubkey } as get_pk ;;
        
        pk ← get_pk tt ;;
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

Equations Att_prot : 
  package 
    (*Attestation_locs_real*) 
    Aux_locs_prot
    Att_interface 
    RA_prot_interface
    := 
    Att_prot :=
    [package
      #def  #[ra_protocol] (chal : 'challenge) : 'pubkey × ('signature × 'bool) 
      {
        #import {sig #[get_pk_att] : 'unit →  'pubkey } as get_pk_att ;;
        #import {sig #[attest] : 'challenge → ('signature × 'message)  } as attest ;;
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;

        pk ← get_pk_att tt ;;                       (* Get the public key *)
        '(att, _) ← attest chal ;;                (* Generate an attestation for the chall *)
        bool ← verify_att (chal, att) ;;            (* Verify the attestation *)
        ret (pk, (att, bool)) 
      } 
  ].  
  
  (****** Equations for Ideal 
  Note: Aux_locs: is the set of memory locations 
  used by the composed package. 
  Also, it is a superset of the memory locations 
  required by AuxPrim_ideal, Sig_ideal_c, and Att_prot_ideal
  *******)

Equations A : 
  package 
    Att_prot_locs_ideal
    [interface]
    RA_prot_interface 
  :=
  A := 
  {package Att_prot ∘  AuxPrim_ideal ∘ Sig_ideal_c }.
  Next Obligation.
  ssprove_valid.
  4: { apply fsubsetxx. }
  - unfold Aux_locs_prot, Att_prot_locs_ideal.
    rewrite /Sig_locs_ideal/Aux_locs_prot.
    rewrite /Sig_locs_real.
    rewrite /Key_locs.
    apply fsubsetU. 
    rewrite fset_cons.
    apply/orP; right.
    apply fsubsetxx.
  - rewrite /Sig_locs_ideal/Att_prot_locs_ideal.
    apply fsubsetU.
    apply/orP. left; apply fsubsetxx.
  - unfold Aux_locs_prot, Att_prot_locs_ideal.
    rewrite /Sig_locs_ideal/Aux_locs_prot.
    rewrite /Sig_locs_real.
    rewrite /Key_locs.
    apply fsubsetU. 
    rewrite fset_cons.
    apply/orP; right.
    apply fsubsetxx.
  
  Qed.

    
  (****** Equations for Real *******)

Equations B : 
  package 
    Att_prot_locs_real 
    [interface] 
    RA_prot_interface 
  :=
  B := 
  {package Att_prot ∘ AuxPrim_real ∘ Sig_real_c  }.
  Next Obligation.
    ssprove_valid.
    4 : { apply fsubsetxx. }
    all: try (unfold Att_prot_locs_real; apply fsubsetUr).
    unfold Att_prot_locs_real. apply fsubsetUl.
  Qed.

  Definition C := Sig_prot_ideal.
  Definition D := Sig_prot_real.

  Equations Aux_Prot  :
    package 
      ((*l :|: *) Aux_locs_prot)
      Sig_prot_ifce
      RA_prot_interface
      := 
    Aux_Prot :=
    [package

      #def #[ra_protocol] (chal : 'challenge) : 'pubkey × ('signature × 'bool) 
      {
        #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;

        state ← get state_loc ;;
        let msg := Hash state chal in
        '(pk, (sig, bool)) ←  prot_sig msg ;;
        ret (pk, (sig, bool))
      }
    ].


  Equations E : 
  package 
  (Sig_locs_ideal :|: Aux_locs_prot)
    [interface]
    RA_prot_interface 
  :=
  E := 
  {package @Aux_Prot  ∘ Sig_prot ∘ Sig_ideal_c }.
  Next Obligation.
  ssprove_valid. 
    2: { apply fsubsetxx. } 
    2: {  apply fsubsetU. apply/orP; right. apply fsubsetxx. }
    1: { unfold Sig_locs_ideal. apply fsubsetU. 
         apply/orP;left; apply fsubsetxx. }
    apply fsubsetU; apply/orP;left; apply fsubsetxx.
  Qed.
  
  Equations F : 
  package 
  (Sig_locs_real :|: Aux_locs_prot)
    [interface]
    RA_prot_interface 
  :=
  F := 
  {package @Aux_Prot ∘ Sig_prot ∘ Sig_real_c }.
  Next Obligation.
  ssprove_valid. 
  4 : { apply fsubsetxx. }
  3 : { apply fsubsetU. apply/orP; right. apply fsubsetxx. }
  2 : { apply fsubsetU.
        apply /orP;left; apply fsubsetxx. }
  apply fsubsetU. 
  apply/orP;left; apply fsubsetxx. 
Qed.
  

(* A more generic definition for swapping codes. *)
Definition cmd_locs {A:choiceType} (c:command A) : {fset Location} :=
  match c with
  | cmd_op _  _ => fset0
  | cmd_get l => fset1 l
  | cmd_put l _ => fset1 l
  | cmd_sample _ => fset0
  end.

Definition pre_fun : heap * heap -> Prop := fun '(s0,s1) => s0 = s1.
Print command.
Print opsig.

(** This is an assumption of SSProve.
    Imports are resolved before stepping into the
    relational Hoare Logic.
    For reference, check out [ssprove_sync].
 *)
Definition no_import {A} (c: command A) : Prop :=
  match c with
  | cmd_op _ _ => False
  | _ => True
  end.

Lemma swap_get_disjoint {B l v} {c: command B} :
    no_import c ->
    fset1 l :#: cmd_locs c
    -> (forall x:B,
   ⊢ ⦃ λ '(s0, s1), (pre_fun ⋊ rem_lhs l v) (s0, s1) ⦄
     ret x
       ≈
     ret x
     ⦃ λ '(a0, s0) '(a1, s1), ( pre_fun ⋊ rem_lhs l v) (s0, s1) /\ a0 = a1 ⦄)
   ->
     ⊢ ⦃ λ '(s0, s1), (pre_fun ⋊ rem_lhs l v) (s0, s1) ⦄
       x ← cmd c ;;
       ret x
         ≈
       x ← cmd c ;;
       ret x
       ⦃ λ '(a0, s0) '(a1, s1), (pre_fun ⋊ rem_lhs l v) (s0, s1) /\ a0 = a1 ⦄.
Proof.
  elim: c => //=.
  - move => l1 _ d H1.
    ssprove_sync.
    + rewrite /get_pre_cond => s0 s1.
      rewrite /pre_fun => s0_eq_s1.
      by rewrite s0_eq_s1.
    + exact: H1.
  - move => l1 v0 _.
    rewrite fdisjoint1s; move/fset1P/eqP => l_neq_l1 H1.
    ssprove_sync => //=.
    rewrite /put_pre_cond/pre_fun => s0 s1 pre.
    by rewrite pre.
  - move => op _ _ H1.
    ssprove_sync.
    exact: H1.
Qed.

(* TODO move into SSProve. *)
Lemma r_swap_scheme_locs_cmd :
  ∀ {A B : choiceType} {S: {fset Location}} (s : raw_code A) (c : command B),
    no_import c ->
    S :#: cmd_locs c →
    ValidCode S [interface] s →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      x ← s ;; y ← cmd c ;; ret (x,y) ≈
      y ← cmd c ;; x ← s ;; ret (x,y)
    ⦃ eq ⦄.
Proof.
  intros A B S s c noi d h.
  induction h.
  - simpl. apply rreflexivity_rule.
  - eapply fromEmpty. rewrite fset0E. eauto.
  - simpl in *. eapply r_transR.
    + eapply (rswap_cmd_eq _ _ _ (cmd_get _) _). simpl.
      set xxx := fun '(s0,s1) => s0 = s1; rewrite -(reshape_pair_id xxx).
      eapply r_get_remember_lhs => a0.
      eapply (rsame_head_cmd_alt c).
      *
        (**
           At this point, I really need to do a case analysis.
           This really is a more general goal though that only holds when the heaps are disjoint!
           After all, the comand could be a write in which case I could not just say that reading the
           value afterwards, it turns out to be the same, as the post condition suggests.
         *)
        move/fdisjointP: d => d; specialize (d l H); move: d; rewrite -fdisjoint1s => d.
        apply (swap_get_disjoint noi d) => x.
        by apply r_ret.
      * move => a1. eapply r_get_remind_rhs.
        ** eapply Remembers_rhs_from_tracked_lhs.
           *** ssprove_invariant.
           *** rewrite /xxx; ssprove_invariant.
        ** ssprove_forget_all. rewrite /xxx.
           eapply r_ret => s0 s1 s0_eq_s1.
           repeat f_equal; exact s0_eq_s1.
    + simpl.
      ssprove_sync_eq.
      exact: H1.
  - simpl in *. eapply r_transR.
    +
      (* Fail eapply rswap_cmd_eq. *)
      instantiate (1 := cmd_bind (cmd_put l v) (fun z => cmd_bind c (fun y => bind k (fun x => ret (pair x y))))).
      simpl.
      case: c noi d IHh => //=.
      * move => l0 _ d IHh.
        ssprove_swap_lhs 0.
        ** move/fdisjointP: d => d; specialize (d l H); move: d.
           by rewrite in_fset1; move/eqP.
        ** apply rreflexivity_rule.
      * move => l0 v0 _ d IHh.
        ssprove_swap_lhs 0.
        ** move/fdisjointP: d => d; specialize (d l H); move: d.
           by rewrite in_fset1; move/eqP.
        ** apply rreflexivity_rule.
      * move => op _ d IHh.
        ssprove_swap_lhs 0.
        apply rreflexivity_rule.
    + simpl. ssprove_sync_eq.
      exact: IHh.
  - simpl in *.
    eapply r_transR.
    + eapply (rswap_cmd_eq _ _ _ (cmd_sample _) _). simpl.
      eapply rsamplerC'_cmd.
    + simpl. eapply (rsame_head_cmd (cmd_sample _)). intro a.
      eauto.
Qed.

Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
eapply r_swap_scheme_locs_cmd => //= ; ssprove_valid
: ssprove_swap.

Lemma A_indist_E : A ≈₀ E.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel chal.
  all: ssprove_code_simpl.
  - simplify_linking. 
    rewrite /cast_fun/eq_rect_r/eq_rect.
    simplify_linking.
    ssprove_code_simpl; simpl.
    ssprove_swap_rhs 0. 
    2: { destruct KeyGen. apply prog_valid. } 
    1: { 
      unfold Key_locs.
      rewrite /cmd_locs.
      apply/fdisjointP => x.
      rewrite fset.fset_fsetU_norm2.
      move/fsetUP.
      case; 
        rewrite -fset1E; move/fset1P => E; rewrite E in_fset1; by [apply/eqP].
        }
    ssprove_code_simpl_more.
    eapply rsame_head_alt_pre.
    1: {
        set xxx := fun '(s0,s1) => s0 = s1. 
        rewrite -(reshape_pair_id xxx).
        apply (rpost_weaken_rule _
                       (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ (xxx (s₀, s₁)) )).
          -- eapply r_reflexivity_alt.
          --- instantiate (1:=Key_locs). destruct KeyGen. exact: prog_valid.
          --- move => l.
          rewrite /Key_locs/xxx. 
          unfold Key_locs => l_not_in_Key_locs. (* Why does rewrite fail? *)
          rewrite /get_pre_cond.
          by intros s0 s1 [=->].
      --- intros.
          rewrite /xxx/put_pre_cond.
          by intros s0 s1 [=->].
      -- intro a. 
           intro a1.
           simplify_linking.
           destruct a. destruct a1. intros H. destruct H.
           by split.
      }
      intros a.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      destruct a.
      ssprove_swap_lhs 2.
      ssprove_swap_lhs 1.
      ssprove_swap_lhs 0.
      ssprove_swap_lhs 6.
      ssprove_swap_lhs 5.
      ssprove_swap_lhs 4.
      ssprove_swap_lhs 3.
      ssprove_swap_lhs 2.
      ssprove_swap_lhs 1. 
      ssprove_contract_get_lhs.
      all: ssprove_sync_eq.  
      intros a.
      ssprove_sync_eq.
      all: ssprove_sync_eq.
      ssprove_sync_eq => pk.
      ssprove_sync_eq => sk.
      ssprove_code_simpl_more.
      ssprove_sync_eq => sig.
      ssprove_sync_eq.
      ssprove_sync_eq => sig'.
      by apply r_ret.

  Qed.

Lemma B_indist_F : B ≈₀ F.
Proof.
eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  - simplify_linking. 
    rewrite /cast_fun/eq_rect_r/eq_rect.
    simplify_linking.
    ssprove_code_simpl; simpl.
    ssprove_swap_rhs 0%N.
    2: {destruct KeyGen. apply prog_valid.  }
    1: {
      unfold Key_locs, cmd_locs.
      apply/fdisjointP => A.
      rewrite fset.fset_fsetU_norm2.
      move/fsetUP.
      case; 
        rewrite -fset1E; move/fset1P => E; rewrite E in_fset1; by [apply/eqP].
      }
    eapply rsame_head_alt_pre.
    1: {
        set xxx := fun '(s0,s1) => s0 = s1. 
        rewrite -(reshape_pair_id xxx).
        apply (rpost_weaken_rule _
                       (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ (xxx (s₀, s₁)) )).
          -- eapply r_reflexivity_alt.
          --- instantiate (1:=Key_locs). destruct KeyGen. exact: prog_valid.
          --- move => l.
          rewrite /Key_locs/xxx. 
          unfold Key_locs => l_not_in_Key_locs. (* Why does rewrite fail? *)
          rewrite /get_pre_cond.
          by intros s0 s1 [=->].
      --- intros.
          rewrite /xxx/put_pre_cond.
          by intros s0 s1 [=->].
      -- intro a. 
           intro a1.
           simplify_linking.
           destruct a. destruct a1. intros H. destruct H.
           by split.
      }
    intros a.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    destruct a.
    ssprove_swap_lhs 2.
    ssprove_swap_lhs 1.
    ssprove_swap_lhs 0.
    ssprove_swap_lhs 4.
    ssprove_swap_lhs 3.
    ssprove_swap_lhs 2.
    ssprove_swap_lhs 1.
    ssprove_contract_get_lhs.
    ssprove_sync_eq.
    intros a.
    ssprove_sync_eq.
    ssprove_sync_eq.
    ssprove_sync_eq => pk.
    ssprove_sync_eq => sk.
    ssprove_code_simpl_more.
    ssprove_sync_eq => pk'.
    by apply r_ret.

Qed.


Theorem red LA' A' :
  ValidPackage LA' RA_prot_interface A_export A' →
    fdisjoint LA' Att_prot_locs_ideal →
    fdisjoint LA' Att_prot_locs_real →
    fdisjoint LA' Sig_locs_ideal →
    LA' :#: Sig_locs_real →
    LA' :#: Aux_locs_prot →
    (AdvantageE A B A' <= AdvantageE C D (A'∘ (@Aux_Prot (*l*))))%R.
Proof.
  move => va H1 H2 H3 H4 H5.
  rewrite Advantage_link. 
  ssprove triangle A [:: (@Aux_Prot  ∘ C) ; (@Aux_Prot  ∘ D)] B A' as ineq.
  eapply le_trans.
  1: { exact: ineq. } 
  erewrite A_indist_E. 
  3: { exact H1. } 
  3: { rewrite -/Att_prot_locs_ideal. exact H1. }
  2: { exact va. }
  rewrite GRing.Theory.add0r.
  rewrite (Advantage_sym (Aux_Prot ∘ D) B A').   
  rewrite B_indist_F.
  2: { exact H2. } 
  2: { exact H2. } 
  by rewrite GRing.Theory.addr0.
Qed. 

Theorem RA_prot_perf_indist LA' A' :
ValidPackage LA' RA_prot_interface A_export A' →
  fdisjoint LA' Att_prot_locs_ideal →
  fdisjoint LA' Att_prot_locs_real →
  fdisjoint LA' Sig_locs_ideal →
  LA' :#: Sig_locs_real →
  LA' :#: Aux_locs_prot →
  (AdvantageE A B A' <= 0)%R.
Proof.
  intros va H1 H2 H3 H4 H5. 
  eapply le_trans. 1: {apply (red LA' A'  va H1 H2 H3 H4 H5). }
  rewrite /C/D.
  rewrite Advantage_sym.
  have xxx: fset [:: state_loc] :#: π5.Sig_locs_real.
  {
    rewrite /π5.Sig_locs_real/Key_locs.
    rewrite -fset1E.
    rewrite fset.fset_fsetU_norm2.
    rewrite fdisjointUr.
    apply/andP.
    split; rewrite fdisjoint1s -fset1E in_fset1; by apply/eqP. 
  }
  rewrite ext_unforge_sig_prot_full.
  1: { by []. }
  2 : {
    rewrite fdisjointUl.
    apply/andP; split.
    1: { exact H3. } unfold Aux_locs_prot, π5.Sig_locs_ideal.  rewrite fdisjointUr.
    apply/andP; split.
    1: apply xxx.
    rewrite -fset1E fdisjoint1s -fset1E in_fset1; by apply/eqP.
  }
  rewrite fdisjointUl. apply/andP; split.
  - exact: H4.
  - apply xxx.
Qed.

End Protocol.
