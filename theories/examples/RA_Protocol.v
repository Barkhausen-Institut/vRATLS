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
From vRATLS Require Import examples.Sig_Prot. Print SignatureProt. 
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
  Import π1 π2 π3 KGc Alg RAA RAH SP SigProt.
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

Parameter connect_msg_chal : Signature.pos_n <= #|Challenge|.

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
    (*4: { instantiate (1:=Att_prot_locs_real). apply fsubsetxx. }*)
    4 : { apply fsubsetxx. }
    all: try (unfold Att_prot_locs_real; apply fsubsetUr).
    unfold Att_prot_locs_real. apply fsubsetUl.
  Qed.

  Definition C := Sig_prot_ideal.
  Definition D := Sig_prot_real.

  Equations Aux_Prot {l} :
    package 
      (l :|: Aux_locs_prot)
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
    Next Obligation.
      ssprove_valid. 
      move=> l.
      ssprove_valid.
      rewrite /Aux_locs_prot.
      rewrite in_fsetU.
      apply/orP.
      right.
      auto_in_fset.
    Qed.


  Equations E : 
  package 
  (Sig_locs_ideal :|: Aux_locs_prot)
    [interface]
    RA_prot_interface 
  :=
  E := 
  {package (@Aux_Prot Sig_locs_ideal)   ∘ Sig_prot ∘ Sig_ideal_c }.
  Next Obligation.
  ssprove_valid. 
    2: { apply fsubsetxx. }
    2: { apply fsubsetxx. }
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
  {package (@Aux_Prot Sig_locs_real) ∘ Sig_prot ∘ Sig_real_c }.
  Next Obligation.
  ssprove_valid. 
  4 : { apply fsubsetxx. }
  3 : { apply fsubsetxx. }
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
Print r_swap_scheme_cmd.
Lemma r_swap_scheme_locs_cmd :
  ∀ {A B : choiceType} {S: {fset Location}} (s : raw_code A) (c : command B),
    S :#: cmd_locs c →
    ValidCode S [interface] s →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      x ← s ;; y ← cmd c ;; ret (x,y) ≈
      y ← cmd c ;; x ← s ;; ret (x,y)
    ⦃ eq ⦄.
Proof.
Admitted.

Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
eapply r_swap_scheme_locs_cmd ; ssprove_valid
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

Theorem red LA' A' (l:{fset Location}):
  ValidPackage LA' Att_interface A_export A' →
    (* TODO *)
    fdisjoint LA' Att_prot_locs_ideal →
    fdisjoint LA' Att_prot_locs_real →
    fdisjoint LA' Sig_locs_ideal →
    LA' :#: Sig_locs_real →
    LA' :#: Aux_locs_prot →
    (AdvantageE A B A' <= AdvantageE C D (A'∘ (@Aux_Prot l)))%R.
Proof.
  move => va H1 H2 H3 H4 H5.
  

  rewrite Advantage_sym.
  simpl in *|-. Print Att_prot_locs_real. Print Att_prot_locs_ideal.
  ssprove triangle ((@Aux_Prot Sig_locs_ideal) ∘ Sig_prot ∘ Sig_ideal_c ) [::
    Sig_prot_ideal ;
    Sig_prot_real
    ] ((@Aux_Prot Sig_locs_real) ∘ Sig_prot ∘ Sig_real_c) A as ineq.




  Theorem RA_prot_perf_indist:
    forall Attacker,
    AdvantageE A B Attacker <= 0.
 










(**deterministically maps (state, challenge) back to x???**)

(** I know axiom & lemma(hash_message_equiv) are the same but there was no other way :( )**)
Axiom hash_message_identity:
forall (state : 'state) (x : 'message),
Hash state (message_to_challenge x) = x.

(*This hypothesis is to reflect the protocol assumptions*)
Lemma hash_determinism:
  forall (state : 'state) (challenge : 'challenge) (x : 'message),
    message_to_challenge x = challenge ->
    Hash state challenge = x.
Proof.
  intros state challenge x Hmessage.
  (* step assumes properties of Hash and message_to_challenge *)
  rewrite <- Hmessage. 
  apply hash_message_identity.
Qed.


Lemma hash_message_equiv:
  forall state x,
    Hash state (message_to_challenge x) = x.
Proof.
  intros state x.
  apply hash_determinism.
  reflexivity. (* message_to_challenge x = message_to_challenge x *)
Qed.

(*Lemma heap_update_equiv:
  forall h loc v,
    set_heap h loc v = set_heap h loc v. *)
Lemma heap_update_equiv:
  forall h loc v1 v2,
    v1 = v2 ->
    set_heap h loc v1 = set_heap h loc v2.
Proof.
  intros h loc v1 v2 Heq.
  (* substitute v2 with v1 in the goal *)
  subst v2.
  (* Now the goal is to prove that set_heap h loc v1 = set_heap h loc v1 *)
  reflexivity.
Qed.

(*Lemma preserve_xxx_set_heap:
  forall h1 h2 loc v,
    xxx (h1, h2) ->
    xxx (set_heap h1 loc v, set_heap h2 loc v).
Proof.
  intros h1 h2 loc v Hrel.
  (* Expand set_heap if its behavior is known *)
  unfold set_heap.
  (* Reasoning about how the relation is preserved after identical updates *)
  (* Here we assume that xxx is preserved by identical updates *)

  simpl.
  unfold xxx in Hrel. 
  unfold sval. *)

Lemma preserve_xxx_set_heap:
  forall h1 h2 loc v,
    h1 = h2 ->
    set_heap h1 loc v = set_heap h2 loc v.
Proof.
  intros h1 h2 loc v Hrel.
  (* Use Hrel to rewrite h2 as h1 *)
  rewrite Hrel.
  (* Now both sides are identical *)
  reflexivity.
Qed.
 
(*
Lemma A_indist_c: 
      A ≈₀ C.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  - simplify_linking. 
    ssprove_sync_eq.
    ssprove_sync_eq.
    ssprove_sync_eq  => pk. 
    ssprove_swap_lhs 0. 
    ssprove_sync_eq => sk.
    ssprove_swap_lhs 2.
    ssprove_swap_lhs 1.
    ssprove_contract_get_lhs. 
    ssprove_swap_lhs 0. 
    ssprove_sync_eq => sig.   
    eapply rpre_weaken_rule.
    2: { move => s0 s1 H. 
         instantiate (1:=λ '(h₀, h₁), xxx (h₀, h₁)).
         simpl.
         exact H. 
      }
    eapply r_get_remember_lhs => state.
    apply r_put_lhs.
    apply r_put_rhs.  
    (*ssprove_sync. *)
    ssprove_restore_mem.
    2: {
      ssprove_sync_eq => sign.
      eapply r_ret => s0 s1 set_vals. 
      apply conj.    
      - assert (Hhash: Hash state (message_to_challenge x) = x).
      1: {
        apply hash_message_equiv.
      }
      rewrite Hhash.
      reflexivity.
      - exact. 
      }
    rewrite /preserve_update_mem/remember_pre/update_heaps.
    intros s₀ s₁ Hrel.
    (*rewrite hash_message_equiv. *)
    (*apply heap_update_equiv.*)

    destruct Hrel as [Hrel_lhs Hrel_rhs].
    (*
    (* I need to update both heaps & reason about the relation *)
    assert (Hupdate: xxx
      (set_heap s₀ sign_loc (setm sig (Sign sk x, x) Signature.tt),
       set_heap s₁ sign_loc (setm sig (Sign sk x, x) Signature.tt))).
       1: {
        apply preserve_xxx_set_heap.
        exact Hrel_lhs.
       }
      *)
    assert (Hhash: Hash state (message_to_challenge x) = x).
    1: {
      apply hash_message_equiv.
    }
    rewrite Hhash. apply preserve_xxx_set_heap. exact Hrel_lhs.
  
  Qed.
*)




Lemma A_indist_c: 
      A ≈₀ C.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  - simplify_linking. 
    ssprove_sync_eq.
    ssprove_sync_eq.
    ssprove_sync_eq  => pk. 
    ssprove_swap_lhs 0. 
    ssprove_sync_eq => sk.
    ssprove_swap_lhs 2.
    ssprove_swap_lhs 1.
    ssprove_contract_get_lhs. 
    ssprove_swap_lhs 0.
    ssprove_sync_eq => sig.   
    eapply rpre_weaken_rule.
    2: { move => s0 s1 H. 
         instantiate (1:=λ '(h₀, h₁), xxx (h₀, h₁)).
         simpl.
         exact H. 
      }
    eapply r_get_remember_lhs => state.
    apply r_put_lhs.
    apply r_put_rhs.
    ssprove_sync.
    1: {
      rewrite /get_pre_cond => s0 s1.
      rewrite /set_lhs/set_rhs.
      case => s1' H.
      
      Search set_rhs set_lhs.
    2:{
      ssprove_restore_mem.

    }







(*
Lemma A_indist_c: 
      A ≈₀ C.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  - simplify_linking. rewrite -/full_heap_eq'.
    ssprove_sync_eq.
    ssprove_sync_eq.
    ssprove_sync_eq  => pk. 
    ssprove_swap_lhs 0.
    ssprove_sync_eq => sk.
    ssprove_swap_lhs 2.
    ssprove_swap_lhs 1.
    ssprove_contract_get_lhs. 

    ssprove_swap_lhs 0.

    ssprove_sync_eq => sig.   
    Print state_loc.
    eapply rpre_weaken_rule.
    2: { move => s0 s1 H. 
         instantiate (1:=λ '(h₀, h₁), xxx (h₀, h₁)).
         simpl.
         exact H. 
      }
    eapply r_get_remember_lhs => state.
    apply r_put_lhs.
    apply r_put_rhs.
    ssprove_sync.
    1: {
      rewrite /get_pre_cond => s0 s1.
      rewrite /set_lhs/set_rhs.
      case => s1' H.
      
      Search set_rhs set_lhs.
    2:{
      ssprove_restore_mem.

    }
    have bbb : 
      (Sign sk
        (Hash state
          (message_to_challenge x)),
       Hash state
        (message_to_challenge x)) =
      (Sign sk x, x).
      {
        f_equal.
        - f_equal.
      }
    
  
    ssprove_swap_lhs 1. Show.


    rewrite /setm. 


    (** I need to sync the signing op **)
    ssprove_sync_eq  => state_loc.
  
    (** trying to match memory modifications for Sign? *)

    Search ( ?v1  ?get ?x ).
   
    apply eq_rel_perf_ind_eq.
*)


Lemma B_indist_D: 
      B ≈₀ D.
Proof. Search (?B ≈₀ ?D).
Print eq_rel_perf_ind_eq.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  - simplify_linking.

    ssprove_sync_eq.
    ssprove_sync_eq.

    (*ssprove_swap_lhs 3.
    ssprove_swap_lhs 2.
    ssprove_swap_lhs 1.
    ssprove_swap_rhs 1.
    ssprove_contract_get_lhs.
    ssprove_sync_eq  => pk. *)

    ssprove_sync_eq  => pk. 
    ssprove_swap_lhs 1.
    ssprove_contract_get_lhs.
    ssprove_swap_lhs 0.
    ssprove_sync_eq => sk.

    eapply rpre_weaken_rule.
    2: { move => s0 s1 H. 
         admit. 
      }
    eapply r_get_remember_lhs => state.
    apply r_put_lhs.
    apply r_put_rhs.
    ssprove_sync.

    apply r_ret. 

    ssprove_sync_eq.

    Check r_get_remember_lhs.

    ssprove_sync_eq => state.
    apply r_get_remember_lhs => state_loc_lhs.
    (*ssprove_sync_eq  => state_loc. *)
    ssprove_sync_eq => sk_loc.
    


  


      (*Equations Att_prot_ideal : package Sig_locs_ideal [interface] Sig_prot_ifce :=
        Att_prot_ideal := {package Sig_prot ∘ Sig_ideal_c }.
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
          rewrite fset_cons.
          rewrite [X in fsubset X _]fset_cons.
          apply fsetUS.
          rewrite !fset_cons -fset0E.
          apply fsub0set.
        - rewrite /Key_locs/Attestation_locs_ideal/Attestation_locs_real/Key_locs.
          rewrite -fset_cat /cat.
          rewrite fset_cons.
          apply fsetUS.
          rewrite fset_cons.
          apply fsetUS.
          rewrite fset_cons.
          apply fsetUS.
          rewrite fset_cons.
          apply fsetUS.
          apply fsubsetxx.
      Defined. *)
  
    (* This prop is different from the RA prop, because it has much more inputs *)
    Parameter RA_prop:
      ∀ (l: {fmap (Signature * chState * chChallenge ) -> 'unit}) 
        (s s' s'' : chState) (pk : PubKey) (sk : SecKey) (chal : chChallenge) (h  : chMessage),
      Ver_sig pk (Sign sk (Hash s chal)) (Hash s' chal) 
      = ((Sign sk (Hash s chal), s'', chal) \in domm l).
  
    Lemma ra_prot_indist: 
      Att_prot_real ≈₀ Att_prot_ideal.
    Proof.
    eapply (eq_rel_perf_ind_ignore (fset [:: attest_loc_long])).
    - rewrite /Attestation_locs_real/Attestation_locs_ideal/Attestation_locs_real.
      apply fsubsetU.
      apply/orP.
      right.
      auto_in_fset.
      rewrite fsetUC.
      rewrite -!fset_cat.
      rewrite fset_cons.
      rewrite [X in fsubset _ X]fset_cons.
      apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsub0set.
    - simplify_eq_rel x.   (* [x] becomes the argument to the procedure. *)
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_code_simpl; simplify_linking.
      ssprove_sync.
      ssprove_sync.
      ssprove_sync => pk.
      ssprove_sync => chal.
      ssprove_sync => sk.
      ssprove_sync => state.
      apply r_get_remember_rhs => a.
      apply r_get_remember_lhs => pk'.
      apply r_get_remember_lhs => state'.
      eapply r_put_rhs.
      ssprove_restore_mem.
      -- ssprove_invariant.
      -- eapply r_get_remember_rhs => a'.
         apply r_get_remember_rhs => state''.
         eapply r_ret => s0 s1 pre //=.
         split.
      --- repeat f_equal.
          eapply RA_prop. intuition eauto. 
      ---move: pre.
         by repeat case.
      Qed.       
  
     (** attest is not a type here, So, I'll use Signature as both input and output type 
    Definition convert_signature_to_attest (sig : Signature) : Signature := sig. **)
    Definition convert_signature_to_attest (sig : Attestation) : 'signature := sig.
  
  (*  Definition Aux := 
      [package
        #def #[att] (_ : 'unit) : ('pubkey) × (('attest) × ('bool))
        {
          #import {sig #[protocol] : 'unit →  ('pubkey) × (('signature) × ('bool)) } as prot_sig ;;
  
          '(pk, (sig, bool)) ←  prot_sig tt ;;
          let attest := convert_signature_to_attest sig in
          ret (pk, (attest, bool))
        }
      ]. *)
  
    (*
    I cannot define this because the Challenge space and the Message space
    are abstract.
    There is only a single connection between these two spaces:
    the [Hash] function.
    *)
  
    Definition Att_prot_locs_ideal := Sig_locs_ideal :|: fset [:: state_loc ].
  
    Equations Aux_ideal :   
      package 
        Att_prot_locs_ideal 
        Sig_prot_ifce
        RA_prot_interface
        := 
      Aux_ideal :=
      [package
  
        #def #[ra_protocol] (_ : 'unit) : 'pubkey × ('attest × 'bool) 
        {
          #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;
  
          chal ← sample uniform i_chal ;;
          state ← get state_loc ;;
          let msg := Hash state chal in
          '(pk, (sig, bool)) ←  prot_sig msg ;;
          ret (pk, (sig, bool))
        }
      ].
      Next Obligation.
        ssprove_valid.
        rewrite /Att_prot_locs_ideal in_fsetU. apply/orP. 
        right; auto_in_fset.
      Qed.
  
      Parameter connect_msg_chal : Signature.pos_n <= #|Challenge|.
  
      Definition Att_prot_locs_real := Sig_locs_real :|: fset [:: state_loc ].
  
      Equations message_to_challenge (m:'message) : 'challenge :=
        message_to_challenge m := _.
      Next Obligation.
        Unset Printing Notations.
        Print π2.chMessage.
        rewrite /π2.chMessage /chChallenge.
        simpl.
        apply widen_ord.
        exact connect_msg_chal.
      Qed.
  
      Equations Aux_real :   
      package 
        Att_prot_locs_real 
        Sig_prot_ifce 
        Sig_prot_ifce
        := 
      Aux_real :=
      [package
  
        #def #[protocol] (msg : 'message) : 'pubkey × ('attest × 'bool) 
        {
          #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;
  
          state ← get state_loc ;;
          let chal' := message_to_challenge msg in
          let msg' := Hash state chal' in
          '(pk, (sig, bool)) ←  prot_sig msg' ;;
          ret (pk, (sig, bool))
        }
      ].
      Next Obligation. 
        ssprove_valid.
        rewrite /Att_prot_locs_real in_fsetU. apply/orP. 
        right; auto_in_fset.
      Qed.
  
    (* Definition pred (n:nat) : nat :=
        match n with
        | O => 0
        | S n' => n'
        end.
  
      Lemma xxx : forall n, pred n = n.
      Proof.
        destruct n eqn:E.
        Fail unfold pred.
        Abort.
      
      Equations pred' (n:nat) : nat :=
        pred' O      := O;
        pred' (S n') := n'. *)
  
    Equations Aux_Sig_prot_ideal : package Att_prot_locs_ideal [interface] RA_prot_interface :=
        Aux_Sig_prot_ideal := {package Aux_ideal ∘ Sig_prot_ideal }.   
    Next Obligation.
        ssprove_valid.
        - apply fsubsetxx.
        - rewrite /Att_prot_locs_ideal/Att_prot_locs_real.
          (*apply/fsubsetP.  *)
          apply/fsubsetP => x Hx.
          rewrite in_fsetU.
          apply/orP; left. 
          done.       
    Qed.
  
    Equations Aux_Sig_prot_real : package Att_prot_locs_real [interface] Sig_prot_ifce :=
      Aux_Sig_prot_real := {package Aux_real ∘ Sig_prot_real }.   
    Next Obligation.
      ssprove_valid.
      - apply fsubsetxx.
      - rewrite /Att_prot_locs_real.
        (*apply/fsubsetP.  *)
        apply/fsubsetP => x Hx.
        rewrite in_fsetU.
        by apply/orP; left.      
  Qed.
  

  Print Att_prot_locs_real.
  Print Att_prot_real.
  Print RA_prot_interface.
  Print Att_prot.


  Lemma ra_prot_real_indist_sig_prot_real: 
    Att_prot_real ≈₀ Aux_Sig_prot_real.
  Proof.
*)














(*

  Import π1 π2 RAP KG Alg RAA SP RAH SigP.

  Definition i_chal := #|Challenge|.
  Definition ra_protocol : nat := 50.

  Definition RA_prot_interface := 
    [interface #val #[ra_protocol] : 'unit → 'pubkey × ('attest × 'bool) ].

  Definition Att_prot : 
    package 
    Attestation_locs_real 
    Att_interface 
    RA_prot_interface
  := [package
    #def  #[ra_protocol] ( _ : 'unit) : 'pubkey × ('attest × 'bool)
    {
      #import {sig #[get_pk_att] : 'unit →  'pubkey } as get_pk_att ;;
      #import {sig #[attest] : 'challenge → ('signature × 'message)  } as attest ;;
      #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;
  
      (* Protocol *)
      pk ← get_pk_att tt ;;
      chal ← sample uniform i_chal ;;
      '(att, msg) ← attest chal ;;
      bool ← verify_att (chal, att) ;;
      ret (pk, ( att, bool ))
    } 
  ]. *)

  Equations Att_prot_real : package Attestation_locs_real 
     [interface] RA_prot_interface :=
    Att_prot_real := {package Att_prot ∘ Att_real_c }.
  Next Obligation.
    ssprove_valid.
    - rewrite /Attestation_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    - rewrite /Key_locs/Attestation_locs_real/Key_locs.
      rewrite fset_cons.
      apply fsetUS.
      rewrite fset_cons.
      apply fsetUS.
      apply fsubsetxx.
    Defined.

    Equations Att_prot_ideal : package Attestation_locs_ideal [interface] RA_prot_interface :=
      Att_prot_ideal := {package Att_prot ∘ Att_ideal_c }.
    Next Obligation.
      ssprove_valid.
      - rewrite /Key_locs/Attestation_locs_ideal/Attestation_locs_real/Key_locs.
        rewrite -fset_cat /cat.
        rewrite fset_cons.
        rewrite [X in fsubset X _]fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        rewrite [X in fsubset X _]fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        rewrite [X in fsubset X _]fset_cons.
        apply fsetUS.
        rewrite !fset_cons -fset0E.
        apply fsub0set.
      - rewrite /Key_locs/Attestation_locs_ideal/Attestation_locs_real/Key_locs.
        rewrite -fset_cat /cat.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        rewrite fset_cons.
        apply fsetUS.
        apply fsubsetxx.
    Defined.

  (* This prop is different from the RA prop, because it has much more inputs *)
  Parameter RA_prop:
    ∀ (l: {fmap (Signature * chState * chChallenge ) -> 'unit}) 
      (s s' s'' : chState) (pk : PubKey) (sk : SecKey) (chal : chChallenge) (h  : chMessage),
    Ver_sig pk (Sign sk (Hash s chal)) (Hash s' chal) 
    = ((Sign sk (Hash s chal), s'', chal) \in domm l).

  Lemma ra_prot_indist: 
    Att_prot_real ≈₀ Att_prot_ideal.
  Proof.
  eapply (eq_rel_perf_ind_ignore (fset [:: attest_loc_long])).
  - rewrite /Attestation_locs_real/Attestation_locs_ideal/Attestation_locs_real.
    apply fsubsetU.
    apply/orP.
    right.
    auto_in_fset.
    rewrite fsetUC.
    rewrite -!fset_cat.
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  - simplify_eq_rel x.   (* [x] becomes the argument to the procedure. *)
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_code_simpl; simplify_linking.
    ssprove_sync.
    ssprove_sync.
    ssprove_sync => pk.
    ssprove_sync => chal.
    ssprove_sync => sk.
    ssprove_sync => state.
    apply r_get_remember_rhs => a.
    apply r_get_remember_lhs => pk'.
    apply r_get_remember_lhs => state'.
    eapply r_put_rhs.
    ssprove_restore_mem.
    -- ssprove_invariant.
    -- eapply r_get_remember_rhs => a'.
       apply r_get_remember_rhs => state''.
       eapply r_ret => s0 s1 pre //=.
       split.
    --- repeat f_equal.
        eapply RA_prop. intuition eauto. 
    ---move: pre.
       by repeat case.
    Qed.       

   (** attest is not a type here, So, I'll use Signature as both input and output type 
  Definition convert_signature_to_attest (sig : Signature) : Signature := sig. **)
  Definition convert_signature_to_attest (sig : Attestation) : 'signature := sig.

(*  Definition Aux := 
    [package
      #def #[att] (_ : 'unit) : ('pubkey) × (('attest) × ('bool))
      {
        #import {sig #[protocol] : 'unit →  ('pubkey) × (('signature) × ('bool)) } as prot_sig ;;

        '(pk, (sig, bool)) ←  prot_sig tt ;;
        let attest := convert_signature_to_attest sig in
        ret (pk, (attest, bool))
      }
    ]. *)

  (*
  I cannot define this because the Challenge space and the Message space
  are abstract.
  There is only a single connection between these two spaces:
  the [Hash] function.
  *)

  Definition Att_prot_locs_ideal := Sig_locs_ideal :|: fset [:: state_loc ].



  Equations Aux_ideal :   
    package 
      Att_prot_locs_ideal 
      Sig_prot_ifce
      RA_prot_interface
      := 
    Aux_ideal :=
    [package

      #def #[ra_protocol] (_ : 'unit) : 'pubkey × ('attest × 'bool) 
      {
        #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;

        chal ← sample uniform i_chal ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        '(pk, (sig, bool)) ←  prot_sig msg ;;
        ret (pk, (sig, bool))
      }
    ].
    Next Obligation.
      ssprove_valid.
      rewrite /Att_prot_locs_ideal in_fsetU. apply/orP. 
      right; auto_in_fset.
    Qed.

    Parameter connect_msg_chal : Signature.pos_n <= #|Challenge|.

    Definition Att_prot_locs_real := Sig_locs_real :|: fset [:: state_loc ].

    Equations message_to_challenge (m:'message) : 'challenge :=
      message_to_challenge m := _.
    Next Obligation.
      Unset Printing Notations.
      Print π2.chMessage.
      rewrite /π2.chMessage /chChallenge.
      simpl.
      apply widen_ord.
      exact connect_msg_chal.
    Qed.

    Equations Aux_real :   
    package 
      Att_prot_locs_real 
      Sig_prot_ifce 
      Sig_prot_ifce
      := 
    Aux_real :=
    [package

      #def #[protocol] (msg : 'message) : 'pubkey × ('attest × 'bool) 
      {
        #import {sig #[protocol] : 'message → 'pubkey × ('signature × 'bool) } as prot_sig ;;

        state ← get state_loc ;;
        let chal' := message_to_challenge msg in
        let msg' := Hash state chal' in
        '(pk, (sig, bool)) ←  prot_sig msg' ;;
        ret (pk, (sig, bool))
      }
    ].
    Next Obligation. 
      ssprove_valid.
      rewrite /Att_prot_locs_real in_fsetU. apply/orP. 
      right; auto_in_fset.
    Qed.

  (* Definition pred (n:nat) : nat :=
      match n with
      | O => 0
      | S n' => n'
      end.

    Lemma xxx : forall n, pred n = n.
    Proof.
      destruct n eqn:E.
      Fail unfold pred.
      Abort.
    
    Equations pred' (n:nat) : nat :=
      pred' O      := O;
      pred' (S n') := n'. *)

  Equations Aux_Sig_prot_ideal : package Att_prot_locs_ideal [interface] RA_prot_interface :=
      Aux_Sig_prot_ideal := {package Aux_ideal ∘ Sig_prot_ideal }.   
  Next Obligation.
      ssprove_valid.
      - apply fsubsetxx.
      - rewrite /Att_prot_locs_ideal/Att_prot_locs_real.
        (*apply/fsubsetP.  *)
        apply/fsubsetP => x Hx.
        rewrite in_fsetU.
        apply/orP; left. 
        done.       
  Qed.

  Equations Aux_Sig_prot_real : package Att_prot_locs_real [interface] Sig_prot_ifce :=
    Aux_Sig_prot_real := {package Aux_real ∘ Sig_prot_real }.   
  Next Obligation.
    ssprove_valid.
    - apply fsubsetxx.
    - rewrite /Att_prot_locs_real.
      (*apply/fsubsetP.  *)
      apply/fsubsetP => x Hx.
      rewrite in_fsetU.
      by apply/orP; left.      
Qed.

Lemma ra_prot_real_indist_sig_prot_real: 
  Att_prot_real ≈₀ Aux_Sig_prot_real.
Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  simplify_linking.

  ssprove_swap_rhs 1.
  ssprove_swap_rhs 2.
  ssprove_swap_rhs 0%N.
  ssprove_swap_rhs 1.
  ssprove_sync_eq.
  ssprove_sync_eq.
  ssprove_swap_rhs 1.
  ssprove_swap_rhs 0.
  ssprove_sync_eq. auto.
  
  simpl. unfold uniform in *. intros H. 
  ssprove_sync_eq => state_loc.
  ssprove_swap_rhs 0. 
  ssprove_sync_eq => sk.
  ssprove_swap_lhs 1.
  ssprove_contract_get_lhs.
  ssprove_sync_eq => state.
  ssprove_sync_eq => pk.
  by apply r_ret.
Qed.



(*Definition attest_sign_invariant (h0 h1 : heap) :=
  forall sig m c,
    (sig, m, c) \in domm *)


  Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ Aux_Sig_prot_ideal.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    simplify_linking.
    ssprove_swap_rhs 1.
    ssprove_swap_rhs 2.
    ssprove_swap_rhs 0%N.
    ssprove_swap_rhs 1.
    ssprove_sync_eq.
    ssprove_sync_eq.
    ssprove_swap_rhs 1.
    ssprove_swap_rhs 0.
    ssprove_swap_rhs 2.
    ssprove_sync_eq. auto=> //=. 
    intros H.
    ssprove_sync_eq.
    




  Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Aux ∘ Att_prot_ideal ≈₀ Sig_prot_ideal.


    Proof.


End Protocol.


Print SignatureProt. Print Sig_Prot. 

Module Type Example
(π1 : SignatureParams)
(π2 : SignatureConstraints)
(RAP : RemoteAttestationParams π2)
(KG : KeyGeneration π1 π2)
(Alg : SignatureAlgorithms π1 π2 KG)
(RAA : RemoteAttestationAlgorithms π1 π2 RAP KG Alg)
(SP : SignaturePrimitives π1 π2 KG Alg)
(RAH : RemoteAttestationHash π1 π2 RAP KG Alg RAA SP)
(Prot : Protocol π1 π2 RAP KG Alg RAA SP RAH)
(SigIdeal: SignatureProt π1 π2 KG Alg SP)
.
Import π1 π2 RAP KG Alg RAA SP RAH  SigIdeal.

Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ Sig_prot_ideal.
  Proof.



  Lemma ra_prot_ideal_indist_sig_prot_ideal: 
    Att_prot_ideal ≈₀ vRATLS.examples.Sig_Prot.SignatureProt.Sig_prot_ideal.
  Proof.