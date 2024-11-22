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

Module Type Protocol
    (π1 : SignatureParams)
    (π2 : SignatureConstraints)
    (RAP : RemoteAttestationParams π2)
    (KG : KeyGeneration π1 π2)
    (Alg : SignatureAlgorithms π1 π2 KG)
    (RAA : RemoteAttestationAlgorithms π1 π2 RAP KG Alg)
    (SP : SignaturePrimitives π1 π2 KG Alg)
    (RAH : RemoteAttestationHash π1 π2 RAP KG Alg RAA SP)

    (SigP: SignatureProt π1 π2 KG Alg SP)
    .
  Import π1 π2 RAP KG Alg RAA SP RAH SigP.

  Definition i_chal := #|Challenge|.
  Definition ra_protocol : nat := 50.
  
  (*
  Definition RA_prot_interface := 
    [interface #val #[ra_protocol] : 'unit → 'pubkey × ('attest × 'bool) ].
  *)

  Print Sig_ifce.
  Print Attestation_locs_real.
  Print Att_interface.

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

Equations message_to_challenge (m:'message) : 'challenge :=
  message_to_challenge m := _.
    Next Obligation.
      rewrite /π2.chMessage /chChallenge.
      simpl.
      apply widen_ord.
      exact connect_msg_chal.
    Qed.

Equations Att_prot_ideal : 
  package 
     Aux_locs_prot
     Att_interface 
     Sig_prot_ifce
  := 
  Att_prot_ideal :=
  [package
    #def  #[protocol] (msg : 'message) : 'pubkey × ('attest × 'bool) 
    {
      #import {sig #[get_pk_att] : 'unit →  'pubkey } as get_pk_att ;;
      #import {sig #[attest] : 'challenge → ('signature × 'message)  } as attest ;;
      #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;
  
      (* Its kinda adversary-controlled challenge *)
      let chal := message_to_challenge msg in 

      pk ← get_pk_att tt ;;                       (* Get the public key *)
      '(att, _) ← attest chal ;;                (* Generate an attestation for the chall *)
      bool ← verify_att (chal, att) ;;            (* Verify the attestation *)
      ret (pk, (att, bool)) 
    } 
  ]. 


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

Equations Att_prot_real : 
  package 
    (*Attestation_locs_real*) 
    Aux_locs_prot
    Att_interface 
    Sig_prot_ifce
    := 
    Att_prot_real :=
    [package
      #def  #[protocol] (msg : 'message) : 'pubkey × ('attest × 'bool) 
      {
        #import {sig #[get_pk_att] : 'unit →  'pubkey } as get_pk_att ;;
        #import {sig #[attest] : 'challenge → ('signature × 'message)  } as attest ;;
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;
    
        (* Its kinda adversary-controlled challenge *)
        let chal := message_to_challenge msg in 

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
    Sig_prot_ifce 
  :=
  A := 
  {package Att_prot_ideal ∘  AuxPrim_ideal ∘ Sig_ideal_c }.
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
    apply/orP; left; apply fsubsetxx.
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
    Sig_prot_ifce 
  :=
  B := 
  {package Att_prot_real ∘ AuxPrim_real ∘ Sig_real_c  }.
  Next Obligation.
    ssprove_valid.
    Check fsubsetxx.
    (*4: { instantiate (1:=Att_prot_locs_real). apply fsubsetxx. }*)
    4 : { apply fsubsetxx. }
    all: try (unfold Att_prot_locs_real; apply fsubsetUr).
    unfold Att_prot_locs_real. apply fsubsetUl.
  Qed.

  Definition C := Sig_prot_ideal.
  Definition D := Sig_prot_real.

  Check A.
  Check B.
  Check C.
  Check D.

  (*** Now A ≈₀ C , B ≈₀ D , 
        A ≈₀ E , B ≈₀ F  ***)

Lemma A_indist_B: 
      A ≈₀ B.
Proof.
Admitted.

Lemma B_indist_D: 
      B ≈₀ D.
Proof. Search (?B ≈₀ ?D).
Print eq_rel_perf_ind_eq.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel x.
  all: ssprove_code_simpl.
  simplify_linking.


  


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

