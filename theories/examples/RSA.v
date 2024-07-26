From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".

From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq fintype zmodp prime finset.
  
Set Warnings "notation-overridden,ambiguous-paths".

From extra Require Import rsa.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Casts
  Package Prelude RandomOracle.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Require Import Coq.Init.Logic.
Require Import List.

Set Equations With UIP.
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From vRATLS Require Import Signature.

Import PackageNotation.

Obligation Tactic := idtac.

Local Open Scope package_scope.

(*
  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter order_gt1 : (1 < #[g])%N.
*)

Module Type RSA_params <: SignatureParams.

  Variable n : nat.
  
  Definition pos_n : nat := 2^n.

  (* the set of prime numbers. *)
  Definition prime_num : finType := {x: 'I_n.+3 | prime x}.
  Definition P : {set prime_num} := [set : prime_num].

  Definition P' (y : prime_num) := (P :\ y)%SET.

  (*
  Definition proj_1 (p : prime_num) : 'I_n.+1 :=
    projT1 p.
  *)

  Lemma p_q_ineq : forall y, y \in P -> P :!=: P' y.
  Proof. 
    unfold P'. intros. 
    apply properD1 in H.
    rewrite eqtype.eq_sym.
    apply proper_neq.
    exact H.
  Qed.

  Definition wf_type p q pq e d := [&& prime p, prime q, p != q,
  0 < pq, p.-1 %| pq, q.-1 %| pq &
  e * d == 1 %[mod pq]].
  
  Local Open Scope ring_scope.
  Import GroupScope GRing.Theory.

  Definition R : Type := 'I_(n*n).+3.
  
  
  (*Definition chR : choice_type := 'fin (mkpos pos_n).*)
  Definition Z_n_prod : finType := prod_finType R R.

  Definition SecKey := Z_n_prod.  
  Definition PubKey : finType := Z_n_prod.
  Definition Signature : finType := R.
  Definition Message : finType := R.
  Definition Challenge : finType := R.
  
End RSA_params.

Module RSA_KeyGen (π1  : RSA_params)
    <: KeyGenParams π1.

  Import π1.
  
  Definition n := π1.n.  

  (* Encryption *)
  Definition encrypt' e p q w : nat := w ^ e %% (p * q ).

  Theorem enc_eq {p q pq d e : nat} (wf : wf_type p q pq d e) w :
    let r := Build_rsa wf in
    encrypt' d p q w = encrypt r w.
  Proof.
    by rewrite /encrypt/encrypt'/r. 
  Qed.
  
  (* Decryption *)
  Definition decrypt' d p q w := w ^ d %% (p * q).

  Theorem dec_eq {p q pq d e : nat} (wf : wf_type p q pq d e) w :
    let r := Build_rsa wf in
    decrypt' e p q w = decrypt r w.
  Proof.
    by rewrite /encrypt/encrypt'/r.
  Qed.
 
  Theorem rsa_correct' {p q pq d e : nat} (wf : wf_type p q pq d e) w :
    let r := Build_rsa wf in
    decrypt' e p q (encrypt' d p q w)  = w %[mod p * q].
  Proof.
    rewrite (enc_eq wf) (dec_eq wf) /=.
    apply rsa_correct.
  Qed.

   (* Encryption *)
   Definition encrypt'' e pq w : nat := w ^ e %% pq.
   
   (* Decryption *)
   Definition decrypt'' d pq w := w ^ d %% pq.

   Lemma eq_dec : forall (p q pq d w: nat) (H: pq = (p * q)%nat), decrypt'' d pq w = decrypt' d p q w.
   Proof.
    Admitted.
  
   Lemma eq_enc : forall (p q pq d w: nat) (H: pq = (p * q)%nat), encrypt'' d pq w = encrypt' d p q w.
   Proof.
   Admitted.

   Theorem rsa_correct'' {p q pq d e : nat} (H: pq = (p * q)%nat) (wf : wf_type p q pq d e) w :
    let r := Build_rsa wf in
    decrypt'' e pq (encrypt'' d pq w)  = w %[mod pq].
  Proof.
    rewrite (eq_dec p q _ _ _ H).
    rewrite (eq_enc p q _ _ _ H).
    rewrite (enc_eq wf) (dec_eq wf) /=.
    rewrite [X in _ %% X = _ %% X]H.
    apply rsa_correct.
  Qed.

  Definition sk0 : SecKey := (1,1)%g.
  Definition pk0 : PubKey := (1,1)%g.
  Definition sig0 : Signature := 1%g.
  Definition m0 : Message := 1%g.
  Definition chal0 : Challenge := 1%g.

  
  #[export] Instance positive_SecKey : Positive #|SecKey|.  
  Proof.
    apply /card_gt0P. exists sk0. auto.
  Qed.
  Definition SecKey_pos : Positive #|SecKey| := _ .
  
  #[export] Instance positive_PubKey : Positive #|PubKey|. 
  Proof.
    apply /card_gt0P. exists pk0. auto.
  Qed.
  Definition PubKey_pos : Positive #|PubKey| := _.

  #[export] Instance positive_Sig : Positive #|Signature|.   
  Proof.
    apply /card_gt0P. exists sig0. auto.
  Qed.
  Definition Signature_pos: Positive #|Signature| := _.

  #[export] Instance positive_Message : Positive #|Message|.   
  Proof.
    apply /card_gt0P. exists m0. auto.
  Qed.
  Definition Message_pos : Positive #|Message| := _.

  #[export] Instance positive_Chal : Positive #|Challenge|.   
  Proof.
    apply /card_gt0P. exists chal0. auto.
  Qed.
  Definition Challenge_pos : Positive #|Challenge| := _.


  Definition chSecKey  : choice_type := 'fin #|SecKey|.
  Definition chPubKey : choice_type := 'fin #|PubKey|.
  Definition chSignature : choice_type := 'fin #|Signature|.
  Definition chMessage : choice_type := 'fin #|Message|.
  Definition chChallenge : choice_type := 'fin #|Challenge|.
  Print chChallenge.

  Definition i_sk := #|SecKey|.
  Definition i_pk := #|SecKey|.
  Definition i_sig := #|Signature|.  

End RSA_KeyGen.

Module RSA_KeyGen_code (π1  : RSA_params) (π2 : KeyGenParams π1)
    <: KeyGen_code π1 π2.
  Import π1 π2.
  Module KGP := KeyGenParams_extended π1 π2.
  Module KG := RSA_KeyGen π1.
  Import KGP KG.

  Import PackageNotation.  
  Local Open Scope package_scope.

  Lemma prime2 (num : 'I_n.+3) (H: 2 = num) : prime num.
  Proof.
    rewrite -H. reflexivity.
  Qed. 

  Lemma two_smaller_three : forall n,  2 < n.+3.
  Proof.
    intro n.
    destruct n.
    - reflexivity.
    - reflexivity. 
  Qed.

  Definition two : 'I_n.+3 := Ordinal (two_smaller_three n ).
  
  Definition p0 : prime_num := exist _ two (prime2 two eq_refl).
  
  Definition i_P := #|P|.
  Instance pos_i_P : Positive i_P.
  Proof.
   apply /card_gt0P. exists p0. auto.
  Qed.

  Fail Definition cast (p : Arit (uniform i_P) ) :=
    otf p.

  Definition cast (p : prime_num ) : 'I_n.+3 := 
    match p with 
    | exist x _ => x
    end.

  Fail Equations? KeyGen:
    code Key_locs [interface] chChallenge :=
    KeyGen :=
    {code
      p ← sample uniform P ;; 
      let p' := enum_val p in
      q ← sample uniform (P' p') ;;
      let q' := enum_val q in
      let p2 := cast p' in
      let q2 := cast q' in
      let sk := fto (p2 * q2)%g in   
      ret sk
    }.

  Lemma n_smaller_nn : forall n : nat, n.+3 <= (n*n).+3.
  Proof.
    intro n. 
    Search ( _ < _ ). 
    Search injective ( _ < _ ).
    Admitted.


  Definition mult_cast (a b : 'I_n.+3) : R :=  
     ((widen_ord (n_smaller_nn n) a) * (widen_ord (n_smaller_nn n) b))%g.

  Equations? KeyGen :
    code Key_locs [interface] (chPubKey × chSecKey) :=
    KeyGen :=
    {code
      p ← sample uniform P ;; 
      let p := enum_val p in
      q ← sample uniform P ;;
      (*#assert (p != q) ;;*)
      let q := enum_val q in
      let p := cast p in
      let q := cast q in
      let sk := mult_cast p q in 
      #put sk_loc := (fto (sk,sk)) ;;
      #put pk_loc := (fto (sk,sk)) ;;
      ret ( (fto (sk,sk)) , fto (sk,sk) )
    }.
    Defined.

End RSA_KeyGen_code.

Module RSA_SignatureAlgorithms (π1  : RSA_params) (π2 : KeyGenParams π1)
<:SignatureAlgorithms π1 π2.
Import π1 π2.
Module KGP := KeyGenParams_extended π1 π2.
Module KG := RSA_KeyGen π1.
Import KGP KG.

  Lemma dec_smaller_n : forall (d pq m : R),  (decrypt'' d pq m) < (n*n).+3.
  Proof.
    Admitted.

  Lemma enc_smaller_n : forall (e pq m : R),  (encrypt'' e pq m) < (n*n).+3.
  Proof.
    Admitted.
  
  Definition dec_to_In  (d pq m : R) : R := Ordinal (dec_smaller_n d pq m). 
  Definition enc_to_In  (e pq m : R) : R := Ordinal (enc_smaller_n e pq m). 

  Definition Sign : ∀ (sk : chSecKey) (m : chMessage), chSignature := 
    fun (sk : chSecKey) (m : chMessage) => fto ( enc_to_In (fst (otf sk)) (snd (otf sk)) (otf m )).

  Definition Ver_sig : ∀ (pk :  chPubKey) (sig : chSignature) (m : chMessage), 'bool :=
    fun (pk :  chPubKey) (sig : chSignature) (m : chMessage)
       => ( dec_to_In (fst (otf pk)) (snd (otf pk)) (otf sig )) == (otf m).

  Theorem Signature_prop:
    ∀ (l: {fmap (chSignature  * chMessage ) -> 'unit})
      (s : chSignature) (pk : chPubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).
  Proof.
    intros l s pk m.
    rewrite /domm/unzip1. 
    rewrite /Ver_sig/dec_to_In/decrypt''/otf/enum_val. 
    destruct pk. 
    simpl.
    destruct l. simpl.
    Search (_ \in fset _).
    



  Proof.
  rewrite /Ver_sig/dec_to_In.
  

End RSA_SignatureAlgorithms.