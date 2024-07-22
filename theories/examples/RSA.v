From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq fintype zmodp prime finset.
Set Warnings "notation-overridden,ambiguous-paths".

From extra Require Import rsa.

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
  Definition prime_num : finType := {x: 'I_n.+1 | prime x}.
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

  Definition R := Finite.clone _ 'I_n.+1.
  Locate choice_type.
  Print Crypt.choice_type.
  
  Definition chR : choice_type := 'fin (mkpos pos_n).
  Definition Z_n_prod : choice_type := (chR × chR).

  Definition SecKey := Z_n_prod.  
  Definition PubKey := Z_n_prod.
  Definition Signature := R.
  Definition Message := R.
  Definition Challenge := R.
  
End RSA_params.

Module RSA_KeyGen (π1  : RSA_params)  
    <: KeyGeneration  π1.

  Import π1.

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
    apply /card_gt0P. exists ch0. auto.
  Qed.
  Definition Challenge_pos : Positive #|Challenge| := _.



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

  Definition chSecKey  : choice_type := 'fin #|SecKey|.
  Definition chPubKey : choice_type := 'fin #|PubKey|.
  Definition chSignature : choice_type := 'fin #|Signature|.
  Definition chMessage : choice_type := 'fin #|Message|.
  Definition chChallenge : choice_type := 'fin #|Challenge|.

  Definition i_sk := #|SecKey|.
  Definition i_pk := #|SecKey|.
  Definition i_sig := #|Signature|.  

  Import PackageNotation.
  
  Local Open Scope package_scope.
  
  Definition i_P := #|P|.
  Instance pos_i_P : Positive i_P.
  Proof.
  Admitted. 

  Locate predArgType.
  Print enum_val.
  Locate enum_val.

  Fail Definition cast (p : Arit (uniform i_P) ) : prime_num :=
    otf p.

  Definition cast (p : Arit (uniform i_P) ) : prime_num :=
    enum_val p.

  Definition KeyGen {L : {fset Location}} :
  code L [interface] (chPubKey × chSecKey) :=
  {code
    p ← sample uniform i_P ;; 
    let p' := cast p in   
    let sk := (p',p') in
    let pk := (p',p') in    
    ret (sk, pk)
  }.
 


End RSA_KeyGen.


Module RSA_params (π1 : SignatureParams) 
    <: KeyGeneration π1.

Import π1.

  (* Encryption *)
  Definition encrypt' e p q w : nat := w ^ e %% (p * q ).

  Definition wf_type p q pq e d := [&& prime p, prime q, p != q,
    0 < pq, p.-1 %| pq, q.-1 %| pq &
    e * d == 1 %[mod pq]].

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
 

End RSA_params.

Module RSA_SignatureAlgorithms 
(π1 : SignatureParams)
(π3 : KeyGeneration π1) <: SignatureAlgorithms π1 π3.

  Definition Sign := encrypt'.

  Definition Ver_sig := decrypt'.

  (*
  Theorem Signature_prop :
    ∀ (l: {fmap (Signature  * w ) -> 'unit}) 
      (s : Signature) (d : nat) (w : nat),
      Ver_sig pk s m = ((s,m) \in domm l).
  *)

End RSA_SignatureAlgorithms.
