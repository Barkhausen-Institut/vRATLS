From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq fintype.
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

From vRATLS Require Import Signature.

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.


Module Type RSA_params <: SignatureParams.

  Parameter A : Type.
  Parameter pq : A -> nat.

  (*
  Record rsa := { 
    p : nat;
    q : nat;
   pq : nat;
    e : nat;
    d : nat; 
   wf : [&& prime p, prime q, p != q,
            0 < pq, p.-1 %| pq, q.-1 %| pq &
            e * d == 1 %[mod pq]]}.

  Print rsa.
*)

  (*
  Definition n {r} := (pq r).
  Definition R {r}:= [finType of 'Z_n].
  *)

  Definition wf_type p q pq e d := [&& prime p, prime q, p != q,
  0 < pq, p.-1 %| pq, q.-1 %| pq &
  e * d == 1 %[mod pq]].

  Local Open Scope ring_scope.
  Import GroupScope GRing.Theory.

  Variable n : nat.

  Definition R := [finType of 'Z_n].
  Definition Z_n_prod := [finType of ('Z_n * 'Z_n)].
  Definition Z_n_prod' := [finType of ('Z_(n*n))].

  Local Open Scope ring_scope. 

  Definition SecKey    : finType := Z_n_prod.  
  Definition PubKey    : finType := Z_n_prod.
  Definition Signature : finType := R.
  Definition Message   : finType := R.
  Definition Challenge : finType := R.

  Definition sk0  : SecKey := (0,0).
  Definition pk0  : PubKey := (0,0).
  Definition sig0 : Signature := 0%R.
  Definition m0   : Message := 0%R.
  Definition ch0  : Challenge := 0%R.

End RSA_params.



Module RSA_KeyGen (π1 : RSA_params) 
    <: KeyGeneration π1.

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

  Definition KeyGen {L : {fset Location}} :
  code L [interface] (chPubKey × chSecKey) :=
  {code
    p ← sample uniform i_pk ;;
    q ← sample uniform i_pk ;;
    e ← sample uniform i_sk ;;
    d ← sample uniform i_sk ;;
    
    assert (prime p) ;;
    assert (prime p) ;;
    ret (p,p)
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
