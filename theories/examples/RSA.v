From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
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

Module Type RSA_Key_Gen_params.

  (* currently useless *)
  Parameter Z_n : finType.
  Parameter Z_n_pos : Positive #|Z_n|.
  #[local] Existing Instance Z_n_pos.
  Definition chZ_n := 'fin #|Z_n|.
  Definition i_Z_n := #|Z_n|.

End RSA_Key_Gen_params.

Module Type RSA_params
    (π1 : SignatureParams) 
    (π2 : SignatureConstraints) 
    (π3 : KeyGeneration π1 π2)
    (π4 : RSA_Key_Gen_params).

  Import π1 π2 π3 π4.

  Record rsa := { 
    p : nat;
    q : nat;
    pq : nat;
    e : nat;
    d : nat; 
    wf : [&& prime p, prime q, p != q,
            0 < pq, p.-1 %| pq, q.-1 %| pq &
            e * d == 1 %[mod pq]]}.
Check e.
  (** Encryption *)
  Definition encrypt' e p q w : nat := w ^ e %% (p * q ).

  Check encrypt'.

  Theorem enc_eq : forall e p q r w,  encrypt' e p q w = encrypt r w.
  Proof.
    intros. rewrite /encrypt/encrypt'.
    rewrite /(rsa.e r). 
    (* 
    rewrite /rsa.e/rsa.p/rsa.q.
    *)
  Admitted.

  
  (** Decryption *)
  Definition decrypt' d p q w := w ^ d %% (p * q).

  Theorem dec_eq : forall d p q r w, decrypt' d p q w = decrypt r w.
  Proof.
  Admitted.

  Theorem rsa_correct' d e p q pq w : 
    [&& prime p, prime q, p != q,
    0 < pq, p.-1 %| pq, q.-1 %| pq &
    e * d == 1 %[mod pq]] ->
    decrypt' e p q (encrypt' d p q w)  = w %[mod p * q].
  Proof.
    intros. 
    (*apply /eqP.*)
    rewrite enc_eq.
    
    rewrite /decrypt'/encrypt'.
    
  Qed.
  
  Definition Sign : ∀ (d : SecKey) (m : chMessage), Signature :=
    let (d',p',q',wf',pq') := d in
    let e' := 1 in
    let r := rsa p' q' pq' e' d' wf'
    in encrypt d pq m.

  Definition Ver_sig : ∀ (e :  PubKey) (sig : Signature) (m : chMessage) (r:rsa), 
      'bool.
  
  Definition sk : SecKey := d.

End RSA_params.

Module rsa_alg <: SignatureAlgorithms.

  Definition Sign : ∀ (sk : SecKey) (m : chMessage), Signature :=
    encrypt m sk.

  Parameter Ver_sig : ∀ (pk :  PubKey) (sig : Signature) (m : chMessage), 
   'bool.

  (* TODO: fmap (Signature * A * A ) -> (Signature * A * A )  triggert endless loop  *)

  (* Final proposition for a signature scheme to be indistinguishable *)
  Parameter Signature_prop:
    ∀ (l: {fmap (Signature  * chMessage ) -> 'unit}) 
      (s : Signature) (pk : PubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).

  End rsa_alg.

  

  

End