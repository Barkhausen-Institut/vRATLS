(****** Trying something else for RSA *)
 (*Require Import Coq.Prime.Prime.*) (*CoqPrime needs to be installed?*)

 (*RSA keyGen proof
 Prime Selection: Two large primes p & q selected. 
 Modulus n: Comp n=p*q.
 phi_n = (p-1)*(q-1).
 e: gcd(e, phi_n) =1.
 *)
 Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zdiv.
Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import NZAxioms.
Require Import NZPow.

Section RSA.
(* Two prime numbers p and q *)
    Variables (p q : Z).
    Hypothesis prime_p : prime p.
    Hypothesis prime_q : prime q. 

(* n is the product of p and q *)
    Definition n := p * q.

(* Totient function phi(n) = (p-1) * (q-1) *)
    Definition phi_n := (p -1) * (q - 1).

(* Public exponent e, which is coprime with phi(n) *)
  Variable e : Z.
  Hypothesis e_coprime_phi_n : Z.gcd e phi_n = 1.

(* Private exponent d, such that e * d ≡ 1 mod phi(n) *)
  Variable d : Z.
  Hypothesis d_mod_inv : (e * d) mod phi_n = 1.

(* Message m, which is less than n *)
  Variable m : Z.
  Hypothesis m_lt_n : 0 <= m < n.



(* The encryption function: c = m^e mod n *)

(*Error (wont work withZdiv either) with this:   Definition encrypt (m : Z) := Z.pow_mod m e n.*)
  Definition mod_exp (m e n : Z) : Z :=
  Z.pow m e mod n.

(* Now use this definition in the encrypt function *)
Definition encrypt (m : Z) : Z :=
  mod_exp m e n.


  (* The decryption function: m' = c^d mod n *)
Definition decrypt (c : Z) : Z :=
  mod_exp c d n.

 (* Prove that decrypting an encrypted message returns the original message i.e. decrypt(encryptm)dn=m. *)
Theorem rsa_correct : decrypt (encrypt m) = m.
Proof.
    unfold encrypt, decrypt, mod_exp.
Abort.


(*Def Sig & Verifi
**The signature is created by raising the m to the power d modulo n. 
The verification checks whether the msg equals the signature raised to the power e modulo n. *)

(* Signature: s = m^d mod n *)
Definition sign (m d n : Z) : Z :=
  Z.pow m d mod n.

(* Verification: Check if m = s^e mod n *)
Definition verify (s e n : Z) : Z :=
  Z.pow s e mod n.

(* Stupid lemma to show exponentiation properties *)
  Lemma pow_mod_equiv : forall (a b m : Z),
      m > 0 -> (a ^ b) mod m = ((a mod m) ^ b) mod m.
  Proof.
    intros a b m1 H.
    (* this stupid property can't be found anywwhere*)
    Print Coq.ZArith.Zdiv. Search ( (_ ^ ?x) = _)%Z.
    rewrite <- Z.pow_mod.
    
    apply Z.pow_mod.
    exact H.
  Qed.

(*To prove that verifying the signature produced by signing the message will return 
the original message, i.e.,  m = (m^d)^e mod n *)

Theorem rsa_signature_correct : verify (sign m d n) e n = m.
Proof.
  unfold sign, verify.
  (*assert (H1: (Z.pow m d)^e = Z.pow m (d * e)). *)
  assert (H1: Z.pow (Z.pow m d mod n) e = Z.pow m (d * e) mod n).
  rewrite Z.pow_mod.


  Print Z.pow.



End RSA.







