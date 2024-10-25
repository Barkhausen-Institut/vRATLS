From Relational Require Import OrderEnrichedCategory GenericRulesSimple.
From mathcomp Require Import all_ssreflect.

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
From extructures Require Import ord fset fmap ffun.

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


Module Type RSA_params <: SignatureParams.

  (* Message space *)
  Variable w : nat.

  (* Sampling space *)
  Variable n : nat.

  Definition pos_n : nat := 2^n.

  Definition r₀ : nat := n.+4.+2.
  (* We need to have at least two primes [p] and [q].
     Indeed, the conditions for phi_N force us to have
     at least prime numbers 2,3 and 5!
   *)
  Definition R₀ : Type := 'I_r₀.
  Definition r : nat := r₀ * r₀.
  Definition R : Type := 'I_r.

  (* the set of prime numbers. *)
  Definition prime_num : finType := {x: R₀  | prime x
                                              (* &  odd x (* --> excludes prime 2 and gives e=7 (smallest)  *) *)
    }.
  Definition P : {set prime_num} := [set : prime_num].

  Lemma two_ltn_r₀ : 2 < r₀.
  Proof. by rewrite /r₀; case: n. Qed.

  Definition two : R₀ := Ordinal two_ltn_r₀.
  Lemma prime2ord : prime two. Proof. by []. Qed.
  Definition two' : prime_num := exist _ two prime2ord.

  Lemma three_ltn_r₀ : 3 < r₀.
  Proof. by rewrite /r₀; case: n. Qed.

  Definition three : R₀ := Ordinal three_ltn_r₀.
  Lemma prime3ord : prime three. Proof. by []. Qed.
  Definition three' : prime_num := exist _ three prime3ord.
  Lemma five_ltn_r₀ : 5 < r₀.
  Proof. by rewrite /r₀; case: n. Qed.

  Definition five : R₀ := Ordinal five_ltn_r₀.
  Lemma prime5ord : prime five. Proof. by []. Qed.
  Definition five' : prime_num := exist _ five prime5ord.

  (*
    This definition accounts for two properties:
    1. [p <> q] such that the primes are not equal and
    2. [2 < p.-1 * q.-1] such that we at the very least draw
       one number [e] from this space.
       Since, in this new space [phi_N = p.-1 * q.-1] we also
       require that [e] is coprime to the space itself, i.e.,
       [coprime e phi_N] we arrive that smallest possible
       [e=3] when [p=2] and [q=5] because
       [2.-1 * 5.-1 = 1 * 4 = 4].
   *)
  Definition P' (y : prime_num) := (* (P :\ y)%SET. *)
    let P_no_y := (P :\ y)%SET in
    if y == two' then (P_no_y :\ three')%SET
    else if y == three' then (P_no_y :\ two')%SET
         else P_no_y.

  Lemma notin_m {T:finType} (a b:T) (Q:{set T}):
    a \notin Q -> a \notin (Q :\ b)%SET.
  Proof.
    move => a_notin_Q.
    rewrite in_setD.
    by apply/nandP; right.
  Qed.

  Lemma P_P'_neq : forall y, y \in P -> P :!=: P' y.
  Proof.
    rewrite /P' => y y_in_P.
    rewrite eqtype.eq_sym.
    apply proper_neq.
    case: (y == two').
    - apply/properP.
      split.
      * by [].
      * exists y => //=.
        apply notin_m.
        rewrite in_setD.
        apply/nandP; left.
        rewrite negbK.
        exact: set11.
    - case: (y == three').
      * apply/properP.
        split.
        + by [].
        + exists y => //=.
          apply notin_m.
          rewrite in_setD.
          apply/nandP; left.
          rewrite negbK.
          exact: set11.
      * by apply properD1.
  Qed.

  Lemma p_q_neq p q (p_in_P: p \in P) :
    q \in P' p -> p <> q.
  Proof.
    rewrite /P'.
    case: (p == two').
    - rewrite in_setD1; move/andP; case => _.
      by rewrite in_setD1; move/andP; case; move/eqP/nesym.
    - case: (p == three');
        [rewrite in_setD1; move/andP; case => _|];
        by rewrite in_setD1; move/andP; case; move/eqP/nesym.
  Qed.

  Definition i_P := #|P|.
  Instance pos_i_P : Positive i_P.
  Proof.
    apply /card_gt0P. by exists two'.
  Qed.

  #[export] Instance positive_P' `(p:prime_num) : Positive #|(P' p)|.
  Proof.
    apply/card_gt0P.
    case H: (p == two'); move/eqP: H.
    - move => H; rewrite H; exists five'.
      rewrite /P'.
      case: (two' == two');
        try repeat rewrite in_setD1 //=.
      apply in_setT.
    - move => H₂.
      rewrite /P'.
      rewrite ifF.
      + case H₃: (p == three'); move/eqP: H₃ => H₃.
        * rewrite H₃.
          exists five'.
          repeat rewrite in_setD1 //=; apply/andP; split.
        * exists two'.
          rewrite in_setD1.
          apply/andP; split; [by apply/eqP/nesym | apply in_setT].
      + by apply/eqP.
  Qed.

  Lemma p_q_neq' (p: 'fin P) (q: 'fin (P' (enum_val p))) : enum_val p != enum_val q.
  Proof.
    apply/eqP.
    apply p_q_neq; try apply/enum_valP.
  Qed.

  (*
  Definition X (m:nat) : finType := 'I_m.+3.
   The above is insufficient. I want to sample an [e] from a space
     such that [1 < e < phi_N] where
     [phi_N = lcm p.-1 q.-1] for Carmichael's totient function or
     [phi_N = p.-1 * q.-1] for Euler's totient function.
     That is [phi_N = totient p * totient q] by [totient_prime].
     And [phi_N = totient (p * q)] by [totient coprime] given [coprime p q].
     That is [phi_N = totient n].
  Search "totient".
  Search coprime prime.
   *)
  Definition E' {m:R} (H:2<m) : finType := { x: 'Z_m | (1 < x) && (coprime m x)}.
  Definition E  {m:R} (H:2<m) : {set (E' H)} := [set : E' H].

  (* Lemma two_ltn_E {m:R} (H:2<m) : 2 < m. Proof. exact:H. Qed. *)

  (* Definition two_Zp (m:R): 'Z_m := inZp 2. *)
  (* Lemma two_gt1 {m:R} (H:2<m) : (1 < two_Zp m)%Z. *)
  (* Proof. *)
  (*   move => //=. *)
  (*   case: m H; case => [|m0] _ //=. *)
  (*   rewrite ltnS /Zp_trunc //=. *)
  (*   case: m0 => [|m1] //=. *)
  (*   rewrite ltnS. *)
  (*   by case: m1. *)
  (* Qed. *)

  (* Definition two_E {m:R} (H:2<m) : (E' H) := *)
  (*   exist _ (two_Zp m) (two_gt1 H). *)

  (* #[export] Instance positive_E {m:R} (H:2<m): Positive #|(E H)|. *)
  (* Proof. apply/card_gt0P; by exists (two_E H). Qed. *)

  (* (* *)
  (* Equations D' (H:{m:R | 2<m}) : finType := *)
  (*   D' (exist H) := E' H. *)
  (*  *) *)
  (* Definition D' (H:{m:R | 2<m}) : finType := *)
  (*   match H with *)
  (*     | exist _ H₀ => E' H₀ *)
  (*   end. *)

  (* Definition D (H:{m:R | 2<m}) : {set (D' H)} := [set : D' H]. *)

  (* Equations two_D (H:{m:R | 2<m}) : (D' H) := *)
  (*   two_D (exist H0) := two_E H0. *)

  (* #[export] Instance positive_D (H :{m:R | 2<m}) : Positive #|(D H)|. *)
  (* Proof. apply/card_gt0P; by exists (two_D H). Qed. *)


  (* Fail Equations C' (H:{m:R | 2<m}) : finType := *)
  (*   C' H with H => { *)
  (*       | (@exist m H₀) := { x:(D' H) | coprime (proj1_sig x) m } *)
  (*     }. *)


  (* (* *)
  (* Definition A₀ {m:nat} (H:2<m) : finType := {x: 'Z_m | 1 < x}. *)
  (* Definition A₁ {m:nat} (H:2<m) : finType := {x: 'Z_m | coprime x m}. *)
  (* Fail Definition A₂ {m:nat} (H:2<m) : finType := {x: 'Z_m | coprime x m ∧ 1 < x}. *)
  (* Definition A₂ {m:nat} (H:2<m) : finType := {x: 'Z_m | coprime x m && (1 < x)}. *)
  (* *) *)
  (* Definition A₀ {m:R} (H:2<m) : finType := {x: 'Z_m | 1 < x}. *)
  (* Definition A₁ {m:R} (H:2<m) : finType := {x: 'Z_m | coprime x m}. *)
  (* Definition C' {m:R} (H:2<m) : finType := {x: 'Z_m | coprime x m && (1 < x)}. *)

  (* Equations C' (H:{m:R | 2<m}) : finType := *)
  (*   C' H with H => { *)
  (*     | (@exist m H₀) := { x:(D' H) | coprime _ m } *)
  (*     }. *)
  (* Next Obligation. *)
  (*   move => H m P_m. *)
  (*   rewrite /D'. *)
  (*   case: H => x H₀. *)
  (*   exact: proj1_sig. *)
  (* Defined. *)

  (* Definition C (H:{m:R | 2<m}) : {set (C' H)} := [set : C' H]. *)

  Definition m_pred (m:R) : 'Z_m := inZp m.-1.
  Lemma m_pred_gt1' {m:R} (m_gt2:2<m) : (1 < m_pred m)%Z.
  Proof.
    rewrite /m_pred.
    case: m m_gt2; case => n0 n0_lt_r //.
    move => H.
    apply/ltnSE => //.
    simpl. (* removes [inZp] *)
    rewrite prednK.
    - simpl.
      rewrite modn_small //.
    - rewrite -pred_Sn.
      move/ltnSE/ltnW:H.
      exact: id.
  Qed.

  Lemma m_pred_gt1 (H:{m:R | 2<m}) : (1 < m_pred (proj1_sig H))%Z.
  Proof.
    case: H => m m_gt2.
    rewrite /sval.
    by apply m_pred_gt1'.
  Qed.

  Lemma m_pred_coprime' {m:R} (m_gt2: 2<m) : coprime m (m_pred m).
  Proof.
    rewrite /sval/m_pred.
    simpl.
    rewrite prednK.
    - rewrite modn_small.
      + apply coprimenP. move/ltnW/ltnW: m_gt2. exact: id.
      + exact: ltnSn.
    - exact: is_positive.
  Qed.

  Lemma m_pred_coprime (H:{m:R | 2<m}) : coprime (proj1_sig H) (m_pred (proj1_sig H)).
  Proof.
    case: H => m m_gt2.
    by apply m_pred_coprime'.
  Qed.

  (* Equations m_pred_C' (H:{m:R | 2<m}) : (D' H) := *)
  (*   m_pred_C' H with H => { *)
  (*     | (@exist m H₀) := exist _ (m_pred m) (m_pred_gt1' H₀) *)
  (*     }. *)

  (* Fail Equations m_pred_C (H:{m:R | 2<m}) : (C' H) := *)
  (*   m_red_C H := exist _ (m_pred_C' H) (m_pred_coprime H). *)

  (* Equations m_pred_C (H:{m:R | 2<m}) : (C' H) := *)
  (*   m_pred_C H := _ . *)
  (* Next Obligation. *)
  (*   move => H. *)
  (*   rewrite /C'/C'_clause_1. *)
  (*   case: H => x x_gt2. *)
  (*   exists (m_pred_C' (exist _ x x_gt2)). *)
  (*   rewrite /m_pred_C'/m_pred_C'_clause_1. *)
  (*   rewrite /C'_obligations_obligation_1. *)
  (*   rewrite /sval. *)
  (*   rewrite coprime_sym. *)
  (*   exact: m_pred_coprime'. *)
  (* Qed. *)

  (* #[export] Instance positive_C (H :{m:R | 2<m}) : Positive #|(E H)|. *)
  (* Proof. apply/card_gt0P; by exists (m_pred_C H). Qed. *)

  Lemma m_pred_all {m:R} (m_gt2: 2<m) : (1 < m_pred m)%Z && coprime m (m_pred m).
  Proof.
    apply/andP.
    by split; [apply m_pred_gt1' | apply m_pred_coprime'].
  Qed.

  Definition m_pred_E {m:R} (H:2<m) : (E' H) :=
    exist _ (m_pred m) (m_pred_all H).

  #[export] Instance positive_E {m:R} (H:2<m): Positive #|(E H)|.
  Proof. apply/card_gt0P; by exists (m_pred_E H). Qed.

  Definition R' : finType := {x:R | 0 < x}.

  Definition wf_type p q phi_N e d := [&& prime p, prime q, p != q,
      0 < phi_N, p.-1 %| phi_N, q.-1 %| phi_N &
                            e * d == 1 %[mod phi_N]].

  Definition Z_n_prod : finType := prod_finType R' R.

  Definition SecKey := Z_n_prod.
  Definition PubKey : finType := Z_n_prod.
  Definition Signature : finType := R.
  Definition Message : finType := R. (* TODO should just be a space that is bounded by another bound *)
  Definition Challenge : finType := R.
(*  Definition E_space : finType := E. *)

  (**
     We need to tanslate a message into the "RSA" space.
   *)
  Parameter padd : forall (pq:nat) (m:Message), 'I_pq.

End RSA_params.

Module RSA_KeyGen (π1  : RSA_params)
    <: KeyGenParams π1.

  Import π1.

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

   Lemma eq_dec (p q pq d w: nat) (H: pq = (p * q)%nat) : decrypt'' d pq w = decrypt' d p q w.
   Proof.
     by rewrite /decrypt''/decrypt' H.
   Qed.

   Lemma eq_enc (p q pq d w: nat) (H: pq = (p * q)%nat) : encrypt'' d pq w = encrypt' d p q w.
   Proof.
     by rewrite /encrypt''/encrypt' H.
   Qed.

   Theorem rsa_correct''
     {p q pq d e : nat}
     (H: pq = (p * q)%nat)
     (wf : wf_type p q
             (p.-1 * q.-1) (* phi_N based on Euler totien function instead of lcm *)
             d e) w :
    let r := Build_rsa wf in
    decrypt'' e pq (encrypt'' d pq w)  = w %[mod pq].
  Proof.
    rewrite (eq_dec p q _ _ _ H).
    rewrite (eq_enc p q _ _ _ H).
    rewrite (enc_eq wf) (dec_eq wf) /=.    rewrite [X in _ %% X = _ %% X]H.
    apply rsa_correct.
  Qed.

  Lemma pq_phi_gt_0 : forall p q, prime p -> prime q -> 0 < p.-1 * q.-1.
  Proof.
    by case => [] // [] // p1; case => [] // [].
  Qed.

  Definition sk0 : SecKey := (exist _ 1%R (ltn0Sn 0), 1)%g.
  Definition pk0 : PubKey := (exist _ 1%R (ltn0Sn 0), 1)%g.
  Definition sig0 : Signature := 1%g.
  Definition m0 : Message := 1%g.
  Definition chal0 : Challenge := 1%g.
(*  Definition ss0 :Sample_space := 1%g. *)


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

  (*
  #[export] Instance positive_Sample : Positive #|Sample_space|.
  Proof.
    apply /card_gt0P. exists ss0. auto.
  Qed.
  Definition Sample_pos : Positive #|Sample_space| := _.
   *)

  Definition chSecKey  : choice_type := 'fin #|SecKey|.
  Definition chPubKey : choice_type := 'fin #|PubKey|.
  Definition chSignature : choice_type := 'fin #|Signature|.
  Definition chMessage : choice_type := 'fin #|Message|.
  Definition chChallenge : choice_type := 'fin #|Challenge|.

  Definition i_sk := #|SecKey|.
  Definition i_pk := #|SecKey|.
  Definition i_sig := #|Signature|.
  (* Definition i_ss := #|Sample_space|.*)

End RSA_KeyGen.

Module RSA_KeyGen_code (π1  : RSA_params) (π2 : KeyGenParams π1)
    <: KeyGen_code π1 π2.

  Import π1 π2.
  Module KGP := KeyGenParams_extended π1 π2.
  Module KG := RSA_KeyGen π1.
  Import KGP KG.

  Import PackageNotation.
  Local Open Scope package_scope.

  Fail Definition cast (p : Arit (uniform i_P) ) :=
    otf p.

  Definition cast (p : prime_num ) : R₀ :=
    match p with
    | exist x _ => x
    end.

  Lemma n_leq_nn : r₀ <= r.
  Proof.
    rewrite /r/r₀ -addn1.
    apply leq_pmull.
    by rewrite addn1.
  Qed.

  Lemma yyy : forall a b,
      prime a ->
      prime b ->
      0 < a * b.
  Proof.
    move => a b ap bp.
    rewrite muln_gt0.
    apply/andP.
    split.
    - exact: prime_gt0 ap.
    - exact: prime_gt0 bp.
  Qed.

  Lemma fold_R3 : (π1.n + (π1.n + (π1.n + π1.n * π1.n.+3).+3).+3).+3 = (π1.n.+3 * π1.n.+3)%nat.
  Proof.
    rewrite (addnC π1.n (muln _ _)).
    repeat rewrite -addSn.
    rewrite -[X in (_ + (_ + X))%nat = _]addn3.
    rewrite -/Nat.add plusE.
    rewrite -[X in (_ + (_ + X))%nat = _]addnA.
    rewrite addn3.
    by rewrite -mulSnr -mulSn -mulSn.
  Qed.


  Lemma fold_R4 : (π1.n + (π1.n + (π1.n + (π1.n + π1.n * π1.n.+4).+4).+4).+4).+4 = (π1.n.+4 * π1.n.+4)%nat.
  Proof.
    rewrite (addnC π1.n (muln _ _)).
    repeat rewrite -addSn.
    rewrite -[X in (_ + (_ + (_ + X)))%nat = _]addn4.
    rewrite -/Nat.add plusE.
    rewrite -[X in (_ + (_ + (_ + X)))%nat = _]addnA.
    rewrite addn4.
    by rewrite -mulSnr -mulSn -mulSn -mulSn.
  Qed.

  Lemma fold_R6 :
    (π1.n +
       (π1.n +
          (π1.n +
             (π1.n +
                (π1.n +
                   (π1.n + π1.n * r₀).+2.+4).+2.+4).+2.+4).+2.+4).+2.+4).+2.+4  = (π1.n.+2.+4 * π1.n.+2.+4)%nat.
  Proof.
    rewrite /r₀.
    rewrite (addnC π1.n (muln _ _)).
    repeat rewrite -addSn.
    rewrite -[X in
        (_ + (_ + (_ + (_ + (_ + X)))))%nat = _]addn4.
    rewrite -/Nat.add plusE.
    rewrite -[X in
        (_ + (_ + (_ + (_ + (_ + X)))))%nat = _]addn2.
    rewrite -/Nat.add plusE.
    rewrite -[X in
        (_ + (_ + (_ + (_ + (_ + X)))))%nat = _]addnA.
    rewrite -[X in
        (_ + (_ + (_ + (_ + (_ + X)))))%nat = _]addnA.
    rewrite (addnC 4 2).
    rewrite (addnA _  2 4).
    rewrite addn2.
    rewrite addn4.
    by rewrite -mulSnr -mulSn -mulSn -mulSn.
  Qed.

  Lemma ltn_R : forall (a b: R₀),
      a * b <
        (π1.n +
           (π1.n +
              (π1.n +
                 (π1.n +
                    (π1.n +
                       (π1.n + π1.n * r₀).+2.+4).+2.+4).+2.+4).+2.+4).+2.+4).+2.+4.
  Proof.
    rewrite /R₀/r₀ => a b.
    by rewrite fold_R6 ltn_mul.
  Qed.


  Lemma yyy' {a b:R₀} (ap: prime a) (bp: prime b) :
    0 < ((widen_ord n_leq_nn a) * (widen_ord n_leq_nn b))%R.
  Proof.
    rewrite /widen_ord /=.
    rewrite -/Nat.mul -/Nat.add.
    rewrite plusE multE.
    rewrite modn_small.
    - by apply yyy.
    - by apply ltn_R.
  Qed.

  Lemma yyy'' {a b:R₀} (ap: prime a) (bp: prime b) :
    0 < ((widen_ord n_leq_nn a) * (widen_ord n_leq_nn b))%nat.
  Proof.
    rewrite /widen_ord /=.
    by apply yyy.
  Qed.

  Definition mult_cast (a b : prime_num) : R' :=
    match a,b with
    | exist a' ap , exist b' bp =>
        exist _
          ((widen_ord n_leq_nn a') * (widen_ord n_leq_nn b'))%R (* <-- This [R] is not our [R] but means the Ring. *)
          (yyy' ap bp)
    end.

  Lemma zzz {a b:R₀} : (a * b)%nat < r.
  Proof.
    move: a b; rewrite /R₀/r.
    case => [a a_ltn]; case => [b b_ltn].
    apply ltn_mul; try apply ltn_ord.
  Qed.

  Definition mult_cast_nat (a b : prime_num) : R' :=
    match a,b with
    | exist a' ap , exist b' bp =>
        exist _
          (Ordinal zzz)
     (yyy'' ap bp)
    end.

  Definition phi_N (a b : prime_num) : nat :=
    match a,b with
    | exist a' ap , exist b' bp => a'.-1 * b'.-1
    end.

  (* Lemma phi_N_gt1 (a b: prime_num) (H: a != b) : 1 < phi_N a b. *)
  (* Proof. *)
  (*   rewrite /phi_N. *)
  (*   case: a H => a a_prime; case: b => b b_prime. *)
  (*   Search exist. *)
  (*   move/negP/eqP. *)
  (*   move/EqdepFacts.eq_sig_fst. *)
  (*   move: a b a_prime b_prime. *)
  (*   case => [] // [] // [] // [] // a //=. *)
  (*   Check prime2ord. *)
  (*   Compute (prime 2). *)
  (*   case => [] // [] // [] // [] // b b_ltn_r₀. *)
  (*   move => //=. *)
  (*   Search Nat.pred muln. *)
  (*   Search (_ < _ * _). *)
  (*   apply (ltnW (pq_phi_gt_0 _ _ a_prime b_prime)). *)
  (*   Admitted. *)

  Lemma sub_r_gt_r {r:R₀} (H:0 < r) : r.-1 < r₀.
  Proof.
    case: r H; case => r r_lt_r₀ // => H //=.
    exact: ltnW.
  Qed.

  Definition sub_r {r:R₀} (H:0 < r) : R₀ :=
    Ordinal (sub_r_gt_r H).

  Lemma phi_N_lt_r (a b : prime_num) : phi_N a b < r.
  Proof.
    rewrite /phi_N //.
    case: a => a a_prim; case: b => b b_prim //.
    rewrite /r.
      apply ltn_mul; [move: a_prim | move: b_prim];
    move/prime_gt1/ltnW; exact: sub_r_gt_r.
  Qed.

  Definition phi_N_ord (a b : prime_num) : R :=
    Ordinal (phi_N_lt_r a b).

  (* Lemma e_inv_gt2 {phi:{m:R | 2<m}} (e: C' phi) : 1 <  Zp_inv (proj1_sig e). *)
  (* (* Lemma e_inv_gt2 (m:R) (H:2<m) (e: C' (@exist R H)) : 1 <  Zp_inv (proj1_sig e). *) *)
  (* Proof. *)
  (*   move: e. rewrite /C' //=. *)
  (*   rewrite /C'_clause_1. *)

  (*   (* *)
  (*   have coprime_m : coprime (proj1_sig phi) (m_pred (proj1_sig phi)) by exact: (m_pred_coprime phi). *)
  (*    *) *)
  (*   case: phi e (* coprime_m *); rewrite /sval => m m_ltn2. *)
  (*   rewrite /m_pred. *)
  (*   rewrite /C' //=. *)
  (*   case; case => x one_ltn_x. *)
  (*   rewrite /sval. *)
  (*   Search Zp_inv. *)
  (*   Print Zp_inv. *)

  (*   rewrite /sval //. *)


  (*   case: m H e e_ltn; *)
  (*     do 3! (case => //=). *)
  (*   Search Zp_inv. *)

  (*   Admitted. *)

  (* Equations calc_d {m:R} (H:2<m) (e:C' H) : E' H := *)
  (*   calc_d H (@exist e' ep) := *)
  (*     exist _ (Zp_inv e') (e_inv_gt2 H e'). *)

  Equations e_widen {m:R} (H:2<m) (e:'Z_m) : R :=
    e_widen _ e := widen_ord _ e.
  Next Obligation.
    rewrite /R/r/E'/Zp_trunc //.
    move => [m m_lt_r] H [e e_gt1] //=.
    repeat rewrite prednK.
    - exact: (ltnW m_lt_r).
    - exact: ltnW (ltnW H).
    - rewrite -ltnS prednK.
      + exact: ltnW H.
      + exact: ltnW (ltnW H).
  Defined.

  Equations calc_d (phi: {m:R | 2<m}) (e:E' (proj2_sig phi)) : 'Z_(proj1_sig phi) :=
    calc_d (exist H) (@exist e' ep) := Zp_inv e' .

  Equations phi_N_ord' (p: 'fin P) (q: 'fin (P' (enum_val p))) : {m:R | 2 < m} :=
    phi_N_ord' p q := exist _ (phi_N_ord (enum_val p) (enum_val q)) _.
  Next Obligation.
    move => p' q'.
    rewrite /phi_N_ord/phi_N //=.

    have p_in_P : enum_val p' \in P := enum_valP p'.
    have q_in_P' : enum_val q' \in (P' (enum_val p')) := enum_valP q'.
    have p_q_neq: enum_val p' \in P -> enum_val q' \in P' (enum_val p') -> enum_val p' <> enum_val q' := (p_q_neq (enum_val p') (enum_val q')).
    move:p_q_neq p_in_P q_in_P'.

    case: (enum_val q') => /= => q'' q_prime.
    case: (enum_val p') => /= => p'' p_prime.

    case: p'' p_prime => //=; case => //=; case => //=.
    case.
    - (* [p = 2] *)
      case: q'' q_prime => //=; case => //=; case => //=.
      case.
      + (* [q = 2] => discard by [P'] *)
        move => q_lt_r₀ q_prime.
        move => p_lt_r₀ p_prime.
        move => p_q_neq p_in_P q_in_P'.

        specialize (p_q_neq p_in_P q_in_P').

        have p_q_eq: Ordinal (n:=r₀) (m:=2) p_lt_r₀ = Ordinal (n:=r₀) (m:=2) q_lt_r₀ by
          clear; apply/eqP; exact: eq_refl. (* <- eqType (proof irrelevance) *)

        have prime_p: prime (Ordinal (n:=r₀) (m:=2) p_lt_r₀) by [].
        have prime_q: prime (Ordinal (n:=r₀) (m:=2) q_lt_r₀) by [].

        have p_q_eq':
          exist (λ x : 'I_r₀, prime x) (Ordinal (n:=r₀) (m:=2) p_lt_r₀) prime_p
            = exist (λ x : 'I_r₀, prime x) (Ordinal (n:=r₀) (m:=2) q_lt_r₀) prime_q :=
          @boolp.eq_exist _ (λ x : 'I_r₀, prime x) _ _ prime_p prime_q p_q_eq.

        have p_prime_eq : prime_p = p_prime by [].
        have q_prime_eq : prime_q = q_prime by [].

        move: p_q_neq p_q_eq'.

        by rewrite p_prime_eq q_prime_eq.

      + (* [q = n.+3] *)
        case.
        * (* [q = 3] => [2 < 1 * 2] => discard by [P'] *)

          move => q_lt_r₀ q_prime.
          move => p_lt_r₀ p_prime.
          move => p_q_neq p_in_P.

          rewrite /P'/three'/three  //=.
          have prime3_eq: q_prime = prime3ord by [].
          rewrite prime3_eq.
          rewrite in_setD.
          move/andP; case.
          have three_ltn_r₀_eq : q_lt_r₀ = three_ltn_r₀ by [].
          rewrite three_ltn_r₀_eq.
          move/negP.

          by rewrite in_set1.

        * (* [q = n.+3] => [2 < 1 * n.+3] => solve *)
          by [].
    - (* [p = n.+3] *)
      (* discard non-prime cases *)
      case: q'' q_prime => //=; case => //=; case => //=.
      (* now solve *)
      case.
      + (* [q = 2] => [2 < n.+2 * 1]  *)
        move => q_lt_r₀ q_prime.
        case.
        * (* [p = 3] => [2 < 2 * 1] => discard by [P']  *)
          move => p_lt_r₀ p_prime.
          move => p_q_neq p_in_P.

          rewrite /P'/three'/three/two'/two  //=.
          have prime2_eq: q_prime = prime2ord by [].
          rewrite prime2_eq.
          rewrite in_setD.
          move/andP; case.
          have two_ltn_r₀_eq : q_lt_r₀ = two_ltn_r₀ by [].
          rewrite two_ltn_r₀_eq.
          move/negP.

          by rewrite in_set1.

        * (* [p = n.+4] => [2 < n.+3 * 1] => solve *)
          by [].
      + (* solve *)
        intros; clear.
        elim: n => [|n' iH].
        * by case: n0.
        * rewrite mulnS; apply ltn_addl.
          exact: iH.
  Defined.

  (*
  equations? keygen :
    code key_locs [interface] 'unit :=
    keygen :=
      {code
         p ← sample uniform p ;;
         let p := enum_val p in
         q ← sample uniform (p' p) ;;
         let q := enum_val q in
         #assert (p != q) ;;

         let phin := phi_n_ord p q in
         #assert (2 < phin) as phin_gt2 ;;

         e ← sample uniform (e phin_gt2) ;;
         let e := enum_val e in
         let d := calc_d phin_gt2 e in
         let ed := ((proj1_sig e) * (proj1_sig d) %% phin) in
         #assert (ed == 1 %% phin) ;;
         let e := e_widen phin_gt2 e in
         let d := e_widen phin_gt2 d in

         let n := mult_cast_nat p q in
         let pub_key := fto (n,e) in
         let sec_key := fto (n,d) in
         #put pk_loc := pub_key ;;
         #put sk_loc := sec_key ;;
         ret '( pub_key, sub_key )
      }.
*)

  (*
    report me:
    This is a bug in SSProve: [#assert] vs. [assert]
    When using [#assert], I get this error.
    This is a pity because [assert P as k] only works as [#assert P as k].
    All is good when I use [assert P].
   *)
 (* Fail Equations? KeyGen : *)
 (*    code Key_locs [interface] (chPubKey × chSecKey) := *)
 (*    KeyGen := *)
 (*      {code *)
 (*         p ← sample uniform P ;; *)
 (*       let p := enum_val p in *)
 (*       q ← sample uniform (P' p) ;; *)
 (*       let q := enum_val q in *)
 (*       #assert (p != q) ;; *)

 (*       let phiN' := phi_N_ord' p q in *)
 (*       let phiN  := proj1_sig phiN' in *)
 (*       let phiN_gt2 := proj2_sig phiN' in *)

 (*       e ← sample uniform (C phiN') ;; *)
 (*       let e := enum_val e in *)
 (*       let d := calc_d phiN e in *)
 (*       let ed := ((proj1_sig e) * (proj1_sig d) %% phiN) in *)
 (*       #assert (ed == 1 %% phiN) ;; *)
 (*       let e := e_widen phiN_gt2 e in *)
 (*       let d := e_widen phiN_gt2 d in *)

 (*       let n := mult_cast_nat p q in *)
 (*       let pub_key := fto (n,e) in *)
 (*       let sec_key := fto (n,d) in *)
 (*       #put pk_loc := pub_key ;; *)
 (*       #put sk_loc := sec_key ;; *)
 (*       ret ( pub_key , sec_key ) *)
 (*      }. *)


  Equations KeyGen :
    code Key_locs [interface] (chPubKey × chSecKey) :=
    KeyGen :=
    {code
      p₀ ← sample uniform P ;;
      let p := enum_val p₀ in
      q₀ ← sample uniform (P' p) ;;
      let q := enum_val q₀ in
      assert (p != q) ;;

      let phiN' := phi_N_ord' p₀ q₀ in
      let phiN₁  := proj1_sig phiN' in
      let phiN₂ := proj2_sig phiN' in

      e ← sample uniform (E phiN₂) ;;
      let e := enum_val e in
      let d := calc_d phiN' e in
      let ed := Zp_mul (proj1_sig e) d in
      assert (ed == Zp1) ;;
      let e := e_widen phiN₂ (proj1_sig e) in
      let d := e_widen phiN₂ d in

      let n := mult_cast_nat p q in
      let pub_key := fto (n,e) in
      let sec_key := fto (n,d) in
      #put pk_loc := pub_key ;;
      #put sk_loc := sec_key ;;
      ret ( pub_key , sec_key )
    }.

End RSA_KeyGen_code.


Module RSA_SignatureAlgorithms
  (π1  : RSA_params)
  (π2 : KeyGenParams π1)
  (π3 : KeyGen_code π1 π2)
<: SignatureAlgorithms π1 π2 π3.

  Import π1 π2 π3.
  Module KGC := RSA_KeyGen_code π1 π2.
  Import KGC KGC.KGP KGC.KG KGC.


  Lemma dec_smaller_n (d s pq : R) (H: 0 < pq) : (decrypt'' d pq s) < pq.
  Proof.
    by rewrite /decrypt''; apply ltn_pmod.
  Qed.

  Lemma enc_smaller_n (e pq : R) (m : 'I_pq) (H: 0 < pq) : (encrypt'' e pq m) < pq.
  Proof.
    by rewrite /encrypt''; apply ltn_pmod.
  Qed.

  Definition dec_to_In  (d s pq : R) (H: 0 < pq) : 'I_pq :=
    Ordinal (dec_smaller_n d s pq H).
  Definition enc_to_In  (e pq:R) (m:'I_pq) (H: 0 < pq) : 'I_pq :=
    Ordinal (enc_smaller_n e pq m H).

  Lemma pq_leq_r:
    forall (pq:fintype_ordinal__canonical__fintype_Finite r), pq <= r.
  Proof.
    case => pq pq_ltn_r /=.
    exact: (ltnW pq_ltn_r).
  Qed.

  Equations Sign (sk : chSecKey) (m : chMessage) : chSignature :=
    Sign sk m :=
      match otf sk with
      | (exist pq O_ltn_pq, sk') =>
          (* This may seem unnecessary because we are casting
             from [R] to ['I_pq] and back to [R'].
             It is important for the proof part though.
           *)
          fto (widen_ord
                 (pq_leq_r pq)
                 (enc_to_In sk' pq (padd pq (otf m)) O_ltn_pq))
      end.

  Equations Ver_sig (pk :  chPubKey) (sig : chSignature) (m : chMessage) : 'bool :=
    Ver_sig pk sig m :=
      match otf pk with
      | (exist pq O_ltn_pq, pk') =>
          (dec_to_In pk' (otf sig) pq O_ltn_pq) == padd pq (otf m)
      end.

  (* Playground begin *)

  Definition fun_from_set {S T:ordType} (s:{fset S*T}) : S -> option T :=
    let m := mkfmap s in λ s₁:S, getm m s₁.

  Definition currying_fmap {S T:ordType} {X:eqType} (m:{fmap (S*T) -> X}) : {fmap S -> {fmap T -> X}} :=
    currym m.

  Definition map_from_set {S T:ordType} (s:{fset S*T}) : {fmap S -> T} := mkfmap s.

  (* I believe that this is the lemma that we need:
     [Check mem_domm.]
   *)

  
  (**
     Note this: Our function is total but our fmap is actually not.
     It may return None. This situation is expressed in the function with the comparison
     of the given and decrypted signature/message.

     So there is:
     [if k ∈ m then true else false]
     or for short:
     [k ∈ m]

     As a function, we have [f] where [k ∈ f] is defined as
     [k₀ == f k]

     As a consequence, we cannot relate [f] to [m] but this function [f']
     f' := k₀ == f k

     This means that [k₀] represents all values that are not in the map.
     Consequently, we cannot prove a general lemma because we need this equality check
     and [k₀].
   *)

  (* Playground end *)

  Lemma xxx {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (f: S -> T) (x₁:S) (x₂:T) :
    (x₁, x₂) \in domm s = (x₂ == f x₁).
  Proof.
    apply/dommP.
  Admitted.

  Definition prod_key_map {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) : {fmap S -> T} :=
    mkfmap (domm s).

  Definition has_key {S T:ordType} (s:{fmap S -> T}) (x:S) : bool := x \in domm s.

  Lemma rem_unit {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S) (x₂:T) :
      (x₁, x₂) \in domm s -> has_key (prod_key_map s) x₁.
  Proof.
    rewrite /has_key/prod_key_map.
    move/dommP. case => x in_s.
    apply/dommP.

    Restart.

    rewrite /has_key/prod_key_map.
    rewrite mem_domm.
    rewrite mem_domm.
    (*move => in_s. *)
    Check getm.
    rewrite /getm.

  Abort.

  Lemma getm_def_seq_step {S T:ordType} {a₀:S*T} {a₁: seq.seq (S*T)} {a₂:S} :
    getm_def (fset (a₀ :: a₁)) a₂ = getm_def (a₀ :: (fset a₁)) a₂.
  Proof.
  Admitted.

  Lemma rem_unit {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S) (x₂:T):
    (x₁, x₂) \in domm s = has_key (prod_key_map s) x₁.
  Proof.
    rewrite /has_key/prod_key_map.
    (*
      Careful here!
      When rewriting with [mem_domm] then
      a check in the domain of a map that evaluates to [bool]
      becomes
      a check for the element itself that evaluates to an [option T].
      This works because Coq coerces [Some _] to [true] and [None] to [false].
      But be careful:
      The comparison [Some x₁ = Some x₂] requires that [x₁ = x₂].
      While this is not necessarily needed! Especially for our lemma!
     *)
    rewrite mem_domm.
    rewrite mem_domm.
    elim/fmap_ind : s => /=.
    - rewrite /domm /=.
      by rewrite -fset0E /mkfmap/foldr.
    - move => s iH [x₁' x₂'] v.
      move/dommPn => notin_s.
      rewrite setmE.
      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def.
      rewrite -/(getm_def _ x₁) -mkfmapE /=.

    Restart.

    rewrite /has_key/prod_key_map mem_domm mem_domm.
    move: x₁ x₂.
    elim/fmap_ind : s => /=.
    - move => x₁ x₂ /=. rewrite /domm /=.
      by rewrite -fset0E /mkfmap/foldr.
    - move => s iH [x₁' x₂'] v notin_s x₁ x₂.
      rewrite setmE.
      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def.
      rewrite -/(getm_def _ x₁) -mkfmapE /=.

      case H: ((x₁,x₂) == (x₁',x₂')).
      -- move/eqP:H => H; inversion H => //=. (* turns left side back into bool because the types differ [T != X] *)
         by rewrite ifT.
      -- case H_x₁: (x₁ == x₁').
         2: exact: iH.
         simpl. (* turns the RHS into [true] *)

         (* This case now seems not solvable:
            [x₁ = x₁' /\ x₂ != x₂']
            The problem is that we do not have any evidence that the LHS
            [(x₁,x₂) ∈ s]
            always holds [true].

            And why should this even be the case?!
            - Our argument was that both sides are derived from the same [s].
              Hence, when [x₁] is in the RHS it also needs to be in the LHS.
              The same holds for when it is not in [s].

            Then why do we fail?
            - Oh well, that is because of the induction!
              The case that we stumble over is the one where we discover an [x₂'] in the RHS
              even without consulting [s] at all.
          *)

    Restart.

    rewrite /has_key/prod_key_map mem_domm mem_domm.
    elim/fmap_ind : s => /=.
    - rewrite /domm /=.
      by rewrite -fset0E /mkfmap/foldr.
    - move => s iH [x₁' x₂'] v notin_s.
      rewrite setmE. (* LHS *)
      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def -/(getm_def _ x₁) -mkfmapE /=. (* RHS *)
      (*
        Indeed, it is the whole approach to solve this via [get_defm]
        just does not work this way.
        In the case, where we add something, we unfold [get_defm] once to
        get the inductive step.
        In this one unfolding, there is always the case where we
        do not consult [s].

        I never use the fact that [(x₁',x₂') ∉ s].
        Let me try.
       *)

    Restart.

    rewrite /has_key/prod_key_map mem_domm mem_domm.
    move: x₁ x₂.
    elim/fmap_ind : s => /=.
    - move => x₁ x₂ /=. rewrite /domm /=.
      by rewrite -fset0E /mkfmap/foldr.
    - move => s iH [x₁' x₂'] v notin_s x₁ x₂.
      rewrite setmE.
      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def.
      rewrite -/(getm_def _ x₁) -mkfmapE /=.

      case H: ((x₁,x₂) == (x₁',x₂')).
      -- move/eqP:H => H; inversion H => //=. (* turns left side back into bool *)
         by rewrite ifT.
      -- case H_x₁: (x₁ == x₁').
         2: exact: iH.
         move/dommPn:notin_s => notin_s.
         specialize (iH x₁' x₂').
         rewrite notin_s in iH.
         move/eqP: H_x₁ => H_x₁; rewrite -H_x₁ in iH.

         (*
           Nevermind the last transformations.
           Let's check out the following hypothesis
           [s (x₁',x₂') = None] which transforms into [s (x₁,x₂') = None]
           and the goal
           [s (x₁,x₂) = Some x₂'].
           The key point that we were missing is the fact that the hypothesis
           contradicts the goal.
           This is because of the following lemma:
          *)
         have xxx : s (x₁,x₂') = None -> forall x₂'', s (x₁,x₂'') = None.

         (*
           Nope, this does not hold!

           But maybe there is a different contradiction.
          *)

         Restart.

    rewrite /has_key/prod_key_map mem_domm mem_domm.
    elim/fmap_ind : s => /=.
    - rewrite /domm /=.
      by rewrite -fset0E /mkfmap/foldr.
    - move => s iH [x₁' x₂'] v notin_s.
      rewrite setmE.
      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def.
      rewrite -/(getm_def _ x₁) -mkfmapE /=.

      case H: ((x₁,x₂) == (x₁',x₂')).
      -- move/eqP:H => H; inversion H => //=. (* turns left side back into bool *)
         by rewrite ifT.
      -- case H_x₁: (x₁ == x₁').
         2: exact: iH.
         rewrite xpair_eqE in H.
         rewrite H_x₁ in H.
         simpl in H.

         (*
           The problem is that the induction tries to add something to the map
           that is not yet there.
           Hence, we get into trouble in the first case where it does not consult
           the map itself.
          *)

         Restart.

    rewrite /has_key/prod_key_map mem_domm mem_domm.
    elim/fmap_ind : s => /=.
    - rewrite /domm /=.
      by rewrite -fset0E /mkfmap/foldr.
    - move => s iH [x₁' x₂'] v notin_s.

      (*
        Why do I think that this holds?

        Case analysis on [x₁ == x₁'].
        - Case: [x₁ == x₁']
            -- RHS always finds [x₂']
            -- LHS needs case analysis on [x₂ == x₂']
              --- Case [x₂ == x₂']: LHS finds it in the first step
              --- Case [x₂ != x₂']: consults [s] where it may find it or not

        So this is the problem. The queries against the maps differ!
        The RHS only looks for [x₁] while the LHS looks for [(x₁,x₂)].

        Does that mean I can prove a lemma where [x₂] is more restricted?
       *)


  Abort.

  Lemma rem_unit {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S) :
    (exists (x₂:T), (x₁, x₂) \in domm s) = has_key (prod_key_map s) x₁.
  Proof.
    rewrite /has_key/prod_key_map mem_domm.
    elim/fmap_ind : s => /=.
    - rewrite /domm /=.
      rewrite -fset0E /mkfmap/foldr.
      simpl.
 
      (* rewrite in_fset0. *)

  Abort.


  Lemma rem_unit {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S) (x₂:T):
    (x₁, x₂) \in domm s -> has_key (prod_key_map s) x₁.
  Proof.
    move: x₁ x₂.
    elim/fmap_ind : s => /=.
    - move => x₁ x₂.
      by rewrite domm0 in_fset0.
    - move => s iH [x₁ x₂] v x_notin_s x₁' x₂'.
      rewrite /has_key/prod_key_map.
      rewrite mem_domm mem_domm.

      rewrite setmE.
      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def.
      rewrite -/(getm_def _ x₁') -mkfmapE /=.

      case H: ((x₁',x₂') == (x₁,x₂)).
      -- move/eqP:H => H; inversion H.
         rewrite ifT //=.
      -- rewrite -mem_domm => x'_in_s.
         case H_x₁: (x₁' == x₁).
         --- by [].
         --- specialize (iH x₁' x₂' x'_in_s).
             rewrite /has_key/prod_key_map mem_domm in iH.
             exact: iH.
  Qed.

  Lemma rem_unit' {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S):
    has_key (prod_key_map s) x₁ -> exists (x₂:T), (x₁, x₂) \in domm s.
  Proof.
    move: x₁.
    elim/fmap_ind : s => /=.
    - move => x₁.
      rewrite /has_key/prod_key_map.
      rewrite mem_domm mkfmapE domm0 //=.
    - move => s iH [x₁ x₂] v x_notin_s x₁'.
      rewrite /has_key/prod_key_map.
      rewrite mem_domm.

      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def -/(getm_def _ x₁') -mkfmapE /=.

      case H_x₁: (x₁' == x₁).
      -- move => x_in_s.
         exists x₂.
         move/eqP:H_x₁ => H_x₁; rewrite H_x₁ //=.
         auto_in_fset. (* TODO remove when pushing this into extructures. or move the tactic alltogether. *)
      -- rewrite /has_key /prod_key_map in iH.
         rewrite -mem_domm => x₁'_in_s.
         specialize (iH x₁' x₁'_in_s).
         case: iH => x₂' iH.
         exists x₂'.
         rewrite /domm in iH.
         by rewrite fset_cons in_fsetU1; apply/orP; right.
  Qed.

  Theorem Signature_prop:
    ∀ (l: {fmap (chSignature  * chMessage ) -> 'unit})
      (s : chSignature) (pk : chPubKey) (m  : chMessage),
      Ver_sig pk s m = ((s,m) \in domm l).
  Proof.
    move => l s pk m.
    apply esym.
    (*
      This looks promising already.
      I would like to move this inequaility onto the branches
      to then say that this is the [v] that is not in the map.
      But for that I need a transformation first to remove the [unit].
     *)
    rewrite mem_domm.
    rewrite /Ver_sig.
    rewrite /getm/getm_def.
    rewrite /dec_to_In/decrypt''.
    (*
      I take that back:
      I do not see how this can be provable at all!

      A map if a partial function. Whether [Ver_sig] indeed implements
      that particular function or phrase the other way around, whether the map
      contains the pairs for the particular [Ver_sig] implementation
      cannot be derived without further evidence!
      (At least I cannot see where this information is supposed to come from!)

      It all feels to me like this wants to be a functional correctness property.
      Or it needs to be part of a different game.
     *)


    Abort.

  Theorem Signature_prop':
    ∀ (l: {fmap (chSignature  * chMessage ) -> 'unit})
      (pk : chPubKey)
      (sk : chSecKey)
      (m  : chMessage),
      Ver_sig pk (Sign sk m) m = ((Sign sk m, m) \in domm l).
  Proof.
    move => l pk sk m.
    rewrite mem_domm.
    rewrite /Ver_sig/Sign.

    generalize (otf m) => m'.
    case: pk => pk pk_lt /=.

    (* LHS *)
    rewrite /enc_to_In/dec_to_In.
    Fail rewrite rsa_correct''.

    (* I can certainly reduce the LHS to [true].
       But the RHS talks about the [Sign] of real instead of ideal!
       We still miss the fact that this tuple is actually really in [l].
     *)
  Abort.


  Theorem Signature_correct pk sk msg seed (* e d p' q'*):
    Some (pk,sk) = Run sampler KeyGen seed ->
    Ver_sig pk (Sign sk msg) msg == true.
  Proof.
    rewrite /Run/Run_aux /=.

    (* SSReflect style generalization: *)
    move: (pkg_interpreter.sampler_obligation_4 seed {| pos := P; cond_pos := pos_i_P |}) => p₀.
    move: (pkg_interpreter.sampler_obligation_4 (seed + 1) {| pos := P' (enum_val p₀); cond_pos := _ |}) => q₀.

    rewrite /assert.
    have p_q_neq'' : enum_val p₀ != enum_val q₀. 1: { by apply p_q_neq'. }
    rewrite ifT //=.

    move: (pkg_interpreter.sampler_obligation_4 (seed + 1 + 1) {| pos := _; cond_pos := _ |}) => e. (* [sk₁] *)

    rewrite /sval.
    case: (enum_val e) => [e']; move/andP; case => [e_gt1 coprime_e_phiN] //.
    have ed_mod : Zp_mul e' (Zp_inv e') == Zp1.
    1:{
      apply/eqP.
      apply Zp_mulzV.
      (* rewrite coprime_sym. *)
      clear e.
      move: e' e_gt1 coprime_e_phiN; rewrite /phi_N_ord'/phi_N_ord/E' //=.
      rewrite Zp_cast.
      - move => e' e_gt1 coprime_e_phiN.
        exact: coprime_e_phiN.
      - apply/ltnW/KGC.phi_N_ord'_obligations_obligation_1.
    }
    rewrite ifT //=.

    case => pk_eq sk_eq. (* injectivity *)

    rewrite /Ver_sig/Sign/dec_to_In/enc_to_In /=.
    rewrite sk_eq pk_eq /=.
    rewrite !otf_fto /=.

    case H: (mult_cast_nat (enum_val p₀) (enum_val q₀)) => [pq pq_gt_O] /=.
    rewrite /widen_ord /=.
    rewrite !otf_fto /=.

    apply/eqP/eqP.
    (* TODO this step is a bit strange. investigate. *)
    case H₁: (Ordinal (n:=pq) (m:=_) _) => [m i].
    case: H₁.

    move: H; rewrite /mult_cast_nat -/Nat.add -/Nat.mul /widen_ord.
    clear sk_eq pk_eq.

    have phi_N_ord_gt2 : 2 < phi_N_ord (enum_val p₀) (enum_val q₀) := KGC.phi_N_ord'_obligations_obligation_1 p₀ q₀.

    move: e' ed_mod e_gt1 coprime_e_phiN phi_N_ord_gt2.
    case Hq: (enum_val q₀) => [q' q'_prime].
    case Hp: (enum_val p₀) => [p' p'_prime].
    move => e' ed_mod e_gt1 coprime_e_phiN phi_N_ord_gt2.

    case.

    case H₂: (Ordinal (n:=r) (m:=p') _) => [p'' p''_ltn_r].
    case: H₂ => p'_eq_p''.
    case H₂: (Ordinal (n:=r) (m:=q') _) => [q'' q''_ltn_r].
    case: H₂ => q'_eq_q''.

    case XX: (Ordinal (n:=r) (m:=p'*q') _) => [p_mul_q pr].
    case: XX. move/esym => p_mul_q_eq.
    move/esym => pq_spec.

    (* TODO remember this hypothesis for [decrypt] and [ecnrypt]. *)
    rewrite -[X in X = _ -> _](@modn_small _ pq).
    - rewrite -[X in _ = X -> _](@modn_small _ pq).

    + have eee : nat_of_ord pq = (p' * q')%N by subst.
        rewrite (rsa_correct'' eee) /=.
        * move => msg_eq. subst.
          repeat rewrite modn_small in msg_eq.
          ** by apply ord_inj.
          ** exact: i.
          ** by []. 
        * rewrite /wf_type.
          apply/andP; split; try exact: p'_prime.
          apply/andP; split; try exact: q'_prime.
          apply/andP; split; [ by move: p_q_neq''; rewrite Hq Hp |].
          apply/andP; split; [ by apply pq_phi_gt_0 |].
          apply/andP; split; [ by apply dvdn_mulr |].
          apply/andP; split; [ by apply dvdn_mull |].
          move: ed_mod; rewrite mulnC.

          (* TODO should be a separate lemma!
             [
               Zp_mul e' (Zp_inv e') == Zp1 ->
               e' * Zp_inv e' == 1 %[mod p'.-1 * q'.-1]
             ]
           *)
          rewrite /Zp_mul/inZp //=.
          move/eqP.
          case.
          move: e' e_gt1 coprime_e_phiN.
          rewrite /Zp_trunc/phi_N_ord/phi_N.
          move => e' e_gt1 coprime_e_phiN.
          Fail rewrite prednK. (* TODO How do I deal with dependent type errors? *)
          move => ed_mod.
          apply/eqP.
          rewrite -[X in _ = 1 %[mod X]]prednK.
          ** rewrite -[X in _ = 1 %[mod X.+1]]prednK.
             *** exact: ed_mod.
             *** apply ltnSE.
                 rewrite prednK.
                 **** apply/ltnW/phi_N_ord_gt2.
                 **** apply/ltnW/ltnW/phi_N_ord_gt2.
          ** apply/ltnW/ltnW/phi_N_ord_gt2.
      + by [].
    - by rewrite /decrypt''; apply ltn_pmod.

    Unshelve.
      1: { clear ed_mod e phi_N_ord_gt2 p'_prime e' e_gt1 coprime_e_phiN Hp; case: p' => [p' p'_ltn_r₀]; apply (leq_trans p'_ltn_r₀ n_leq_nn). }
      clear ed_mod e e' e_gt1 coprime_e_phiN phi_N_ord_gt2 q'_prime Hq; case: q' => [q' q'_ltn_r₀]; apply (leq_trans q'_ltn_r₀ n_leq_nn).
  Qed.

End RSA_SignatureAlgorithms.
