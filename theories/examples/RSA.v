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

Local Open Scope package_scope.


Module RSA_params <: SignatureParams.

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

End RSA_params.

(*
TODO Turn this into a module type
 *)
Module Padding.

  Import RSA_params.

  (**
     We need to tanslate a message into the "RSA" space.
   *)
  Parameter padd : forall (pq:nat) (m:Message), 'I_pq.

End Padding.


Module RSA_func.

  Import RSA_params.

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

End RSA_func.



Module RSA_KeyGen <: KeyGenParams RSA_params.

  Import RSA_params RSA_func.

  Definition sk0 : SecKey := (exist _ 1%R (ltn0Sn 0), 1)%g.
  Definition pk0 : PubKey := (exist _ 1%R (ltn0Sn 0), 1)%g.
  Definition sig0 : Signature := 1%g.
  Definition m0 : Message := 1%g.
  Definition chal0 : Challenge := 1%g.

  #[export] Instance SecKey_pos : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. exists sk0. auto.
  Qed.

  #[export] Instance PubKey_pos : Positive #|PubKey|.
  Proof.
    apply /card_gt0P. exists pk0. auto.
  Qed.

  #[export] Instance Signature_pos : Positive #|Signature|.
  Proof.
    apply /card_gt0P. exists sig0. auto.
  Qed.

  #[export] Instance Message_pos : Positive #|Message|.
  Proof.
    apply /card_gt0P. exists m0. auto.
  Qed.

  #[export] Instance Challenge_pos : Positive #|Challenge|.
  Proof.
    apply /card_gt0P. exists chal0. auto.
  Qed.

  Definition chSecKey  : choice_type := 'fin #|SecKey|.
  Definition chPubKey : choice_type := 'fin #|PubKey|.
  Definition chSignature : choice_type := 'fin #|Signature|.
  Definition chMessage : choice_type := 'fin #|Message|.
  Definition chChallenge : choice_type := 'fin #|Challenge|.

  Definition i_sk := #|SecKey|.
  Definition i_pk := #|PubKey|.
  Definition i_sig := #|Signature|.

End RSA_KeyGen.



Module RSA_KeyGen_code <: KeyGen_code RSA_params RSA_KeyGen.

  Import Padding.
  Import RSA_params RSA_KeyGen.
  Module KGP := KeyGenParams_extended RSA_params RSA_KeyGen.
  Import KGP.
  Module π1 := RSA_params.

  Import PackageNotation.
  Local Open Scope package_scope.

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

  Lemma mult_prime_gt_0 : forall a b,
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


  Lemma widen_mult_prime_gt_0_R {a b:R₀} (ap: prime a) (bp: prime b) :
    0 < ((widen_ord n_leq_nn a) * (widen_ord n_leq_nn b))%R.
  Proof.
    rewrite /widen_ord /=.
    rewrite -/Nat.mul -/Nat.add.
    rewrite plusE multE.
    rewrite modn_small.
    - by apply mult_prime_gt_0.
    - by apply ltn_R.
  Qed.

  Lemma widen_mult_prime_gt_0_nat {a b:R₀} (ap: prime a) (bp: prime b) :
    0 < ((widen_ord n_leq_nn a) * (widen_ord n_leq_nn b))%nat.
  Proof.
    rewrite /widen_ord /=.
    by apply mult_prime_gt_0.
  Qed.

  Definition mult_cast (a b : prime_num) : R' :=
    match a,b with
    | exist a' ap , exist b' bp =>
        exist _
          ((widen_ord n_leq_nn a') * (widen_ord n_leq_nn b'))%R (* <-- This [R] is not our [R] but means the Ring. *)
          (widen_mult_prime_gt_0_R ap bp)
    end.

  Lemma mult_cast_nat_lt_r {a b:R₀} : (a * b)%nat < r.
  Proof.
    move: a b; rewrite /R₀/r.
    case => [a a_ltn]; case => [b b_ltn].
    apply ltn_mul; try apply ltn_ord.
  Qed.

  Definition mult_cast_nat (a b : prime_num) : R' :=
    match a,b with
    | exist a' ap , exist b' bp =>
        exist _
          (Ordinal mult_cast_nat_lt_r)
     (widen_mult_prime_gt_0_nat ap bp)
    end.

  Definition phi_N (a b : prime_num) : nat :=
    match a,b with
    | exist a' ap , exist b' bp => a'.-1 * b'.-1
    end.

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
  Qed.

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


Module RSA_SignatureAlgorithms <: SignatureAlgorithms
                                    RSA_params
                                    RSA_KeyGen
                                    RSA_KeyGen_code.

(*


Module RSA_SignatureAlgorithms
  (π1 : RSA_params)
  (π2 : KeyGenParams π1)
  (π3 : KeyGen_code π1 π2)
<:
  (* FIXME This only gets the abstract definitions and hence creates the correctness
           property based on that.
           But I need the concrete implementations in order to create the proof!

           I would like to give a dedicated instance to derive from
           [SignatureAlgorithms π1 (RSA_KeyGen π1) (RSA_KeyGen_code π1 π2)]
           but Coq does not allow me to do so.

           At the same time, Coq does not allow me to make the module parameters
           more concrete because appartently only a module type can be a parameter.
           (This makes a lot of sense because modules can just be imported.)
   *)
  SignatureAlgorithms π1 (RSA_KeyGen π1) (RSA_KeyGen_code π1 π2).

  Import π1 π2 π3 π3.KGP.
*)

  Import RSA_params RSA_func RSA_KeyGen RSA_KeyGen_code RSA_KeyGen_code.KGP Padding.

  Module KG := RSA_KeyGen_code.


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
      - apply/ltnW/KG.phi_N_ord'_obligations_obligation_1.
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

    have phi_N_ord_gt2 : 2 < phi_N_ord (enum_val p₀) (enum_val q₀) := KG.phi_N_ord'_obligations_obligation_1 p₀ q₀.

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

    + have noo_pq : nat_of_ord pq = (p' * q')%N by subst.
        rewrite (rsa_correct'' noo_pq) /=.
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
