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
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

(* Obligation Tactic := idtac. *)

#[local] Open Scope package_scope.

From vRATLS Require Import examples.Signature.
From vRATLS Require Import extructurespp.ord.
From vRATLS Require Import extructurespp.fmap.
From vRATLS Require Import extructurespp.fset.
From vRATLS Require Import examples.RA.

Module Hash
  (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KGc)
  (RAA : RemoteAttestationAlgorithms π1 π2 KGc)
  (RAH : RemoteAttestationHash π1 π2 KGc Alg RAA).

  Import KGc.KGP RAA RAH RAH.SP.

    (* Normally, this would be located in a Functor.
      This is just [fmap] on a tuple.
    *)
  Definition pair_fmap {S T T':Type} (f: T -> T') : (T * S) -> (T' * S) :=
    λ '(t,s), (f t,s).

  Lemma second_id : forall S T T' (f: T -> T') (t:T * S), snd (pair_fmap f t) = snd t.
  Proof.
    by [move => S T T' f; case => a b].
  Qed.

  Definition fmap_kmap' {S} {T T':ordType} (f: T->T') (m:{fmap T -> S}) : {fmap T' -> S} :=
    mapm2 f id m.

  Definition hash_eq (a_loc : Value attest_loc_long.π1) (s_loc : Value sign_loc.π1) : Prop :=
    (fmap_kmap'
        (fun t =>
          match t with
          | (sig, state, challenge) => (sig, Hash state challenge)
          end)
        a_loc) = s_loc.

  Definition full_heap_eq : precond  :=
    λ '(s0, s1),
      get_heap s0 pk_loc = get_heap s1 pk_loc /\
        get_heap s0 sk_loc = get_heap s1 sk_loc /\
        get_heap s0 state_loc = get_heap s1 state_loc /\
        hash_eq (get_heap s0 attest_loc_long) (get_heap s1 sign_loc) /\
        (forall {l:Location}, l \notin Attestation_locs_ideal → l \notin Comp_locs → get_heap s0 l = get_heap s1 l).

  Lemma INV'_full_heap_eq:
    INV' Attestation_locs_ideal Comp_locs full_heap_eq.
  Proof.
    split.
    - rewrite /full_heap_eq;
        case => pk_loc_eq;
        case => sk_loc_eq;
        case => state_loc_eq;
        case => attest_loc_eq other_eq l notin_att_locs notin_comp_locs.
      case in_att_locs: (l \in Attestation_locs_ideal).
      + move: in_att_locs; move/idP => in_att_locs.
        move: notin_att_locs; move/negP => //=.
      + case in_comp_locs: (l \in Comp_locs).
        * move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
        * clear in_att_locs; clear in_comp_locs.
          apply (other_eq _ notin_att_locs notin_comp_locs).
    - rewrite /full_heap_eq;
        case => pk_loc_eq;
        case => sk_loc_eq;
        case => state_loc_eq;
        case => attest_loc_eq other_eq l v notin_att_locs notin_comp_locs.
      repeat split.
      + case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have pk_loc_in_att_locs: pk_loc \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               left; auto_in_fset.
             }
             have pk_not_eq_l: pk_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs pk_loc_in_att_locs). }
             by [do 2! rewrite (get_set_heap_neq _ _ _ _ pk_not_eq_l)].
      + (* same as above but for  [sk_loc] *)
        case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have sk_loc_in_att_locs: sk_loc \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               left; auto_in_fset.
             }
             have sk_not_eq_l: sk_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs sk_loc_in_att_locs). }
             by [do 2! rewrite (get_set_heap_neq _ _ _ _ sk_not_eq_l)].
      + (* same as above but for  [state_loc] *)
        case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have state_loc_in_att_locs: state_loc \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               left; auto_in_fset.
             }
             have state_not_eq_l: state_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs state_loc_in_att_locs). }
             by [do 2! rewrite (get_set_heap_neq _ _ _ _ state_not_eq_l)].
      + (* same as above but for [attest_loc_long] and [sign_loc] *)
        case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have attest_loc_in_att_locs: attest_loc_long \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               right; auto_in_fset.
             }
             have attest_not_eq_l: attest_loc_long != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs attest_loc_in_att_locs). }
             have sign_loc_in_comp_locs: sign_loc \in Comp_locs.
             { clear; rewrite /Comp_locs; auto_in_fset. }
             have sign_not_eq_l: sign_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_comp_locs sign_loc_in_comp_locs). }
             by [rewrite (get_set_heap_neq _ _ _ _ attest_not_eq_l) (get_set_heap_neq _ _ _ _ sign_not_eq_l)].
      + move => l' l'_notin_att_locs l'_notin_comp_locs.
        case E: (l==l').
        * move: E; move/eqP => l_eq_l'.
          rewrite -l_eq_l'.
          by [do 2! (rewrite get_set_heap_eq)].
        * move: E; move/negP/idP; rewrite eqtype.eq_sym => l_neq_l'.
          do 2! rewrite (get_set_heap_neq _ _ _ _ l_neq_l').
          apply: (other_eq l' l'_notin_att_locs l'_notin_comp_locs).
  Qed.

  Lemma Invariant_heap_eq_ideal:
    Invariant Attestation_locs_ideal Comp_locs full_heap_eq.
  Proof.
    split.
    - by [apply INV'_full_heap_eq].
    - by [].
  Qed.

  #[export] Hint Extern 10 (Invariant Attestation_locs_ideal Comp_locs full_heap_eq) =>
    eapply Invariant_heap_eq_ideal
    : typeclass_instances ssprove_invariant.

  Definition full_heap_eq' : precond  :=
    λ '(s0, s1),
        hash_eq (get_heap s0 attest_loc_long) (get_heap s1 sign_loc) /\
          (forall {l:Location}, l \notin (fset [:: attest_loc_long ; sign_loc]) → get_heap s0 l = get_heap s1 l).

  Lemma att_loc_in : attest_loc_long \in fset [:: attest_loc_long; sign_loc].
  Proof. auto_in_fset. Qed.

  Lemma sign_loc_in : sign_loc \in fset [:: attest_loc_long; sign_loc].
  Proof. auto_in_fset. Qed.

  (* TODO generalize *)
  Lemma not_in_diff: forall l,
      l \notin Attestation_locs_ideal ->
      l \notin Comp_locs ->
      l \notin (fset [:: attest_loc_long ; sign_loc]).
  Proof.
    move => l h1 h2.
    rewrite -fdisjoints1.
    apply (@fdisjoint_trans _
             (fset [:: attest_loc_long; sign_loc])
             (Attestation_locs_ideal :|: Comp_locs)
             (fset1 l)
          ).
    2: {
      rewrite fdisjointC fdisjointUr.
      apply/andP; split; by [rewrite fdisjoint1s].
    }
    rewrite fset_cons.
    apply fsetUSS.
    - rewrite /Attestation_locs_ideal fset1E.
      apply fsubsetUr.
    - rewrite /Comp_locs -fset1E fsub1set.
      auto_in_fset.
  Qed.

  Lemma INV'_full_heap_eq'_get : forall s1 s2,
      full_heap_eq' (s1, s2) ->
      ∀ l,
        l \notin Attestation_locs_ideal ->
        l \notin Comp_locs ->
        get_heap s1 l = get_heap s2 l.
  Proof.
    move => s1 s2.
    rewrite /full_heap_eq;
      case => attest_loc_eq other_eq l notin_att_locs notin_comp_locs.
    case in_att_locs: (l \in Attestation_locs_ideal).
    + move: in_att_locs; move/idP => in_att_locs.
      move: notin_att_locs; move/negP => //=.
    + case in_comp_locs: (l \in Comp_locs).
      * move: in_comp_locs; move/idP => in_comp_locs.
        move: notin_comp_locs; move/negP => //=.
      * clear in_att_locs; clear in_comp_locs.
        apply (other_eq _ (not_in_diff _ notin_att_locs notin_comp_locs)).
  Qed.

  Lemma INV'_full_heap_eq'_get_set : forall s1 s2,
      full_heap_eq' (s1, s2) ->
      ∀ l (v : Value l.π1),
        l \notin Attestation_locs_ideal ->
        l \notin Comp_locs ->
        full_heap_eq' (set_heap s1 l v, set_heap s2 l v).
  Proof.
    move => s1 s2.
    rewrite /full_heap_eq';
        case => attest_loc_eq other_eq l v notin_att_locs notin_comp_locs.
      repeat split.
      + case in_att_locs: (l \in Attestation_locs_ideal).
        * move: in_att_locs; move/idP => in_att_locs.
          move: notin_att_locs; move/negP => //=.
        * case in_comp_locs: (l \in Comp_locs).
          ** move: in_comp_locs; move/idP => in_comp_locs.
          move: notin_comp_locs; move/negP => //=.
          ** clear in_att_locs; clear in_comp_locs.
             have attest_loc_in_att_locs: attest_loc_long \in Attestation_locs_ideal.
             {
               clear.
               rewrite /Attestation_locs_ideal /Attestation_locs_real in_fsetU; apply /orP.
               right; auto_in_fset.
             }
             have attest_not_eq_l: attest_loc_long != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_att_locs attest_loc_in_att_locs). }
             have sign_loc_in_comp_locs: sign_loc \in Comp_locs.
             { clear; rewrite /Comp_locs; auto_in_fset. }
             have sign_not_eq_l: sign_loc != l.
             { rewrite eqtype.eq_sym; apply (disjoint_noteq notin_comp_locs sign_loc_in_comp_locs). }
             by [rewrite (get_set_heap_neq _ _ _ _ attest_not_eq_l) (get_set_heap_neq _ _ _ _ sign_not_eq_l)].
      + move => l' l'_notin_diff_locs.
        case E: (l==l').
        * move: E; move/eqP => l_eq_l'.
          rewrite -l_eq_l'.
          by [do 2! (rewrite get_set_heap_eq)].
        * move: E; move/negP/idP; rewrite eqtype.eq_sym => l_neq_l'.
          do 2! rewrite (get_set_heap_neq _ _ _ _ l_neq_l').
          apply: (other_eq l' l'_notin_diff_locs).
  Qed.

  Lemma INV'_full_heap_eq':
    INV' Attestation_locs_ideal Comp_locs full_heap_eq'.
  Proof.
    split.
    - apply INV'_full_heap_eq'_get.
    - apply INV'_full_heap_eq'_get_set.
  Qed.

  Lemma Invariant_heap_eq_ideal':
    Invariant Attestation_locs_ideal Comp_locs full_heap_eq'.
  Proof.
    split.
    - by [apply INV'_full_heap_eq'].
    - by [].
  Qed.

  #[export] Hint Extern 10 (Invariant Attestation_locs_ideal Comp_locs full_heap_eq') =>
    eapply Invariant_heap_eq_ideal'
    : typeclass_instances ssprove_invariant.

  Lemma get_pre_cond_full_heap:
    ∀ ℓ
      (L: {fset Location}),
      (fdisjoint (fset [:: attest_loc_long; sign_loc]) L) ->
      ℓ \in L ->
      get_pre_cond ℓ full_heap_eq'.
  Proof.
    move => ℓ L h_disjoint l_in_L.
    rewrite /get_pre_cond => s₀ s₁ h_full_heap_eq.
    apply h_full_heap_eq.
    move: h_disjoint; rewrite fdisjointC; move/fdisjointP; move => h_disjoint.
    apply (h_disjoint ℓ l_in_L).
  Qed.

  #[export] Hint Extern 10 (get_pre_cond _ full_heap_eq') =>
    eapply get_pre_cond_full_heap
    : ssprove_invariant.


  Lemma put_pre_cond_full_heap:
    ∀ ℓ (v : Value ℓ.π1) (L: {fset Location}),
      (fdisjoint (fset [:: attest_loc_long; sign_loc]) L) ->
      ℓ \in L -> put_pre_cond ℓ v full_heap_eq'.
  Proof.
    move => ℓ v L h_disjoint l_in_L.
    rewrite /put_pre_cond/full_heap_eq' => s₀ s₁ h_full_heap_eq.
    have h_disjoint' := h_disjoint.
    move: h_disjoint'; rewrite fdisjointC; move/fdisjointP; move => h_notin.
    have l_in_L' := l_in_L.
    move: l_in_L'; move/h_notin. move/disjoint_noteq => l_neq_att_sign.
    case: h_full_heap_eq => full_heap_left full_heap_right.
    split.
    - have l_neq_att_loc := l_neq_att_sign attest_loc_long att_loc_in.
      rewrite eqtype.eq_sym in l_neq_att_loc.
      rewrite (get_set_heap_neq _ _ _ _ l_neq_att_loc).

      have l_neq_sign_loc := l_neq_att_sign sign_loc sign_loc_in.
      rewrite eqtype.eq_sym in l_neq_sign_loc.
      rewrite (get_set_heap_neq _ _ _ _ l_neq_sign_loc).

      apply full_heap_left.
    - move => l l_notin_att_sign.
      case E: (ℓ == l).
      + move/eqP in E.
        by [rewrite -E; repeat rewrite get_set_heap_eq].
      + move/eqP in E.
        (* Why is the below so hard?! *)
        have X: ℓ <> l /\ (true = true) := conj E erefl.
        move/predD1P in X.
        rewrite Bool.andb_true_r eqtype.eq_sym in X.

        repeat rewrite (get_set_heap_neq _ _ _ _ X).
        apply: (full_heap_right _ l_notin_att_sign).
  Qed.

  #[export] Hint Extern 10 (put_pre_cond _ _ full_heap_eq') =>
    eapply put_pre_cond_full_heap
    : ssprove_invariant.

  Lemma size_length_eq: forall A (l: seq.seq A),
      size l = length l.
  Proof.
    by [].
  Qed.

  Lemma map_size T T' (f: T->T') (l: seq.seq T):
      size (map f l) = size l.
  Proof.
    repeat rewrite size_length_eq; apply: map_length.
  Qed.

  Lemma fmap_kmap_setm {S} {T T': ordType}:
    forall (f: T -> T') (k:T) (v:S) (m: {fmap T -> S}),
      (* k \notin domm m -> *)
      injective f -> (* if this is bijective then I would not end up in omap! *)
      fmap_kmap' f (setm m k v) = setm (fmap_kmap' f m) (f k) v.
  Proof.
    rewrite /fmap_kmap'.
    apply mapm2_setm.
 Qed.

  Definition prod_dist (A B C : Type) (n: A*B*C) : (A*(B*C)) :=
    let (m,c) := n in let (a,b) := m in (a,(b,c)).

  Lemma pair_dist_eq {A B C : Type} {a0 a1: A} {b0 b1: B} {c0 c1: C}:
    (a0,(b0,c0)) = (a1,(b1,c1)) ->
    (a0,b0,c0) = (a1,b1,c1).
  Proof.
    move/pair_equal_spec; case => a0_eq_a1.
    move/pair_equal_spec => [b0_eq_b1 c0_eq_c1].
    have x := conj a0_eq_a1 b0_eq_b1.
    rewrite -pair_equal_spec in x.
    have y := conj x c0_eq_c1.
    rewrite -pair_equal_spec in y.
    exact: y.
  Qed.

  Lemma preserve_mem_full_heap_eq:
    forall {sign_loc_val: Value sign_loc.π1} {att_loc_val: Value attest_loc_long.π1} state x y,
      preserve_update_mem
        [::
           hpv_r sign_loc
             (setm sign_loc_val (y, Hash state x) tt);
           hpv_l attest_loc_long
             (setm att_loc_val (y, state, x) tt)
        ]
        [:: hpv_r sign_loc sign_loc_val; hpv_l attest_loc_long att_loc_val]
        full_heap_eq'.
    move => sign_loc_val att_loc_val state x y.
    rewrite /preserve_update_mem/remember_pre => s0 s1 h.
    rewrite /full_heap_eq' //=.
    split.
    - move: h; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; move => hasheq heq att_loc_mem sign_loc_mem.
      do 2! rewrite get_set_heap_eq.
      rewrite /hash_eq.
      (* At this point, we are at the core of the whole proof.
         we need to reason now about the map function.
         [hasheq] is my precondition which says:
         The values stored at [attest_loc_long] and [sign_loc] are [hash_eq] equal.
         Now I need to show that this property is preserved when adding new values.
         The proof is by induction on the values of [att_loc_val] and [sign_loc].
         This becomes clear when unfolding [map].
       *)
      Fail elim: (setm att_loc_val (y,state, x) tt).
      (* The challenge is to cancel the empty map case because the map
         is obviously not empty!
       *)

      (*
      TODO: I need to find a way to rewrite the LHS into
      [ [:: (y, state,x , tt); att_loc_val] ].
      If I managed to do that then I can unfold [map] and simplify.

      This is not possible because the sequence is ordered.
      Hence it is not clear at which position [(y,state,x,tt) is located. ]
       *)

      (* Preserved. *)
      move: att_loc_mem.
      elim/fmap_ind H: att_loc_val => [|m iH key value].
      + move => att_loc_mem //=.
        (* Now I have to show that [sign_loc_val] is also empty. *)
        rewrite /rem_lhs in att_loc_mem.
        move: hasheq; rewrite /hash_eq att_loc_mem //= => hasheq.
        rewrite /rem_rhs in sign_loc_mem; rewrite sign_loc_mem in hasheq.
        by [rewrite -hasheq].
      + move => key_notin att_loc_mem.
        move: m iH H key_notin att_loc_mem  => initial_set iH H key_notin att_loc_mem.

        rewrite /rem_lhs in iH.
        rewrite /rem_lhs in att_loc_mem.

        (*
          At this point I'm stuck.
          I will never be able to use the [iH] because of [att_loc_mem].

          Another question is then:
          Can I even use the induction over fmap then?!
         *)

        Restart.

    move => sign_loc_val att_loc_val state x y.
    rewrite /preserve_update_mem/remember_pre => s0 s1 h.
    rewrite /full_heap_eq' //=.
    split.
    - move: h; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; move => hasheq heq att_loc_mem sign_loc_mem.
      rewrite /rem_lhs in att_loc_mem.
      move: hasheq; rewrite /hash_eq att_loc_mem //= => att_loc_sign_loc_eq.
      rewrite /rem_rhs in sign_loc_mem; rewrite sign_loc_mem in att_loc_sign_loc_eq.
      do 2! rewrite get_set_heap_eq.
      rewrite -att_loc_sign_loc_eq.

      apply: fmap_kmap_setm.
      move => [[sig1 state1] chal1] [[sig2 state2] chal2] //=.
      move => h.
      have Hash_inj_pair := Collision_Resistence (state1,chal1) (state2,chal2).
      move/pair_equal_spec:h => [sig1_eq_sig2 hash1_eq_hash2].
      apply: pair_dist_eq.
      apply/pair_equal_spec; split.
      + exact: sig1_eq_sig2.
      + exact: (Hash_inj_pair hash1_eq_hash2).
    - move => l l_notin.
      rewrite (get_set_heap_neq _ _ _ _ (disjoint_noteq l_notin att_loc_in)).
      rewrite (get_set_heap_neq _ _ _ _ (disjoint_noteq l_notin sign_loc_in)).
      move:h; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; move => _ other_heap_eq _ _.
      exact: (other_heap_eq l l_notin).
  Qed.

  Lemma l_in_lSet {l:Location}: l \in (fset [:: l]).
  Proof.
    auto_in_fset.
  Qed.

  Lemma get_eq_loc {l: Location} {t} {c1 c2: Value l.π1 -> raw_code t} :
    l \notin fset [:: attest_loc_long; sign_loc] ->
    (forall x:Value l.π1,
        ⊢ ⦃ full_heap_eq' ⦄
          c1 x ≈ c2 x
          ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀, s₁) ⦄) ->
    ⊢ ⦃ full_heap_eq' ⦄
    x1 ← get l ;; c1 x1 ≈ x2 ← get l ;; c2 x2
  ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀, s₁) ⦄.
  Proof.
    move => l_notin.
    eapply (rsame_head_cmd_alt (cmd_get l)).
    eapply (cmd_get_preserve_pre l full_heap_eq').
    ssprove_invariant.
    2: { apply (@l_in_lSet l). }
    rewrite -fset1E fdisjoints1.
    exact: l_notin.
  Qed.

End Hash.
