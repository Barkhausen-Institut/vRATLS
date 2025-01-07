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

Obligation Tactic := idtac.

#[local] Open Scope package_scope.

From vRATLS Require Import examples.Signature.
From vRATLS Require Import examples.RA.
From vRATLS Require Import examples.RA_Locations.
From vRATLS Require Import examples.Hash.
From vRATLS Require Import extructurespp.ord.
From vRATLS Require Import extructurespp.fmap.
From vRATLS Require Import extructurespp.fset.


Module Unforgability
  (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KGc)
  (RAA : RemoteAttestationAlgorithms π1 π2 KGc)
  (RAH : RemoteAttestationHash π1 π2 KGc Alg RAA).
  Module HA := Hash π1 π2 KGc Alg RAA RAH.
  Module Locs := Locations π1 π2 KGc Alg RAA RAH.
  Import KGc KGc.KGP RAA RAH RAH.SP RAH.SP.KG HA Locs.



  (* TODO I'm not convinced that this lemma states anything meaningfull. *)
  Lemma sig_real_vs_att_real:
    Att_real ∘ Key_Gen ≈₀ Aux ∘ Sig_real ∘ Key_Gen.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    - simplify_linking.
      ssprove_code_simpl.
      rewrite /cast_fun/eq_rect_r/eq_rect.
      simplify_linking.
      ssprove_code_simpl.
      eapply rsame_head_alt_pre.

      -- pose xxx ( t : heap * heap) := match t with | (s₀, s₁) => s₀ = s₁ end.
         apply (rpost_weaken_rule _
           (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ xxx (s₀, s₁) )).
        --- apply (rpre_weaken_rule (λ '(s₀, s₁), xxx (s₀, s₁) )).
          ----  eapply r_reflexivity_alt.
            ----- instantiate (1:=Key_locs). destruct KeyGen. exact: prog_valid.
            ----- move => l. unfold xxx.
                  rewrite /Key_locs => l_not_in_Key_locs.
                  unfold get_pre_cond.
                  intros s0 s1. intros h. rewrite h. reflexivity.
            ----- move => l v l_not_in_Key_locs.
                  unfold xxx. unfold put_pre_cond.
                  intros s0 s1 h. rewrite h. reflexivity.
          ---- unfold xxx. intros s0 s1 h. exact h.
        --- intros a0 a1. destruct a0. destruct a1. split.
            + destruct H. unfold xxx in H0. exact H0.
            + destruct H. exact H.
      -- intros a. destruct a. repeat ssprove_sync_eq. intros a1. apply r_ret. intros s0' s1' h.
         split. ++ reflexivity.
                ++ exact h.
    - destruct x.
      ssprove_swap_lhs 0.
      ssprove_sync_eq => state.
      ssprove_sync_eq => sk_loc.
      simplify_linking.
      by [apply r_ret].
    - case x => s s0.
      case s => s1 s2.
      ssprove_swap_lhs 0.
      ssprove_sync_eq => state.
      ssprove_sync_eq => pk.
      by [apply r_ret].
  Qed.



  Ltac sync_sig_att :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
        lazymatch c with
(*        | x ← sample ?op ;; _ => eapply (rsame_head_cmd_alt (cmd_sample op)); [ eapply cmd_sample_preserve_pre |  ] *)
        | #put ?ℓ := ?v ;;  _ => eapply (rsame_head_cmd_alt (cmd_put ℓ v));
                                 [ eapply (cmd_put_preserve_pre ℓ full_heap_eq')
                                 | intros [] ]
                                   (* TODO look for the hypothesis in the context. *)
        | x ← get ?ℓ ;;  _ => eapply (@get_eq_loc ℓ)
(*        | x ← cmd ?c ;;     _ => eapply (rsame_head_cmd_alt c) *)
(*        | assertD ?b        _ => eapply (r_assertD_same A b) *)
        | _ => fail "No head found"
        end
    | |- _ => fail "The goal should be a syntactic judgment"
  end.

  (* To rewrite the post condition I need to "rewrite under binders".
     I could do so with setoid_rewrite: https://coq.inria.fr/refman/addendum/generalized-rewriting.html
     But the SSReflect approach to this seems once more much more intuitive to me:
     https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#rewriting-under-binders
   *)

  Import FunctionalExtensionality.
  Lemma post_eq:
    forall {t} {pre: precond} {l r: raw_code t} {post post' : postcond t t},
      (forall a b, post a b = post' a b) ->
      ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄ = ⊢ ⦃ pre ⦄ l ≈ r ⦃ post' ⦄.
  Proof.
    move => t pre l r post post' post_eq_post'.
    f_equal.
    do 2! apply functional_extensionality => ?.
    apply post_eq_post'.
  Qed.

  Lemma reshape_pair_id {T T0 T1 : Type} (f : T * T0 -> T1) : (fun '(pair x y) => f (pair x y)) = f.
  Proof.
    apply functional_extensionality; by [case].
  Qed.

  Lemma put_bind:
    forall (t : Choice.type) (l : Location) (v : l) (c : raw_code t),
      putr l v c = bind (putr l v (ret tt)) (fun x => c).
  Proof. by[]. Qed.




  Lemma sig_ideal_vs_att_ideal :
    Att_ideal ∘ Key_Gen ≈₀ (* Aux_Sig_ideal ∘ Key_Gen *) Aux ∘ Sig_ideal ∘ Key_Gen.
  Proof.
    eapply eq_rel_perf_ind with (full_heap_eq').
    1: { rewrite concat_1.
         rewrite concat₃.
         apply: Invariant_heap_eq_ideal'.
          }
    simplify_eq_rel x.
    all: ssprove_code_simpl;
      repeat simplify_linking;
      rewrite -/full_heap_eq';
      (** approach 1:
       [ under @post_eq => [a b] do [ case: a => b₀ s₀; case: b => b₁ s₁; rewrite -/(full_heap_eq (s₀,s₁))]. ]
       *)
      (** approach 2:
      [under @post_eq => a b.
       1:{ case: a => b₀ s₀; case: b => b₁ s₁.
          rewrite -/(full_heap_eq (s₀,s₁)).
          by rewrite over. }]
       *)
      (* Both of the above approaches fail because the [over] tactic expects just rewrites.
         So we do it the slightly more inconvenient way and have to state what we want.
       *)
      rewrite (@post_eq _ _ _ _ _
                 (λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ /\ full_heap_eq' (s₀,s₁))).
      2:{ case => b₀ s₀; case  => b₁ s₁. by [rewrite -/(full_heap_eq' (s₀,s₁))]. }
    - Fail ssprove_sync.
      ssprove_code_simpl.
      rewrite /cast_fun/eq_rect_r/eq_rect.
      simplify_linking.
      ssprove_code_simpl.
      eapply rsame_head_alt_pre.
      --  apply (rpost_weaken_rule _
      (λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ /\ full_heap_eq' (s₀, s₁)  )).
        ----  rewrite -(reshape_pair_id full_heap_eq').
              eapply r_reflexivity_alt.
            ----- instantiate (1:=Key_locs). destruct KeyGen. exact: prog_valid.
             ----- move => l.
                  rewrite /Key_locs. unfold Key_locs => l_not_in_Key_locs. (* Why does rewrite fail? *)
                  ssprove_invariant.
                  rewrite fset_cons.
                  rewrite fdisjointUl.
                  apply/andP.
                  split;
                  (( try rewrite -fset1E); rewrite fdisjoint1s; auto_in_fset).
            ----- move => l v l_not_in_Key_locs. ssprove_invariant.
                  unfold Key_locs.
                  ssprove_invariant.
                  rewrite fset_cons.
                  rewrite fdisjointUl.
                  apply/andP.
                  split;
                  (( try rewrite -fset1E); rewrite fdisjoint1s; auto_in_fset).
        ---- case => a0 s0; case => a1 s1. case => l r. by [split].
      -- intro a.
         destruct a.
         rewrite -(reshape_pair_id full_heap_eq').
         ssprove_sync. 2: apply (@l_in_lSet sk_loc).
          1: rewrite -fset1E fdisjoints1; auto_in_fset.

          ssprove_sync. 2: apply (@l_in_lSet pk_loc).
          1: rewrite -fset1E fdisjoints1; auto_in_fset.
          ssprove_sync. 2: apply (@l_in_lSet pk_loc).
          1: rewrite -fset1E fdisjoints1; auto_in_fset.

          move => a; by [apply r_ret].
    - ssprove_swap_rhs 0%N.
      sync_sig_att. 1: auto_in_fset.
      move => state.
      sync_sig_att.
      + ssprove_invariant.
      + move => state_loc.

        (* gets *)
        Fail eapply r_get_remember_lhs.
        (* I have to reshape the precondition into:
           [λ '(s0, s1), full_heap_eq' (s0, s1)]
         *)
        rewrite -(reshape_pair_id full_heap_eq').
        eapply r_get_remember_lhs => att_loc_val.
        eapply r_get_remember_rhs => sign_loc_val.
        (* gets done *)

        (* puts *)
        eapply r_put_lhs.
        eapply r_put_rhs.
        (* puts done *)

        ssprove_restore_mem.
        2: { eapply r_ret => s0 s1 set_vals.
             exact: (conj erefl set_vals).
        }

        (* normally: [ssprove_invariant] TODO *)
        rewrite /preserve_update_mem/remember_pre/update_heaps.
        apply: preserve_mem_full_heap_eq.
    - by [].
    - case: x => chal sig.
      ssprove_swap_lhs 0%N.

      sync_sig_att.
      1: { auto_in_fset. }
      move => state.

      rewrite -(reshape_pair_id full_heap_eq').
      eapply r_get_remember_lhs => att_loc_val.
      eapply r_get_remember_rhs => sign_loc_val.

      eapply r_ret => s0 s1 pre.
      split.
      + move:pre; rewrite /full_heap_eq'/(_ ⋊ _); repeat case; rewrite /rem_lhs; case => [heq other_eq att_loc_val_eq].
        rewrite /rem_rhs => sign_loc_val_eq.
        repeat rewrite mem_domm.
        move: heq; rewrite /hash_eq/fmap_kmap'/mapm2.
        rewrite att_loc_val_eq sign_loc_val_eq.
        rewrite -eq_fmap /eqfun => heq.
        have heq' := (heq (sig, Hash state chal)).
        move: heq'; rewrite mkfmapE /=; move => heq'; rewrite -heq'.
        apply esym.

        (* Turn the [seq.map] part into a function in order to apply the lemma. *)
        pose f (y:Type) (p: ((('signature * 'state) * 'challenge) * y)) : (('signature * 'message) * y) :=
          (let (s, challenge) := p.1 in
           let (sig0, state0) := s in
           (sig0, Hash state0 challenge)
          ,p.2).

        have fold_f (y:Type) (p: ((('signature * 'state) * 'challenge) * y)) :
          (let (s, challenge) := p.1 in
           let (sig0, state0) := s in
           (sig0, Hash state0 challenge)
             ,p.2) = f _ p by [].
        have fold_f' (y:Type) :
          (fun (p: ((('signature * 'state) * 'challenge) * y)) =>
             (let (s, challenge) := p.1 in
              let (sig0, state0) := s in
              (sig0, Hash state0 challenge)
                ,p.2)) =1 f _ by [].
        rewrite (eq_map (fold_f' _)).

        pose f' (p': (('signature * 'state) * 'challenge)) : ('signature * 'message) :=
          let (s, challenge) := p' in
          let (sig0, state0) := s in
          (sig0, Hash state0 challenge).

        have f_fst (y:Type) (p: ((('signature * 'state) * 'challenge) * y)) : f _ p = (f' p.1, p.2)
          by [rewrite /f/f'].
        have f_fst' : f _ =1 fun p => (f' p.1, p.2) by rewrite /eqfun => x; apply f_fst.

        rewrite (eq_map (f_fst' _)).
        (* Done *)

        have inj_f' : injective f'.
        1: { clear. rewrite /f'/injective.
             do 2! case; move => sig1 state1 chal1.
             do 2! case; move => sig2 state2 chal2.
             move/pair_equal_spec; case => si_eq Hash_eq.
             apply pair_dist_eq; apply pair_equal_spec; split; move => //=.
             by [apply Collision_Resistence].
        }

        by [rewrite -/(f' (sig, state, chal)) (getm_def_injx' _ _ inj_f')].
      + by [move:pre; rewrite /(_ ⋊_); do 2! case].
    - by [].
  Qed.


  Theorem RA_unforg LA A :
      ValidPackage LA Att_interface A_export A →
      fdisjoint LA (Sig_real_locp).(locs) →
      fdisjoint LA (Sig_ideal_locp).(locs) →
      fdisjoint LA Aux_locs →
      fdisjoint LA (Att_real_locp).(locs) →
      fdisjoint LA (Att_ideal_locp).(locs) →
      (AdvantageE (Att_ideal_c) (Att_real_c) A
        <= AdvantageE (Aux ∘ Sig_ideal ∘ Key_Gen) (Aux ∘ Sig_real_c) A)%R.
  Proof.
    move => va H1 H2 H3 H4 H5.
    rewrite Advantage_sym.
    simpl in *|-.
    ssprove triangle (Att_real ∘ Key_Gen) [::
      Aux ∘ Sig_real ∘ Key_Gen ;
      Aux ∘ Sig_ideal ∘ Key_Gen
      ] (Att_ideal ∘ Key_Gen) A as ineq.
    eapply le_trans.
    1: { exact: ineq. }
    clear ineq.
    rewrite sig_real_vs_att_real.

    2: exact: H4.
    2: {
      rewrite fdisjointUr.
      apply/andP; split; assumption.
    }
    rewrite GRing.add0r.
    rewrite [X in (_ + X <= _)%R]Advantage_sym.

    (* Set Typeclasses Debug Verbosity 2. *)

    rewrite sig_ideal_vs_att_ideal.
    (* Type class resolution failed because of the [Att_interface_f].
       Both advantages need to be on the same interface!
     *)
    2: exact: H5.
    2: {
      (* TODO There should be a tactic for discharging such [fdisjoint] goals! *)
      rewrite /Comp_locs.
      rewrite /Aux_locs in H3.
      rewrite /Sig_locs_ideal in H2.
      (* This feels like a silly construction. Is there a better way to arrive at this [Prop]? *)
      rewrite /is_true in H3; rewrite /is_true in H2.
      have prim_aux : true && true by [].
      rewrite -[X in X && _]H3  -[X in _ && X]H2 in prim_aux.

      move: prim_aux; rewrite -fdisjointUr (* -/fset_cat *) /=.

      (* TODO move below into extructurespp and extend. *)
      rewrite /Sig_locs_real/Key_locs.

      exact: id.
    }
    rewrite GRing.addr0.
    by [rewrite Advantage_sym].
  Qed.

End Unforgability.
