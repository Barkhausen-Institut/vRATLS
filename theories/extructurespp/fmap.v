Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssrnat ssreflect
  ssrfun ssrbool ssrnum eqtype seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From Coq Require Import Unicode.Utf8.

From extructures Require Import ord fset fmap.
From vRATLS Require Import extructurespp.ord.


(*
  TODO:
  The conversion from [setm] to [setm_def] etc.
  is always the same. So I guess one can state
  the same facts also directly for [fmap]!
 *)

Section Facts.

  Variable A:ordType.
  Variable B:Type.

  Lemma setm_def_seq_cons {a0 a1:A} {b0 b1:B} {s: seq.seq (A * B)} :
    (a0 < a1)%ord ->
    ((a0,b0) :: ((a1,b1) :: s)) = setm_def (T:=A) ((a1,b1) :: s) a0 b0.
  Proof.
    rewrite /setm_def //= => h.
    rewrite ifT //=.
  Qed.

  Lemma setm_def_seq_nil {a:A} {b:B} :
    (a,b) :: nil = setm_def (T:=A) (nil) a b.
  Proof. by [].  Qed.

  Lemma setm_def_seq_cons_eq {a0 a1:A} {b0 b1:B} {s: seq.seq (A * B)} :
    a0 == a1 ->
    (a0,b0) :: s = setm_def (T:=A) ((a1,b1) :: s) a0 b0.
  Proof.
    rewrite /setm_def //= => h.
    rewrite ifF.
    - by [rewrite ifT].
    - move:h; move/eqP => h; rewrite h.
      apply: Ord.ltxx.
  Qed.

  Lemma setm_def_seq_cons_eq' {a:A} {b0 b1:B} {s: seq.seq (A * B)} :
    (a,b0) :: s = setm_def (T:=A) ((a,b1) :: s) a b0.
  Proof. apply: (setm_def_seq_cons_eq (eqtype.eq_refl a)). Qed.

  Lemma getm_def_setm_defxy {a0 a1:A} {b0 b1:B} {s: seq.seq (A * B)}:
    getm_def (T:=A) (setm_def (T:=A) ((a0, b0) :: s) a1 b1) a1 = Some b1.
  Proof.
    elim: ((a0,b0) :: s) => [| [a0' b0'] s' iH] //=.
    - by [rewrite ifT].
    - rewrite /setm_def /= -/(setm_def s a1 b1).
      case H: (a1 == a0').
      + move/eqP: H => H; rewrite H.
        rewrite ifF //=.
        * repeat rewrite ifT //=.
        * apply: Ord.ltxx.
      + have a1_neq_a0 := H.
        move/neq_ltgt/orP:H.
        case => [a1_lt_a0|a0_lt_a1].
        * rewrite ifT //= ifT //=.
        * rewrite ifF.
          ** rewrite /getm_def /= -/(getm_def _ a1) -/(setm_def s' a1 b1).
             rewrite ifF /=.
             *** apply: iH.
             *** by [].
          ** by [move/eqP: a0_lt_a1; case: (Ord.ltgtP a1 a0')].
  Qed.

  Lemma getm_def_setm_defxx {a:A} {b:B} {s: seq.seq (A * B)}:
    getm_def (T:=A) (setm_def (T:=A) s a b) a = Some b.
  Proof.
    case: s => [|[a' b'] s'].
    - by [rewrite -setm_def_seq_nil /= ifT].
    - case H: (a == a').
      + by [move/eqP:H => H; rewrite H -setm_def_seq_cons_eq' /= ifT].
      + by [apply: getm_def_setm_defxy].
  Qed.

  Lemma getm_def_setm_defE {a x:A} {b:B} {s: seq.seq (A * B)}:
    (x == a = false) ->
    getm_def (T:=A) (setm_def (T:=A) s a b) x = getm_def (T:=A) s x.
  Proof.
    move => a_neq_x.
    elim: s => [| [a' b'] s' iH].
    - rewrite /getm_def /= ifF //=.
    - move => //=.
      case x_neq_a': (x == a').
      + have a_neq_x' := a_neq_x.
        move/eqP: x_neq_a' => x_neq_a'; rewrite x_neq_a' in a_neq_x'.
        move/neq_ltgt/orP: a_neq_x'; case => [a'_lt_a|a_lt_a'].
        * move/eqP/eqP: a'_lt_a => a'_lt_a.
          rewrite ifF //=.
          ** rewrite ifF //=.
             *** rewrite ifT //=.
                 by [apply/eqP].
             *** by [rewrite x_neq_a' eqtype.eq_sym in a_neq_x].
          ** (* a != a' and a' < a *)
            apply: (ord_lt_false a'_lt_a).
        * rewrite ifT //= ifF.
          ** by [rewrite x_neq_a' ifT].
          ** exact: a_neq_x.
      + have a_neq_x' := a_neq_x.
        move/neq_ltgt/orP: a_neq_x'; case => [x_lt_a|a_lt_x].
        * rewrite eqtype.eq_sym in x_neq_a'.
          have x_neq_a'' := x_neq_a'.
          move/neq_ltgt/orP: x_neq_a''; case => [a'_lt_x|x_lt_a'].
          ** have a'_lt_a := Ord.lt_trans a'_lt_x x_lt_a.
             have a'_lt_a' := a'_lt_a.
             move: a'_lt_a'; rewrite /Ord.lt; move/andP => [a'_leq_a a'_neq_a].
             move: a'_lt_x; rewrite /Ord.lt; move/andP => [a'_leq_x a'_neq_x].
             move: x_lt_a; rewrite /Ord.lt; move/andP => [x_leq_a x_neq_a].
             rewrite ifF //=.
             *** rewrite ifF //=.
                 **** rewrite ifF.
                      ***** by [exact: iH].
                      ***** apply/eqP/eqP; rewrite eqtype.eq_sym; exact: a'_neq_x.
                 **** apply/eqP/eqP; rewrite eqtype.eq_sym; exact: a'_neq_a.
             *** rewrite eqtype.eq_sym.
                 apply/negP/negP/nandP.
                 left.
                 rewrite Ord.ltNge in a'_lt_a. exact: a'_lt_a.
          ** case a_lt_a': (a < a')%ord => //=.
             *** by [rewrite ifF //= ifF //= eqtype.eq_sym].
             *** move: a_lt_a'; rewrite /Ord.lt; move/nandP; case.
                 **** rewrite -Ord.ltNge /Ord.lt; move/andP => [a'_leq_a a'_neq_a].
                      rewrite ifF //=.
                      ***** rewrite ifF.
                      ****** exact: iH.
                      ****** rewrite eqtype.eq_sym; exact: x_neq_a'.
                      ***** apply/negP/negP; rewrite eqtype.eq_sym; exact: a'_neq_a.
                 **** move/negbNE => a_eq_a'. rewrite ifT //=.
                      by [rewrite ifF].
        * case a_lt_a': (a < a')%ord => //=. (* TODO same as above: refactor! *)
          ** by [rewrite ifF //= ifF //= eqtype.eq_sym].
          ** move: a_lt_a'; rewrite /Ord.lt; move/nandP; case.
             *** rewrite -Ord.ltNge /Ord.lt; move/andP => [a'_leq_a a'_neq_a].
                 rewrite ifF //=.
                 **** rewrite ifF.
                      ***** exact: iH.
                      ***** exact: x_neq_a'.
                 **** apply/negP/negP; rewrite eqtype.eq_sym; exact: a'_neq_a.
             *** move/negbNE => a_eq_a'. rewrite ifT //=.
                 by [rewrite ifF].
  Qed.

  Lemma setm_def_seq_consE {a:A} {b0 b1:B} {s: seq.seq (A * B)} :
    mkfmap (setm_def (T:=A) s a b0) = mkfmap (setm_def (T:=A) ((a,b1) :: s) a b0).
  Proof.
    rewrite -eq_fmap.
    rewrite /eqfun => x.
    repeat rewrite mkfmapE.
    case: s => [| [k' v'] s'].
    - rewrite /setm_def [RHS]//=.
      rewrite ifF.
      + by [rewrite ifT].
      + apply: Ord.ltxx.
    - rewrite /setm_def //=. rewrite -/(setm_def s' a b0).
      rewrite [in RHS]ifF.
      + rewrite [in RHS]ifT => [|//=].
        case H: (a == k').
        * move: H; move/eqP => H.
          rewrite ifF.
          ** case P: (x == a).
             *** move: P; move/eqP => P; rewrite P.
                 rewrite /getm_def //=.
                 repeat rewrite ifT //=.
             *** rewrite /getm_def //=.
                 rewrite ifF //=.
                 rewrite -/(getm_def s' x).
                 rewrite ifF //=.
                 rewrite H in P.
                 rewrite ifF //=.
          ** rewrite H; apply Ord.ltxx.
        * move: H; move/neq_ltgt/orP.
          case => [a_lt_k|k_lt_a].
          ** rewrite ifT //=.
          ** rewrite ifF.
             *** rewrite /getm_def //=.
                 case I: (x == a).
                 **** rewrite ifF //=.
                      ***** rewrite -/(getm_def (setm_def _ _ _)).
                      move/eqP:I => I; rewrite I.
                      apply: getm_def_setm_defxx.
                      ***** move/eqP: I => I; rewrite I.
                      move/eqP: k_lt_a; case: (Ord.ltgtP a k') => //=.
                 **** repeat rewrite -/(getm_def _ x).
                      by [rewrite getm_def_setm_defE].
             *** move: k_lt_a; move/eqP/eqP.
                 apply: lt_antisym.
      + apply: Ord.ltxx.
  Qed.


  Lemma getm_def_injx {A':ordType} {a:A} {f: A -> A'} {s: seq.seq (A * B)} :
    injective f ->
    getm_def [seq (f p.1, p.2) | p <- s] (f a) = getm_def s a.
  Proof.
    move => inj_f.
    elim: s => [| ab s' iH].
    - by [].
    - rewrite /seq.map -/(seq.map _ s') /getm_def -/(getm_def s' a) -/(getm_def _ (f a)) /=.
      case e: (f a == f ab.1).
      + move/eqP/inj_f/eqP:e => e; by [rewrite ifT].
      + move: e; rewrite (inj_eq inj_f) => e; by [rewrite ifF].
  Qed.

  Lemma getm_def_injx' {A':ordType} {a:A} {f: A -> A'} {s: {fmap A → B}} :
    injective f ->
    getm_def [seq (f p.1, p.2) | p <- s] (f a) = s a.
  Proof. apply getm_def_injx. Qed.


  Lemma getm_injx' {A':ordType} {a:A} {f: A -> A'} {s: {fmap A → B}} :
    injective f ->
    (mkfmap [seq (f p.1, p.2) | p <- s]) (f a) = s a.
  Proof.
    rewrite mkfmapE; apply getm_def_injx'.
  Qed.

  Lemma getm_def_seq_map_id {a:A} {s: seq.seq (A * B)} :
    getm_def [seq (p.1, p.2) | p <- s] a = getm_def s a.
  Proof.
    pose pair_id (X Y : Type) (x: prod X Y) := (x.1,x.2).
    have pair_id_eq_id (X Y : Type) (x: prod X Y) : pair_id X Y x = id x
      by [rewrite /id/pair_id; apply esym; apply surjective_pairing].
    have pair_id_eq_id' (X Y : Type) : pair_id X Y =1 id.
      by [rewrite /eqfun => x; apply pair_id_eq_id].
    have eid := pair_id_eq_id' A B.
    by [rewrite (eq_map eid) map_id].
  Qed.

  Lemma getm_def_seq_step {S T:ordType} {a₀:S*T} {a₁: seq.seq (S*T)} {a₂:S} :
    getm_def (fset (a₀ :: a₁)) a₂ = getm_def (a₀ :: (fset a₁)) a₂.
  Proof.
  Admitted.

  Lemma rem_unit {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S) (x₂:T):
    (x₁, x₂) \in domm s -> x₁ \in domm (mkfmap (domm s)).
  Proof.
    move: x₁ x₂.
    elim/fmap_ind : s => /=.
    - move => x₁ x₂.
      by rewrite domm0 in_fset0.
    - move => s iH [x₁ x₂] v x_notin_s x₁' x₂'.
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
             rewrite mem_domm in iH.
             exact: iH.
  Qed.

  Lemma rem_unit' {S T:ordType} {X:eqType} (s:{fmap (S*T) -> X}) (x₁:S):
    x₁ \in domm (mkfmap (domm s)) -> exists (x₂:T), (x₁, x₂) \in domm s.
  Proof.
    move: x₁.
    elim/fmap_ind : s => /=.
    - move => x₁.
      rewrite mem_domm mkfmapE domm0 //=.
    - move => s iH [x₁ x₂] v x_notin_s x₁'.
      rewrite mem_domm.

      rewrite domm_set mkfmapE -fset_cons getm_def_seq_step /getm_def -/(getm_def _ x₁') -mkfmapE /=.

      case H_x₁: (x₁' == x₁).
      -- move => x_in_s.
         exists x₂.
         move/eqP:H_x₁ => H_x₁; rewrite H_x₁ //=.
         rewrite in_fset.
         exact: mem_head.
      -- rewrite -mem_domm => x₁'_in_s.
         specialize (iH x₁' x₁'_in_s).
         case: iH => x₂' iH.
         exists x₂'.
         rewrite /domm in iH.
         by rewrite fset_cons in_fsetU1; apply/orP; right.
  Qed.

End Facts.
