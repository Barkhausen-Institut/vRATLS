
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  fingroup.fingroup prime ssrnat ssreflect ssrfun ssrbool ssrnum.
Set Warnings "notation-overridden,ambiguous-paths".

Open Scope ring_scope.
Import GroupScope GRing.Theory.


Parameter gT : finGroupType.
Parameter prime_order : prime #|gT|.

Definition p := #|gT|.

Lemma p_gt1 : (1 < p)%N.
Proof.
  apply (prime_gt1 prime_order).
Qed.

(* Fails because the [p] needs to be converted. *)
Fail Definition intoZp : 'I_p -> 'Z_p := enum_val.

(* Detour via nat (implicit coercion). *)
Definition intoZp : 'I_p -> 'Z_p := inZp.

(* Direct conversion via cast using the fact [1 < p]. *)
Definition intoZp' : 'I_p -> 'Z_p.
Proof.
  rewrite -(Zp_cast p_gt1) //=.
Defined.

Fail Definition fromZp : 'Z_p -> 'I_p := enum_rank.

(* We cannot reuse the proof because its type needs to be converted. *)
Fail Definition fromZp : 'Z_p -> 'I_p :=
  fun x =>
    match x with
    | Ordinal m m_lt_p => Ordinal m_lt_p
    end.

(* The same as above but with casting the type of the proof. *)
Definition fromZp : 'Z_p -> 'I_p.
Proof.
  case => m.
  rewrite (Zp_cast p_gt1) => m_lt_p.
  exact (Ordinal m_lt_p).
Defined.

(* But now I need to rewrite with these stupid rewrites in the term/type. *)
Lemma intoZp_fromZp : forall x : 'I_p,
    fromZp (intoZp' x) = x.
Proof.
  rewrite /intoZp'/fromZp => x.
  rewrite /eq_rect_r/eq_rect //=.
  case: x => m m_lt_p //=.
  Check Zp_cast.
  case: (Zp_cast (p:=p) p_gt1); rewrite /Zp_trunc => Zp_eq_p //=.
  Fail rewrite Zp_eq_p.
Abort.

Lemma intoZp_fromZp' : forall x : 'I_p,
    fromZp (intoZp x) = x.
Proof.
  rewrite /intoZp/fromZp/inZp => x.
  rewrite /eq_rect_r/eq_rect //=.
  case: x => m m_lt_p //=.
Abort.

Definition fromZp'' (q:nat) : 'Z_q.+2 -> 'I_q.+2 := fun x => x.
Definition intoZp'' (q:nat) : 'I_q.+2 -> 'Z_q.+2 := fun x => x.

Definition z (q:nat) : 'Z_q -> 'Z_q.-2.+2 := fun x => x.
Definition y (q:nat) : 'Z_q -> 'I_q.-2.+2 := fun x => x.

Check False_rect.
Check False_rec.
Check Bool.diff_false_true.

(* This fails because it requires a rewrite of [H]. *)
Fail Definition into (q:nat) (H: (1 < q)%N) : 'I_q -> 'I_q.-2.+2 :=
  match q with
  | _.+2 => id
  | _ => False_rect _ (Bool.diff_false_true H)
  end.

Definition into {q:nat} : (1 < q)%N -> 'I_q -> 'I_q.-2.+2 :=
  match q with
  | _.+2 => fun _ => id
  | _ => fun H => False_rect _ (Bool.diff_false_true H)
  end.

Print into.

Definition into' {q:nat} : (1 < q)%N -> 'I_q -> 'I_q.-2.+2.
Proof.
  case: q => //=.
  case => //=.
Defined.

Print into'.

Definition into'' {q:nat} : (1 < q)%N -> 'I_q -> 'I_q.-2.+2.
Proof.
  case: q.
  - move => H. inversion H.
  - case.
    + move => H. inversion H.
    + move => n H. exact id.
Defined.

Print into''.

(** Lesson learned
    Creating functions with tactics results in really complex terms.
    Those are hard to handle when using these functions in lemmas.
 **)

(* TODO How do I formulate such a function using Equations? *)

Definition from {q:nat} : (1 < q)%N -> 'I_q.-2.+2 -> 'I_q :=
  match q with
  | _.+2 => fun _ => id
  | _ => fun H => False_rect _ (Bool.diff_false_true H)
  end.

Lemma into_from {q:nat} (H : (1 < q)%N) x : from H (into H x) = x.
Proof. by case: q H x => [|[]]. Qed.

Lemma into_from' {q:nat} (H : (1 < q)%N) x : from H (into H x) = x.
Proof.
  case: q H x => //=.
  case => //=.
Qed.

Lemma from_into {q:nat} (H : (1 < q)%N) x : into H (from H x) = x.
Proof. by case: q H x => [|[]]. Qed.
