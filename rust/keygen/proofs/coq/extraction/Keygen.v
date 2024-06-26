(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import Rand. (* as Rng *)

Notation t_Nat_t := (int64).

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Definition main (_ : unit) : unit :=
  tt.

Record t_State : Type :={
  f_sk : t_Option_t int64;
}.

Definition impl__State__key_gen (self : t_State_t) : (t_State_t × int64) :=
  let self := (if
      impl__is_none (f_sk self)
    then
      let '(_,out) := (f_gen (thread_rng tt)) : (t_ThreadRng_t × int64) in
      let sk0 := (out) : int64 in
      let '(tmp0,out) := (impl__replace (f_sk self) sk0) : (t_Option_t int64 × t_Option_t int64) in
      let self := (Build_t_State tmp0) : t_State_t in
      let _ := (out) : t_Option_t int64 in
      self
    else
      self) : t_State_t in
  let '(_,out) := (f_gen (thread_rng tt)) : (t_ThreadRng_t × int64) in
  let pk := (out) : int64 in
  let hax_temp_output := (pk) : int64 in
  (self,hax_temp_output).
