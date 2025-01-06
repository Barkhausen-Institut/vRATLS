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
From vRATLS Require Import extructurespp.ord.
From vRATLS Require Import extructurespp.fmap.
From vRATLS Require Import extructurespp.fset.


(* TODO All these proof should be redone based on the new tactic. *)

Module Locations
  (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
  (π2 : KeyGenParams π1)
  (KGc : KeyGen_code π1 π2)
  (Alg : SignatureAlgorithms π1 π2 KGc)
  (RAA : RemoteAttestationAlgorithms π1 π2 KGc)
  (RAH : RemoteAttestationHash π1 π2 KGc Alg RAA).

  Import KGc.KGP RAA RAH RAH.SP.

    (********************************************)
  (********************************************)
  (********************************************)
  (********************************************)
  (********************************************)
  (*
  Definition Comp_locs := fset [:: pk_loc ; sk_loc ; state_loc ; sign_loc ].
  Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
  Definition Attestation_locs_ideal := Attestation_locs_real :|: fset [:: attest_loc_long ].
  *)

  Lemma concat_1 :
    Attestation_locs_ideal :|: Key_locs = Attestation_locs_ideal.
  Proof.
    rewrite /Attestation_locs_ideal.
    rewrite /Attestation_locs_real/Key_locs.
    rewrite -fset_cat /cat.
    rewrite fsetUC.
    apply/eqP.
    rewrite -/(fsubset (fset [:: pk_loc; sk_loc]) _).
    (*rewrite [X in fsubset _ (_ :|: X)]fset_cons.*)
    rewrite fset_cons.
    rewrite [X in fsubset X _]fset_cons.
    apply fsetUS.
    rewrite fset_cons.
    rewrite [X in fsubset X _]fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  Qed.

  Lemma concat_1_real :
    Attestation_locs_real :|: Key_locs = Attestation_locs_real.
  Proof.
    rewrite /Attestation_locs_real/Key_locs.
    rewrite fsetUC.
    apply/eqP.
    rewrite -/(fsubset (fset [:: pk_loc; sk_loc]) _).
    (*rewrite [X in fsubset _ (_ :|: X)]fset_cons.*)
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  Qed.

  Lemma concat_2 :
    Comp_locs :|: Key_locs = Comp_locs.
  Proof.
    rewrite /Comp_locs/Key_locs.
    rewrite fsetUC.
    apply/eqP.
    rewrite -/(fsubset (fset [:: pk_loc; sk_loc]) _).
    (*rewrite [X in fsubset _ (_ :|: X)]fset_cons.*)
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  Qed.

  Lemma general_subset_concat : forall a b c : Location,
    ((fset [:: a ; b ; c]) :|: (fset [:: a ; b])) = (fset [:: a ; b ; c]).
  Proof.
    intros.
    rewrite fsetUC.
    apply/eqP.
    rewrite -/(fsubset (fset [:: a; b]) _).
    (*rewrite [X in fsubset _ (_ :|: X)]fset_cons.*)
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite fset_cons.
    rewrite [X in fsubset _ X]fset_cons.
    apply fsetUS.
    rewrite !fset_cons -fset0E.
    apply fsub0set.
  Qed.


  Lemma concat₃ :
    (Aux_locs :|: (Sig_locs_ideal :|: Key_locs)) = Comp_locs.
  Proof.
    rewrite /Aux_locs/Sig_locs_ideal/Sig_locs_real/Key_locs/Comp_locs.
    repeat rewrite fset_fsetU_norm2.
    repeat rewrite -fsetUA. (* base shape *)

    (* stategy: deduplicate by moving same items to the left. *)
    (* shift item on index 4 to the right (index starts from 0) *)
    do 2! rewrite fsetUA.
    rewrite [X in _ :|: X]fsetUC.
    repeat rewrite -fsetUA.
    rewrite fsetUid.

    (* index 0 is special *)
    rewrite fsetUC.
    repeat rewrite -fsetUA.

    (* index 1 *)
    rewrite [X in _ :|: X]fsetUC.
    repeat rewrite -fsetUA.
    rewrite fsetUid.

    (* index 2 *)
    do 1! rewrite fsetUA.
    rewrite [X in _ :|: X]fsetUC.
    repeat rewrite -fsetUA.
    rewrite fsetUid.

    (* now all we need to do is put them into the right order *)
    (* index 2 *)
    do 1! rewrite fsetUA.
    rewrite [X in _ :|: X]fsetUC.
    repeat rewrite -fsetUA.

    (* index 0 *)
    rewrite fsetUC.
    repeat rewrite -fsetUA.

    (* index 0 *)
    rewrite fsetUC.
    repeat rewrite -fsetUA.

    (* now fold back into fset (from right to left ... think list!) *)
    repeat rewrite -fset_cat cat1s.
    by [].
  Qed.

  Lemma concat_3 :
  fset [:: pk_loc; state_loc]
    :|: (fset [:: pk_loc; sk_loc]
    :|: fset [:: sign_loc]
    :|: fset [:: pk_loc; sk_loc])
  = fset [:: pk_loc; state_loc; pk_loc; sk_loc; sign_loc].
Proof.
  (* LHS *)
  repeat rewrite fset_fsetU_norm2.
  repeat rewrite -fsetUA. (* base shape *)

  (* stategy: deduplicate by moving same items to the left. *)
  (* shift item on index 4 to the right (index starts from 0) *)
  do 2! rewrite fsetUA.
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.
  rewrite fsetUid.

  rewrite fsetUC.
  repeat rewrite -fsetUA.

  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.
  rewrite fsetUid.

  do 1! rewrite fsetUA.
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.
  rewrite fsetUid.

  (* final order *)
  do 1! rewrite fsetUA.
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.

  (* do 0! rewrite fsetUA. *)
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.

  rewrite fsetUC.
  repeat rewrite -fsetUA.

  (* collapse into fset *)
  repeat rewrite -fset_cat cat1s.

  (* RHS *)
  apply esym.

  repeat rewrite fset_fsetU_norm5. (* normalize *)
  repeat rewrite -fsetUA. (* base shape *)

  rewrite fsetUC.
  repeat rewrite -fsetUA.

  (* do 0! rewrite fsetUA. *)
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.
  rewrite fsetUid.

  (* final order *)

  (* do 0! rewrite fsetUA. *)
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.

  (* do 0! rewrite fsetUA. *)
  rewrite [X in _ :|: X]fsetUC.
  repeat rewrite -fsetUA.

  rewrite fsetUC.
  repeat rewrite -fsetUA.

  (* collapse into fset *)
  by repeat rewrite -fset_cat cat1s.
Qed.

End Locations.
