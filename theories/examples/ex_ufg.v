(* so far, this is an abstract implementation of a signature scheme 
initially implemented for RA.v
Will be extended by actual signature implementations
*)

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

(*
  This is needed to make definitions with Equations transparent.
  Otherwise they are opaque and code simplifications in the
  proofs with [ssprove_code_simpl] does not resolve properly.
 *)
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Require Import examples.Signature.

Import PackageNotation.

Obligation Tactic := idtac.

#[local] Open Scope package_scope.
Variable (n: nat).
Definition pos_n: nat := 2^n.
Definition chSet t := chMap t 'unit.
Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Module Type ExistentialUnforgeability
  (π1 : SignatureParams)
  (π2 : SignatureConstraints)
  (Alg : SignatureAlgorithms π1 π2)
  (Prim : SignaturePrimitives π1 π2 Alg).

  Import π1.
  Import π2.
  Import Alg.
  Import Prim.

  Definition oracle : nat := 70. 

  Definition Ex_unforge_loc := fset [:: pk_loc ; sk_loc ; sign_loc].

  (*
    #val #[oracle    ] : 'unit → (fmap (Signature * Message) -> 'unit) ;
  *)

  Definition i_msg := #|chMessage|.        

  Definition ExUfg_interface := [interface
    #val #[init] : 'unit → 'unit ;
    #val #[get_pk] : 'unit → 'pubkey ;    
    #val #[oracle] : 'message → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
  ].

  Definition Ex_Ufg : package Ex_unforge_loc [interface] 
    Prim_interface_init
  := [package
    #def  #[init] (_ : 'unit) : 'unit
    { 
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      ret tt
    } ;
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    { 
      pk ← get pk_loc  ;;
      ret pk
    } ;
    #def  #[sign] (msg : 'message) : 'signature
    (* this should be 'unit -> unit, and we can sample the message but then we need to redefine the type. Also, sampling isn't really accurate *)
    { 
      sk ← get sk_loc ;;
      let sig := Sign sk msg in
      S ← get sign_loc ;;
      let S' := setm S (sig, msg) tt in
      #put sign_loc := S' ;;
      ret sig
    };
    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      pk ← get pk_loc  ;;
      let bool1 := Ver_sig pk sig msg in
      S ← get sign_loc ;;
      let bool2 := ( (sig,msg) \in domm S ) in
      ret (andb bool1 bool2)
      (*ret bool2*)
    }
  ].  
    
  Definition ɛ_indist A :=
    AdvantageE Prim_real_init Prim_ideal_init A.

  Definition AdvantageS (G₀ : raw_package) (A : raw_package) : R :=
    `| Pr (A ∘ G₀) true |.     

  Definition ɛ_unforge A :=
    AdvantageS Ex_Ufg A. 

  (* TODO: *)
  (* Explain difference in definitions *)

  Theorem commitment_hiding :
    ∀ LA A, 
    ValidPackage LA Prim_interface_init A_export A →
    fdisjoint LA Prim_locs_real →
    fdisjoint LA Prim_locs_ideal →
    fdisjoint LA Ex_unforge_loc →
    ( (ɛ_unforge A) <= (ɛ_indist A))%R.
  Proof.
  Admitted.
    
(*
Lemma exquivalence_of_definitions: 
    Prim_ideal_init ≈₀ Ex_Ufg.
  Proof.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  - ssprove_sync_eq.
    eapply rpost_weaken_rule. 
    1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. 
    intuition auto. 
  - eapply rpost_weaken_rule. 
    1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. 
    intuition auto.
  - ssprove_sync_eq => sk.
    ssprove_sync_eq => sign_loc.
    eapply rpost_weaken_rule. 
    1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. 
    intuition auto.
  - simplify_linking.
    destruct m.
    ssprove_sync_eq => sign_loc.
    eapply rpost_weaken_rule. 
    1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. 
    intuition auto.
  Qed.
  *)


End ExistentialUnforgeability.