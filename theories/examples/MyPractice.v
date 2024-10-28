
(**Some Random examples from the SSProve repository to practice **)

(**********************
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".


From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude pkg_composition.


From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

(*why local?*)
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.


(*Module Type is like a interface? specifying paras and defs that any module 
claiming to be of this type must satisfy. *)
Module Type SimpleParams.
    Parameter Space : finType.   (* Space a para represent finite type, BUT in  DDH, this type may 
    represent the space of possible group elements or random values*)
    Parameter Space_pos : Positive #|Space|.   (*For Positive, I copied the above*)
    (*Space_pos is a para that specifies Space, +ve no of elements (i.e, #|Space|).
    and Positive #|Space| means it’s greater than 0? *)
    Print Prelude.
End SimpleParams.

Module SimpleExample (SP : SimpleParams).
(* def of module SimpleExample with para SP, and import allows direct access 
to def and para from SimpleParams *)
Import SP.


Definition SAMPLE := 0%N. (* SAMPLE has value 0?*)

#[local] Existing Instance Space_pos.

Definition chElem : choice_type := 'fin #|Space|.
Definition i_space := #|Space|.


Definition secret_loc1 : Location := (chElem ; 33%N).
Definition secret_loc2 : Location := (chElem ; 34%N).


(*chElem defines choice types for working with finite types*)


Definition Simple_locs := fset [:: secret_loc1 ; secret_loc2].


Definition DDH_real :
package                                          (* Note: A package with no imports is called a game. *)
  Simple_locs                                    (* Location. *)
  [interface]                                    (* A list of interface for imports, in this case its empty*)
  [interface                                     (* A list of interface for Exports *)
    #val #[ SAMPLE ] : 'unit → 'unit ]           (* [SAMPLE] could be nat no/identifier*)
  :=                                             (* Defined *)
  [package
    #def #[ SAMPLE ] (s : 'unit) : 'unit
    {
      a ← sample uniform i_space ;;
      b ← sample uniform i_space ;;
      #put secret_loc1 := a ;;
      #put secret_loc2 := b ;;
      ret s
    }
  ].

******************)


(* DDH example begins here *)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".


From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude pkg_composition.


From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

(*why local?*)
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.



(* So here, GroupParam and DDHParams define parameters for the game: *)
Module Type GroupParam.

  Parameter gT : finGroupType.             (* gT is the group type here *)
  Definition ζ : {set gT} := [set : gT].   (*The set of all elements in the group *)
  Parameter g :  gT.                       (* g is a generator for the group *)
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].      (*  The group has a prime order *)

End GroupParam.

(* and also DDHParams specifies the finite type Space, 
representing possible secret choices, and asserts that the space is non-empty with Space_pos.*)
Module Type DDHParams.
  Parameter Space : finType.
  Parameter Space_pos : Positive #|Space|.
End DDHParams.

(*The DDH module defines with two module TYPES DDHParams and GroupParam as parameters?*)
Module DDH (DDHP : DDHParams) (GP : GroupParam). (***Starts from here*)

  Import DDHP.
  Import GP.

  Definition SAMPLE := 0%N.

  #[local] Existing Instance Space_pos.

  Definition GroupSpace : finType := gT.
  #[local] Instance GroupSpace_pos : Positive #|GroupSpace|.
  Proof.
    apply /card_gt0P; by exists g.
  (* Needs to be transparent to unify with local positivity proof? *)
  Defined.

  Definition chGroup : choice_type := 'fin #|GroupSpace|.

  Definition i_space := #|Space|.
  Definition chElem : choice_type := 'fin #|Space|.

  Notation " 'group " := (chGroup) (in custom pack_type at level 2).

  Definition secret_loc1 : Location := (chElem ; 33%N).
  Definition secret_loc2 : Location := (chElem ; 34%N).
  Definition secret_loc3 : Location := (chElem ; 35%N).

  Definition DDH_locs :=
    fset [:: secret_loc1 ; secret_loc2 ; secret_loc3].


    (*The DDH_real package samples two random group elements a and b and computes:
    The pair (g^a, g^b, g^(a*b)), which represents the real interaction in the DDH problem. 
    Here a and b are sampled uniformly at random.
    *)
  Definition DDH_real :
    package DDH_locs [interface]
      [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ] :=
      [package
        #def #[ SAMPLE ] (_ : 'unit) : 'group × 'group × 'group
        {
          a ← sample uniform i_space ;;
          b ← sample uniform i_space ;;
          #put secret_loc1 := a ;;
          #put secret_loc2 := b ;;
          ret (fto (g^+ a), (fto (g^+ b), fto (g^+(a * b))))
        }
      ].

  Definition DDH_E := [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ].


  
  (*The DDH_ideal package instead samples three independent random group elements a, b, and c. It returns (g^a, g^b, g^c), 
  which mimics the structure of a real instance but replaces the product g^(a*b) with an independent third element g^c.*)
  Definition DDH_ideal :
    package DDH_locs [interface] DDH_E :=
      [package
        #def #[ SAMPLE ] (_ : 'unit) : 'group × 'group × 'group
        {
          a ← sample uniform i_space ;;
          b ← sample uniform i_space ;;
          c ← sample uniform i_space ;;
          #put secret_loc1 := a ;;
          #put secret_loc2 := b ;;
          #put secret_loc3 := c ;;
          ret (fto (g^+a), (fto (g^+b), fto (g^+c)))
        }
      ].


    (*The loc_GamePair represents a pair of games:
        b = true: The real game (DDH_real).
        b = false: The ideal game (DDH_ideal).*)
  Definition DDH :
    loc_GamePair [interface #val #[ SAMPLE ] : 'unit → 'group × 'group × 'group ] :=
    λ b,
      if b then {locpackage DDH_real } else {locpackage DDH_ideal }.

  Definition ϵ_DDH := Advantage DDH.

End DDH.   (***Ends here*)

