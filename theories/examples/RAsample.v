(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.

(** REMOTE ATTESTATION
    VERIFIER                             PROVER
Generates a chal-
  lenge 'chal'
                   -----chal----->    
                                       Attestation
                                       (using TPM) 
                   <-----res------
Validity check
  of proof
  *)

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
  proofs with [ssprove_code_simpl] do not resolve properly.
 *)
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

Require Import examples.Signature.
Require Import examples.RA.

Module Protocol
    (π1 : SignatureParams)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2)
    (π4 : RemoteAttestationAlgorithms π1 π2 π3)
    (π5 : SignatureScheme π1 π2 π3)
    (π6 : RemoteAttestation π1 π2 π3 π4 π5).

  Import π1 π2 π3 π4 π5 π6.

  Parameter Hash' : chState -> chChal -> chMessage.

  Definition chal_loc    : Location := ('challenge ; 5%N).
  Definition RA_locs := fset [:: chal_loc ; sk_loc ; pk_loc ; state_loc].
  Definition RA   : nat := 46. (* routine to get the public key *)
  Definition RA_prot_interface := [interface #val #[RA] : 'unit → 'bool ].


  (* those are redefined, change above once fixed *)
  Definition Challenge := Arit (uniform pos_n).
  Definition chChal : choice_type := 'fin (mkpos pos_n).
  Notation " 'challenge " := Challenge       (in custom pack_type at level 2).
  Notation " 'challenge " := chChal        (at level 2): package_scope.

  Definition RA_real :
      package
        RA_locs
        Att_interface
        RA_prot_interface
    :=
    [package
      #def #[RA] (_ : 'unit) : 'bool
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
        #import {sig #[attest] : 'challenge → 'signature } as attest ;;
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;

        (* PROTOCOL *)

        (* Verifier-side *)

        (* KeyGen *)
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        (* sample the challenge *)
        chal ← sample uniform pos_n ;;
        #put chal_loc := chal ;;
        (* take the state *)
        state ← get state_loc ;; (* not sure here. Would like to sample, but it's not random*)
        (* compute message *)
        let msg := Hash' state chal in

        (* Send message to prover *)
        let msg_p :=msg in

        (* Prover-side *)
        (* sign (=attest) message *)
        att ← attest msg_p ;;

        (* Send attestation to verifier *)
        let att_v := att in

        (* Verifier-side *)
        bool ← verify_att chal att_v ;;

        (* TODO
           This verification does not make sense to me.
           It is a routine on the prover side, I believe.
           What does that even mean?
           At this point the verifier asks:
           Is the prover actually running a system that has my state?
         *)

        (* We make the whole communication and the pk available to the attacker. *)
        ret (pk, (msg, att))

        (* FIXME
           I do not think that the handling of state is properly done here.
           Not that this protocol assumes that the verifier and the prover
           have the verify same [pk] and [sk].
         *)
      }
    ].

  Definition RA_ideal :
      package
        locs interface
        [interface ]
    :=
    [package
      #def #[RA (_ : 'unit) : (_,_)
      {
        #import {sig #[get_pk] : 'unit → 'pubkey } as get_pk ;;
        #import {sig #[attest] : 'challenge → 'signature } as attest ;;
        #import {sig #[verify_att] : ('challenge × 'signature) → 'bool } as verify_att ;;
        
        ...
      };

      ].


End Protocol.

