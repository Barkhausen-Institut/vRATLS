

(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.
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

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

Obligation Tactic := idtac.

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
** ATTESTATION
Input: 'chal'
--------------
TPM generates 'quoted' information
sig = Sign(chal,key,quoted)
--------------
Output: '(sig,quoted)'
**)

(*
Introduction:
Here we will look at the remote attestation that is using a TPM for secure hardware 
cryptography. It is like the version used on the RATLS paper.
*)

Module Type SignatureParams.

    Variable (n: nat).
    Definition pos_n: nat := 2^n.

    (*
      FIXME This does not make much sense, does it?
      Keys should be of type [uniform p].

      J: I made this because the signature ideal-game requires us
      to create and add to a set and ask if something is an element of
      that set. This construction is from MACCCA.v
      (See joy of crypto, p. 194)
      Furthermore, this entire file works without a single
      'sampling' call. I guess the "randomness / samlpling" is an
      important part of ssprove. But the core is that it is able to show
      that two packages are the same. They may or may not use a sampling.
      But, it indeed might be necessary/ helpful to add it at some point.
     *)

    Definition SecKey : choice_type := chFin(mkpos pos_n).
    Definition PubKey : choice_type := chFin(mkpos pos_n).
    Definition State : choice_type := chFin(mkpos pos_n).
    Definition Challenge : choice_type := chFin(mkpos pos_n).
    Definition Attestation : choice_type := chFin(mkpos pos_n).
    Definition Message : choice_type := chFin(mkpos pos_n).
    Definition Signature : choice_type := chFin(mkpos pos_n).

End SignatureParams.

(** |  SIGNATURE  |
    |   SCHEME    | **)

Module Type SignatureAlgorithms (π : SignatureParams).

  Import π.

  #[local] Open Scope package_scope.

  (*
    FIXME
    This also looks strange to me:
    It seems like the whole scheme builds upon an
    asymmetric encryption scheme.
    If so, then we should definitely show that this
    is indeed the case!

    J: I don't understand the question. I've never defined an
    encryption nor an decryption functionality. Where do you
    get the impression that we use an asymmetric enc. scheme?

    S: From the presence of a public-secret key pair.
   *)

  (*TODO Use the [kgen] function from MACCA. *)
  Parameter KeyGen : (SecKey × PubKey).

  Parameter Sign : ∀ {M:Type} (sk : SecKey) (m : M), Signature.

  Parameter Ver_sig : ∀ (pk : PubKey) (sig : Signature) (m : Message), 'bool.

  Parameter Attest :
    ∀ {L : {fset Location}} (sk : SecKey) ( c : Challenge ) (s : State),
       code L [interface] Signature.

  Parameter Ver_att :
    ∀ {L : {fset Location}} (pk : PubKey) (att : Attestation)
                   ( c : Challenge) ( s : State),
       code L [interface] 'bool.

End SignatureAlgorithms.

Module RemoteAttestation (π : SignatureParams)
  (Alg : SignatureAlgorithms π).

  Import π.
  Import Alg.

  #[local] Open Scope package_scope.

  Notation " 'pubkey "    := PubKey      (in custom pack_type at level 2).
  Notation " 'pubkey "    := PubKey      (at level 2): package_scope.
  Notation " 'signature " := Signature   (in custom pack_type at level 2).
  Notation " 'signature " := Signature   (at level 2): package_scope.
  Notation " 'state "     := State       (in custom pack_type at level 2).
  Notation " 'state "     := State       (at level 2): package_scope.
  Notation " 'challenge " := Challenge   (in custom pack_type at level 2).
  Notation " 'challenge " := Challenge   (at level 2): package_scope.
  Notation " 'message "   := Message     (in custom pack_type at level 2).
  Notation " 'message "   := Message     (at level 2): package_scope.
  Notation " 'att "       := Signature (in custom pack_type at level 2).
  Notation " 'att "       := Signature (at level 2): package_scope.

  (**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
  *)
  Definition chSet t := chMap t 'unit.
  Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
  Notation " 'set t " := (chSet t) (at level 2): package_scope.

  Definition tt := Datatypes.tt.

  Definition pk_loc      : Location := (PubKey    ; 0%N).
  Definition sk_loc      : Location := (SecKey    ; 1%N).
  Definition message_loc : Location := (Message   ; 2%N).
  Definition sign_loc    : Location := ('set ('signature × 'message); 3%N).
  Definition state_loc   : Location := (State    ; 4%N).
  Definition chal_loc    : Location := (Challenge ; 5%N).
  Definition attest_loc  : Location := ('set ('att × 'challenge × 'state ) ; 6%N).

  Definition get_pk    : nat := 42. (* routine to get the public key *)
  Definition get_state : nat := 43. (* routine to get the state to be attested *)
  Definition sign      : nat := 44. (* routine to sign a message *)
  Definition verify_sig: nat := 45. (* routine to verify the signature *)
  Definition verify_att: nat := 46.

  Notation " 'attest "    := Attestation    (in custom pack_type at level 2).
  Definition attest    : nat := 47. (* routine to attest *)

  (*
TODO:
    Definition Attestation_locs := fset [:: pk_loc ; sk_loc; sign_loc ].


    Definition hash ((chal,st):'set ('challenge × 'state )) : 'set ('message) :=
      (chal,st).
  *)
(*
TODO remove below
 *)

  Equations hash {c s} (x: choice_type) (H: x = chMap (chProd (chFin c) (chFin s)) 'unit) : choice_type :=
    hash (chMap (chProd (chFin cPos) (chFin sPos)) _) eq_refl :=
      chMap
        (chFin
           (mkpos
              (pos cPos * pos sPos)
              (* (Positive_prod (cond_pos cPos) (cond_pos sPos)) *)
        ))
        'unit.

  Check hash_equation_1.
  Check FunctionalElimination_hash.

Fail  Equations hash' (x: choice_type) {H: x = 'set ('challenge × 'state)} : choice_type :=
    hash' (chMap (chProd (chFin cPos) (chFin sPos)) _) eq_refl :=
      chMap
        (chFin
           (mkpos
              (pos cPos * pos sPos)
              (* (Positive_prod (cond_pos cPos) (cond_pos sPos)) *)
        ))
        'unit.

  Lemma hash_spec: hash ('set ('challenge × 'state)) eq_refl = 'set ('message).
  Proof.
    rewrite /chSet/Challenge/State/Message.
    set x := chMap 'fin pos_n 'unit.
    elim/FunctionalElimination_hash: (hash (chMap ('fin pos_n × 'fin pos_n) 'unit) erefl) (* (hash _ _) *).
    move => c s.
    rewrite /x.
    f_equal.
    f_equal.
    (*
      This spec is just not true.
      I believe that the problem is in the data definition.
      It defines values instead of mathematical structure.
     *)
    Print Location.
    (*
      Note that the need for specifying a [choice_type]
      comes from the need to store it into a heap location.
      But the better way to achieve this, is to use a mathematical
      structure and then create the heap locations out of this.
      In the code, it is possible to just use the conversion
      functions [fto] and [otf] from SSProve.

      For example, in DDH we define
      [Definition chGroup : choice_type := 'fin #|GroupSpace|.]
      which comes directly from a mathematical structure:
      [Definition GroupSpace : finType := FinGroup.arg_finType gT.]
      and:
      [Parameter gT : finGroupType.]

      In RA, we do not have such a construction.
      We essentially define:
      [Definition Challenge : choice_type := chFin(mkpos pos_n).]
      with:
      [Definition pos_n: nat := 2^n.]
      That is: there is no mathematical structure.
      It is actually just a concrete value [2^n].

      Maybe here a small explanation, why locations want to
      be of type [choice_type]:
      because they define default values, i.e., the initial
      value of the heap location.
      See [choice_type.chCannonical].
      [choice_type] coerces to mathcomps [choiceType]
      https://math-comp.github.io/htmldoc/mathcomp.ssreflect.choice.html

      To cut a long story short:
      A message should not be of type [choice_type] but of the
      type of the mathematical structure, probably [I_n]
     *)
  Abort.

  (* MACCA approach. *)
  Context (mk_hash : 'state -> 'challenge -> 'message).
  (* But I cannot see how the result is possible when the space is not a group.
     That is because the heap locations in MACCA all have the same type or are subsets.
     They never have to convert one into the other.
   *)

  (* Check this out: *)
  Fail Definition f: 'set ('message) := chMap (chFin (mkpos 1)) chUnit.
  Check Choice.sort 'set ('message).
  (* So what are the inhabitants of this type?! *)
  Fail Definition f: 'set ('message) := chMap (chFin (mkpos pos_n)) chUnit.
  (* Nope. Check out the error message:
     [
Error:
The term "chMap 'fin pos_n 'unit" has type "choice_type" while it is expected to have type
 "Choice.sort 'set ('message)".
     ]
     That is, it cannot reduce [Choice.sort 'set ('message)] in the type!
     Remember [rew]?!
     Let's check out what [Choice.sort 'set ('message)] actually should reduce to:
   *)
  Print Choice.sort.
  Eval hnf in Choice.sort 'set ('message).
  Locate FMap.
  Check FMap.fmap_type.
  Eval hnf in (chElement_ordType 'message).
  Check Ordinal.
  Check is_true.
  Lemma two_lt_three : 2 < 3. by []. Defined.
  Compute Ordinal two_lt_three.
  Locate "<".
  Definition f: 'I_3 := Ordinal two_lt_three.

  Definition X: choice_type := (chFin (mkpos 3)).
  Definition g: X := Ordinal two_lt_three.

  Locate "\in".
  Check in_mem.
  Locate in_mem.
  Print Coq.ssr.ssrbool.

  (* We still need a group in order to perform any
     operation on two elements.
   *)
  

  Parameter Hash :
    	State -> Challenge ->
      Message.
(*
  Parameter Hash_refl :
    forall s1 c1 , Hash s1 c1 = Hash s1 c1.

  Parameter Hash_bij :
    forall s1 c1 s2 c2, s1 != s2 \/ c1 != c2  -> Hash s1 c1 != Hash s2 c2. *)

  (* The signature scheme requires a heap location to store the seen signatures. *)
  Definition Signature_locs_real := fset [:: pk_loc ; sk_loc].
  Definition Signature_locs_fake := Signature_locs_real :|: fset [:: sign_loc ].

  (* The remote attestation protocol does the same. *)
  Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
  Definition Attestation_locs_fake := Attestation_locs_real :|: fset [:: attest_loc ].

  (*
    The key challenge: relate [sign_loc] and [attest_loc].
   *)

  Definition Sign_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : 'message → 'signature ;
    #val #[verify_sig] : ('signature × 'message) → 'bool
  ].

  Definition Att_interface := [interface
  #val #[get_pk] : 'unit → 'pubkey ;
  #val #[attest] : 'challenge → 'signature ;
  #val #[verify_att] : ('challenge × 'signature) → 'bool
  ].

  Definition Sig_real : package Signature_locs_real [interface] Sign_interface
  := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    } ;

    #def #[sign] ( 'msg : 'message ) : 'signature
    {
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let sig := Sign sk msg in
      ret sig
    };

    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      pk ← get pk_loc  ;;
      let bool := Ver_sig pk sig msg in
      ret bool
    }
  ].

  Equations Sig_ideal : package Signature_locs_fake [interface] Sign_interface :=
  Sig_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };

    #def #[sign] ( 'msg : 'message ) : 'signature
    {
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let sig := Sign sk msg in
      S ← get sign_loc ;;
      #put sign_loc := setm S (sig, msg) tt ;;
      ret sig
    };

    #def #[verify_sig] ( '(sig,msg) : 'signature × 'message) : 'bool
    {
      S ← get sign_loc ;;
      ret ( (sig,msg) \in domm S)
    }
  ].
  Next Obligation.
    ssprove_valid; rewrite /Signature_locs_fake/Signature_locs_real in_fsetU; apply /orP.
    2,3,6: left;auto_in_fset.
    all: right; auto_in_fset.
  Defined.

  Definition Att_real : package Attestation_locs_real [interface] Att_interface
  := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc  ;;
      ret pk
    };

    #def #[attest] (chal : 'challenge) : 'signature
    {
      state ← get state_loc ;;
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let msg := Hash state chal in
      let att := Sign sk msg in
      ret att
    };

    #def #[verify_att] ('(chal, att) : ('challenge × 'signature)) : 'bool
    {
      pk ← get pk_loc ;;
      state ← get state_loc ;;
      let msg := Hash state chal in
      let bool := Ver_sig pk att msg in
      ret bool
    }
  ].

  Equations Att_ideal : package Attestation_locs_fake [interface] Att_interface :=
  Att_ideal := [package
    #def  #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    };

    #def #[attest] (chal : 'challenge) : 'attest
    {
      A ← get attest_loc ;;
      state ← get state_loc ;;
      let (sk,pk) := KeyGen in
      #put pk_loc := pk ;;
      #put sk_loc := sk ;;
      let att := Sign sk (chal, state) in
      #put attest_loc := setm A ( att, chal, state ) tt ;;
      ret att
    };

    #def #[verify_att] ('(chal, att) : ('challenge × 'attest)) : 'bool
    {
      A ← get attest_loc ;;
      state ← get state_loc ;;
      let b :=  (att, chal, state) \in domm A in
      ret b
    }
  ].
  Next Obligation.
    ssprove_valid; rewrite /Attestation_locs_fake/Attestation_locs_real in_fsetU; apply /orP.
    1,3,7: right;auto_in_fset.
    all: left; auto_in_fset.
  Defined.

  Definition Aux_locs := fset [:: sign_loc ; pk_loc ].

  Definition Aux :
  package Aux_locs
  Sign_interface
  Att_interface :=
  [package
    #def #[get_pk] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;
    #def #[attest] ( '(chal,state) : ('challenge × 'state )) : 'signature
    {
      #import {sig #[sign] : 'message  → 'signature } as sign ;;
      let msg := Hash state chal in
      att ← sign msg ;;
      ret att
    } ;
    #def #[verify_att] ('(chal, state, att) : ('challenge × 'state) × 'signature) : 'bool
    {
      #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
      let msg := Hash state chal in
      b  ← verify (att,msg) ;;
      ret b
      (* When I just write:
         [verify (att,msg)]
         Then SSProve errors out and cannot validate the package. Why?
       *)
    }
  ].

  Definition mkpair {Lt Lf E}
    (t: package Lt [interface] E) (f: package Lf [interface] E): loc_GamePair E :=
    fun b => if b then {locpackage t} else {locpackage f}.

  Definition Sig_unforg := @mkpair Signature_locs Signature_locs Sign_interface Sig_real Sig_ideal.
  Definition Att_unforg := @mkpair Attestation_locs Attestation_locs Att_interface Att_real Att_ideal.

(* Attestation_locs =o Aux_locs o Sig_locs
Definition Attestation_locs := fset [:: pk_loc ; sk_loc; attest_loc ].

Definition Signature_locs := fset [:: pk_loc ; sk_loc ; sign_loc ].
Definition Aux_locs' := fset [:: sign_loc ; pk_loc ; attest_loc ]. *)

  Lemma sig_real_vs_att_real_true:
    Att_unforg true ≈₀  Aux ∘ Sig_unforg true.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    - eapply rpost_weaken_rule.
      1: eapply rreflexivity_rule.
      move => [a1 h1] [a2 h2] [Heqa Heqh].
      intuition auto.
    - destruct x.
      ssprove_sync_eq.
      ssprove_sync_eq.
      by [apply r_ret].
    - case x => s s0.
      case s => s1 s2.
      ssprove_sync_eq.
      move => a.
      by [apply r_ret].
  Qed.

  Lemma sig_ideal_vs_att_ideal_false :
  Att_unforg false ≈₀ Aux ∘ Sig_unforg false.
  Proof.
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel x.
    all: ssprove_code_simpl.
    - ssprove_sync_eq => pk_loc.
      by [apply r_ret].
    - case x => challenge state.
      ssprove_swap_lhs 0.
      ssprove_sync_eq.
      ssprove_swap_lhs 0.
      ssprove_sync_eq.
      rewrite /attest_loc /sign_loc.
    Admitted.
  (*Qed.*)

  (* This is what the theorem is supposed to look like, but it doesn't compile! -> to be changed*)
  Theorem RA_unforg LA A :
  ∀ LA A,
    ValidPackage LA [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[sign] : ('challenge × 'state) → 'attest ;
    #val #[verify_sig] : ( ('challenge × 'state) × 'attest) → 'bool
    ] A_export A →
    fdisjoint LA (sig_real_vs_att_real_true).(locs) →
    fdisjoint LA (sig_ideal_vs_att_ideal_true).(locs) →
    Advantage Att_unforg <= Advantage Sig_unforg.
Proof.
  
