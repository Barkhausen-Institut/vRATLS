Module HeapHashAltAlgo.

  Module Type RemoteAttestationParams <: SignatureConstraints.

    Definition chState : choice_type := 'fin (mkpos pos_n).
    Definition chChallenge : choice_type := 'fin (mkpos pos_n).
    Definition Attestation : choice_type := 'fin (mkpos pos_n).

    Definition chMessage := 'fin (mkpos pos_n).

  End RemoteAttestationParams.

  Module Type RemoteAttestationAlgorithms
    (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2).
    Import π1.
    Import π2.
    Import π3.

    Local Open Scope package_scope.

    Notation " 'state "     := chState       (in custom pack_type at level 2).
    Notation " 'state "     := chState       (at level 2): package_scope.
    Notation " 'challenge " := chChallenge   (in custom pack_type at level 2).
    Notation " 'challenge " := chChallenge   (at level 2): package_scope.

    Definition state_loc   : Location := ('state    ; 4%N).
    Definition attest_loc  : Location := ('set (Signature × chMessage) ; 2%N).

    Definition verify_att: nat := 46.

    Notation " 'attest "    := Attestation    (in custom pack_type at level 2).
    Definition attest    : nat := 47. (* routine to attest *)

    Parameter Hash : chState -> chChallenge -> chMessage.
    Parameter UnHash : chChallenge -> chMessage -> chState.

  End RemoteAttestationAlgorithms.

  Module RemoteAttestation
    (π1 : SignatureParams)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2)
    (π4 : RemoteAttestationAlgorithms π1 π2 π3)
    (π5 : SignatureScheme π1 π2 π3).

    Import π1 π2 π3 π4 π5.


    (* The remote attestation protocol does the same as the signature scheme, i.e.,
       it stores the attestations handed out.
     *)
    Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
    Definition Attestation_locs_fake := Attestation_locs_real :|: fset [:: attest_loc ].

    Definition Att_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[attest] : 'challenge → 'signature ;
    #val #[verify_att] : ('challenge × 'signature) → 'bool
    ].

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
        s ← get state_loc ;;
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash s chal in
        let att := Sign sk msg in
        #put attest_loc := setm A ( att, msg ) tt ;;
        ret att
      };

      #def #[verify_att] ('(chal, att) : ('challenge × 'attest)) : 'bool
      {
        A ← get attest_loc ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        if (att, msg) \in domm A then ret (state == UnHash att chal) else ret false
      }
    ].
    Next Obligation.
      ssprove_valid; rewrite /Attestation_locs_fake/Attestation_locs_real in_fsetU; apply /orP.
      1,3,7: right;auto_in_fset.
      all: left; auto_in_fset.
    Defined.

    (* We need a common interface, so we need to define an [AUX] for the
       signature scheme.
     *)
    Definition Aux_locs := fset [:: pk_loc ; state_loc ].

    Definition Aux : package Aux_locs Sign_interface Att_interface :=
    [package
      #def #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };

      #def #[attest] ( chal : 'challenge ) : 'signature
      {
        #import {sig #[sign] : 'message  → 'signature } as sign ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        att ← sign msg ;;
        ret att
      };

      #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
      {
        #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        b  ← verify (att,msg) ;;
        if b then ret (state == UnHash att chal) else ret false
        (* When I just write:
           [verify (att,msg)]
           Then SSProve errors out and cannot validate the package. Why?
         *)
      }
    ].

    Definition mkpair {Lt Lf E}
      (t: package Lt [interface] E) (f: package Lf [interface] E): loc_GamePair E :=
      fun b => if b then {locpackage t} else {locpackage f}.

    Definition Sig_unforg := @mkpair Signature_locs_real Signature_locs_fake Sign_interface Sig_real Sig_ideal.
    Definition Att_unforg := @mkpair Attestation_locs_real Attestation_locs_fake Att_interface Att_real Att_ideal.

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
        ssprove_sync_eq => state.
        do 2! ssprove_sync_eq.
        by [apply r_ret].
      - case x => s s0.
        case s => s1 s2.
        ssprove_swap_lhs 0.
        ssprove_sync_eq => state.
        ssprove_sync_eq => pk.
        case: (Ver_sig pk s0 (Hash state (Ordinal (n:={| pos := {| pos := pos_n; cond_pos := PositiveExp2 n |}; cond_pos := PositiveExp2 n |}) (m:=s1) s2))).
        2: by [apply r_ret].
        (* here I need a property that connects Hash and UnHash. *)
    Qed.

    (* TODO If we define the spec right then this proof needs fixing! *)
    Lemma sig_ideal_vs_att_ideal_false :
      Att_unforg false ≈₀ Aux ∘ Sig_unforg false.
    Proof.
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel x.
      all: ssprove_code_simpl.
      - ssprove_sync_eq => pk_loc.
        by [apply r_ret].
      - ssprove_swap_lhs 0; ssprove_sync_eq => state.
        do 2! (ssprove_swap_lhs 0; ssprove_sync_eq).
        ssprove_sync_eq => sig.
        ssprove_sync_eq.
        by [apply r_ret].
      - case x => a b.
        ssprove_swap_lhs 0; ssprove_sync_eq => state.
        ssprove_sync_eq => sig.
        by [apply r_ret].
    Qed.

    (* TODO If we define the spec right then this proof needs fixing! *)
    Theorem RA_unforg LA A :
        ValidPackage LA Att_interface A_export A →
        fdisjoint LA (Sig_unforg true).(locs) →
        fdisjoint LA (Sig_unforg false).(locs) →
        fdisjoint LA Aux_locs →
        fdisjoint LA (Att_unforg true).(locs) →
        fdisjoint LA (Att_unforg false).(locs) →
        (Advantage Att_unforg A <= AdvantageE Sig_ideal Sig_real (A ∘ Aux))%R.
    Proof.
      move => va H1 H2 H3 H4 H5.
      rewrite Advantage_E Advantage_sym.
      simpl in H1.
      simpl in H2.
      simpl in H3.
      simpl in H4.
      simpl in H5.
      ssprove triangle (Att_unforg true) [::
        Aux ∘ Sig_unforg true ;
        Aux ∘ Sig_unforg false
        ] (Att_unforg false) A as ineq.
      eapply le_trans.
      1: { exact: ineq. }
      clear ineq.
      rewrite sig_real_vs_att_real_true.
      2: simpl; exact: H4.
      2: {
        simpl.
        rewrite fdisjointUr.
        apply/andP; split; assumption.
      }
      rewrite GRing.add0r.
      rewrite [X in (_ + X <= _)%R]Advantage_sym.
      rewrite sig_ideal_vs_att_ideal_false.
      2: { simpl; exact: H5. }
      2: { rewrite fdisjointUr; apply/andP; split; assumption. }
      rewrite GRing.addr0.
      by [rewrite -Advantage_link Advantage_sym].
    Qed.

  End RemoteAttestation.
End HeapHashAltAlgo.

Module NoHeapHash.

  Module Type RemoteAttestationParams <: SignatureConstraints.

    Definition chState : choice_type := 'fin (mkpos pos_n).
    Definition chChallenge : choice_type := 'fin (mkpos pos_n).
    Definition Attestation : choice_type := 'fin (mkpos pos_n).

    Definition chMessage := 'fin (mkpos pos_n).

  End RemoteAttestationParams.

  Module Type RemoteAttestationAlgorithms
    (π1 : SignatureParams) (* TBD This is strange. The reason is because our code depends on signature scheme functions. *)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2).
    Import π1.
    Import π2.
    Import π3.

    Local Open Scope package_scope.

    Notation " 'state "     := chState       (in custom pack_type at level 2).
    Notation " 'state "     := chState       (at level 2): package_scope.
    Notation " 'challenge " := chChallenge   (in custom pack_type at level 2).
    Notation " 'challenge " := chChallenge   (at level 2): package_scope.

    Definition state_loc   : Location := ('state    ; 4%N).
    Definition attest_loc  : Location := ('set (Signature × ('challenge × 'state)) ; 5%N).

    Definition verify_att: nat := 46.

    Notation " 'attest "    := Attestation    (in custom pack_type at level 2).
    Definition attest    : nat := 47. (* routine to attest *)

    (*
      FIXME this hash function spec is insufficient.
      It allows to discard one of the arguments and just return the other as message!
     *)
    Parameter Hash : chState -> chChallenge -> chMessage.

  (*
    Parameter Hash_refl :
      forall s1 c1 , Hash s1 c1 = Hash s1 c1.

    Parameter Hash_bij :
      forall s1 c1 s2 c2, s1 != s2 \/ c1 != c2  -> Hash s1 c1 != Hash s2 c2. *)

    Parameter Hash_spec:
      forall state challenge sk msg sig (A: 'set (Signature × ('challenge × 'state))) (B: 'set (Signature × chMessage)),
        msg = Hash state challenge ->
        sig = Sign sk msg ->
        ((sig,(challenge,state)) \in domm A) = ((sig, msg) \in domm B).

    (*
      I cannot define such an equality for writing to a heap location.
      I need an invariant on these two dedicated heap locations that allows
      them to be unequal.
      Or even better that establishes an invariant that is based on
      the above spec!

      For that I need to generalize the spec a bit such that I do not need
      the secret key [sk]:
     *)

    Parameter Hash_spec':
      forall state challenge msg sig (A: 'set (Signature × ('challenge × 'state))) (B: 'set (Signature × chMessage)),
        msg = Hash state challenge ->
        ((sig,(challenge,state)) \in domm A) = ((sig, msg) \in domm B).

    (* Note that I could actually get the [sk] from the heap locations
       as well but that makes the invariant more evolved.
     *)

    (*
      Check out what actually happened now:
      In order to prove this property, I will have to prove that
      the [Hash] function is bijective!
      That is exactly what we assumed. The above lemmas just show how to use
      this property in the proof.
     *)

  End RemoteAttestationAlgorithmsNoHeapSig.


  Module RemoteAttestationNoHeapSig
    (π1 : SignatureParams)
    (π2 : RemoteAttestationParams)
    (π3 : SignatureAlgorithms π1 π2)
    (π4 : RemoteAttestationAlgorithmsNoHeapSig π1 π2 π3)
    (π5 : SignatureScheme π1 π2 π3).

    Import π1 π2 π3 π4 π5.


    (* The remote attestation protocol does the same as the signature scheme, i.e.,
       it stores the attestations handed out.
     *)
    Definition Attestation_locs_real := fset [:: pk_loc ; sk_loc; state_loc ].
    Definition Attestation_locs_fake := Attestation_locs_real :|: fset [:: attest_loc ].

    Definition Att_interface := [interface
    #val #[get_pk] : 'unit → 'pubkey ;
    #val #[attest] : 'challenge → 'signature ;
    #val #[verify_att] : ('challenge × 'signature) → 'bool
    ].

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
        s ← get state_loc ;;
        let (sk,pk) := KeyGen in
        #put pk_loc := pk ;;
        #put sk_loc := sk ;;
        let msg := Hash chal s in
        let att := Sign sk msg in
        #put attest_loc := setm A ( att, chal, s ) tt ;;
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

    (*
      TODO:
      Currently, these descriptions do not facilitate an actual protocol.
      A protocol really is where I call [attest] and [verify_att] in one single piece of code.
      The thing that happens then is that there need to be two locations for the state:
      one in the client and the other in the server.
     *)

    (* We need a common interface, so we need to define an [AUX] for the
       signature scheme.
     *)
    Definition Aux_locs := fset [:: pk_loc ; state_loc ].

    Definition Aux : package Aux_locs Sign_interface Att_interface :=
    [package
      #def #[get_pk] (_ : 'unit) : 'pubkey
      {
        pk ← get pk_loc ;;
        ret pk
      };
  
      #def #[attest] ( chal : 'challenge ) : 'signature
      {
        #import {sig #[sign] : 'message  → 'signature } as sign ;;
        state ← get state_loc ;;
        let msg := Hash state chal in
        att ← sign msg ;;
        ret att
      };
  
      #def #[verify_att] ('(chal, att) : 'challenge × 'signature) : 'bool
      {
        #import {sig #[verify_sig] : ('signature × 'message) → 'bool } as verify ;;
        state ← get state_loc ;;
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
  
    Definition Sig_unforg := @mkpair Signature_locs_real Signature_locs_fake Sign_interface Sig_real Sig_ideal.
    Definition Att_unforg := @mkpair Attestation_locs_real Attestation_locs_fake Att_interface Att_real Att_ideal.
  
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
        ssprove_sync_eq => state.
        do 2! ssprove_sync_eq.
        by [apply r_ret].
      - case x => s s0.
        case s => s1 s2.
        ssprove_swap_lhs 0.
        ssprove_sync_eq => state.
        ssprove_sync_eq => pk.
        by [apply r_ret].
    Qed.
  
    (*
      Another invariant over the heaps:
      [f(h__attest) = h__sign]
      with
      [
        Definition f (h) : h :=
        match h__loc with
        | attest_loc (chal, state) att => hash (chal,state)
        | _ => id
      ]
     *)
  
    Lemma sig_ideal_vs_att_ideal_false :
    Att_unforg false ≈₀ Aux ∘ Sig_unforg false.
    Proof.
      eapply eq_rel_perf_ind_eq.
      simplify_eq_rel x.
      all: ssprove_code_simpl.
      - ssprove_sync_eq => pk_loc.
        by [apply r_ret].
      - rewrite /Att_ideal.
        case x => challenge state.
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
    
  End RemoteAttestationNoHeapSig.