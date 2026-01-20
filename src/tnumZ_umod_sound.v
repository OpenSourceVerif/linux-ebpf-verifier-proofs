From Coq Require Import Bool List ZArith Lia.
From bpf.src Require Import Zmore tnumZ tnumZ_inv tnumZ_add_sound tnumZ_sub_sound tnumZ_shift_sound.
Import ListNotations.

Lemma Z_pow2_log2_gt_0 : forall x,
  2 ^ (Z.log2 x) > 0.
Proof.
  intros. apply Z.gt_lt_iff.
  apply Z.pow_pos_nonneg. lia. apply Z.log2_nonneg.
Qed.

Lemma Z_pow2_equiv : forall x, Z_is_pow2 x = true <-> Z_pow2 x.
Proof.
  unfold Z_is_pow2; unfold Z_pow2. split; intros.
  - apply andb_prop in H; destruct H.
    apply Z.ltb_lt in H; apply Z.eqb_eq in H0. split. apply H.
    destruct (Z.eqb_spec x (2 ^ (Z.log2 x))).
    + exists (Z.log2 x). split; apply Z.log2_nonneg + lia.
    + exfalso.
      apply Z.bits_inj_iff in H0; unfold Z.eqf in H0. specialize (H0 (Z.log2 x)).
      rewrite Z.land_spec in H0. rewrite Z.bits_0 in H0.
      assert (Hbit1: Z.testbit x (Z.log2 x) = true) by apply (Z.bit_log2 _ H).
      assert (Hbit2: Z.testbit (x - 1) (Z.log2 x) = true).
      { rewrite Z.testbit_odd. rewrite (Z.shiftr_div_pow2 _ _ (Z.log2_nonneg x)).
        pose proof (Z.log2_spec x H). destruct H1.
        set (p := 2 ^ Z.log2 x).
        assert (Hge1: 1 <= (x - 1) / p).
        { assert (p <= x - 1) by lia.
          apply (Z_div_le _ _ p (Z_pow2_log2_gt_0 x)) in H3.
          rewrite (Z_div_same p (Z_pow2_log2_gt_0 x)) in H3. apply H3. }
        assert ((x - 1) / p >= 2 \/ (x - 1) / p < 2) by lia.
        destruct H3 as [Hcontra | Hlt2].
        { rewrite (Z.pow_succ_r _ _ (Z.log2_nonneg x)) in H2.
          apply (Zmult_ge_compat_l _ _ p) in Hcontra; try lia. }
        assert ((x - 1) / p = 1) by lia.
        rewrite H3. reflexivity. }
      rewrite Hbit1, Hbit2 in H0. lia.
  - destruct H as [H [x0 [H0 H1]]]. apply andb_true_iff. split; try lia.
    apply Z.eqb_eq. rewrite <- H1. rewrite Z.sub_1_r; rewrite <- Z.ones_equiv.
    rewrite Z.land_ones. apply Z_mod_same_full.
    rewrite <- H1 in H. destruct x0; try lia.
Qed.

Lemma or_m_same_and_eq: forall x,
  Z.lor x (- x) = - Z.land x (- x).
Proof.
  intros.
  rewrite <- Z.add_move_0_l.
  rewrite Z.add_comm.
  rewrite Z.add_lor_land.
  lia.
Qed.

Lemma Z_lsb_is_pow2 : forall x, 0 < x -> Z_pow2 (Z.land x (-x)).
Proof.
  intros. rewrite <- Z_pow2_equiv. unfold Z_is_pow2.
  apply andb_true_iff. split.
  - apply Z.ltb_lt.
    replace 0 with (-x + x).
    2:{ lia. }
    rewrite Z.add_comm.
    rewrite <- Z.add_lor_land.
    assert (Heq: Z.lor x (- x) < 0).
    2:{ lia. }
    rewrite Z.lor_neg.
    lia.
  - apply Z.eqb_eq. apply Z.bits_inj; unfold Z.eqf; intros.
    assert (N : n < 0 \/ n >= 0) by lia.
    destruct N.
    + destruct n; try lia; simpl.
      reflexivity.
    + rewrite !Z.land_spec.
      rewrite Z.testbit_0_l.
      destruct (Z.testbit x n) eqn: Hn; try lia.
      rewrite andb_true_l.
      rewrite andb_false_iff.
      right.
      assert (Heq: Z.land x (- x) =
      - (- (Z.land x (- x)))). {
        rewrite Z.opp_involutive.
        lia.
      }
      rewrite Heq; clear Heq.
      rewrite <- Z.lnot_eq_pred_opp.
      rewrite ! Z.lnot_spec; try lia.
      rewrite negb_false_iff.

      rewrite <- or_m_same_and_eq.
      rewrite !Z.lor_spec; try lia.
      rewrite Hn.
      lia.
Qed.

Lemma Z_lsb_range : forall x k,
  0 < x <= 2 ^ k - 1 -> 0 < Z.land x (-x) <= 2 ^ k - 1.
Proof.
  intros x k Hx.
  destruct Hx as [Hxlow Hxhigh].
  assert (Hpow2 : Z_pow2 (Z.land x (- x))) by (apply Z_lsb_is_pow2; apply Hxlow).
  destruct Hpow2 as [Hgt0 [k0 [Hge0 Heq]]].
  split.
  - rewrite <- Heq. apply Z.pow_pos_nonneg; lia.
  - apply (Z.le_trans _ x).
    + apply Z_land_leb. lia.
    + apply Hxhigh.
Qed.

Lemma Z_testbit_neg_1 : forall n,
  0 <= n -> Z.testbit (-1) n = true.
Proof.
  intros. destruct n.
  - reflexivity.
  - simpl. reflexivity.
  - pose proof Pos2Z.neg_is_neg. lia.
Qed.

Lemma Z_ldiff_land_ones : forall x y k,
  Z.ldiff (Z.land x (Z.ones k)) (Z.land y (Z.ones k)) = Z.land (Z.ldiff x y) (Z.ones k).
Proof.
  intros. apply Z.bits_inj. unfold Z.eqf. intros.
  rewrite Z.ldiff_spec. rewrite! Z.land_spec.
  rewrite Z.ldiff_spec. rewrite negb_andb.
  assert (n < 0 \/ k < 0 <= n \/ 0 <= k <= n \/ 0 <= n < k) by lia.
  destruct H as [H | [[H H0] | [H | H]]].
  - destruct n; try lia. reflexivity.
  - destruct k; try discriminate. rewrite Z.ones_equiv; simpl.
    rewrite (Z_testbit_neg_1 _ H0); simpl.
    rewrite orb_false_r. rewrite! andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high _ _ H). lia.
  - rewrite (Z.ones_spec_low _ _ H).
    rewrite orb_false_r. rewrite! andb_true_r. reflexivity.
Qed.

Lemma Z_land_neg_1 : forall x, Z.land (-1) x = x.
Proof.
  intros. apply Z.bits_inj. unfold Z.eqf. intros.
  rewrite Z.land_spec. assert (n < 0 \/ 0 <= n) by lia.
  destruct H.
  - destruct n; try lia. reflexivity.
  - rewrite (Z_testbit_neg_1 _ H). apply andb_true_l.
Qed.

Lemma Z_pow_nonneg_rev : forall a b,
  0 < Z.pow a b -> 0 <= b.
Proof.
  intros. destruct b as [| b' | b'].
  - reflexivity.
  - apply Pos2Z.is_nonneg.
  - discriminate.
Qed.

Lemma Z_size_Z_upper_bound: forall x, 
  0 <= x -> x <= Z.ones (Z_size_Z x).
Proof.
  intros. unfold Z_size_Z. destruct x; try lia.
  - rewrite Z.ones_equiv. lia.
  - rewrite Z.ones_equiv. apply Z.lt_le_pred.
    rewrite (Z.abs_eq _ (Pos2Z.is_nonneg p)). rewrite Z.add_1_r.
    apply (Z.log2_spec _ (Pos2Z.is_pos p)).
Qed.

Lemma mod_upper_bound: forall a b i j
  (Ha_inv: tnum_ge_inv a)
  (Hb_inv: tnum_ge_inv b)
  (Hga: gamma a i)
  (Hgb: gamma b j),
  0 < j -> Z.modulo i j <= Z.ones (Z_size_Z (Z.min (fst a + snd a) (fst b + snd b))).
Proof.
  intros.
  pose proof (tnum_ge_inv_gamma_bound _ _ Hgb Hb_inv).
  destruct (Z.leb_spec j (fst a + snd a)).
  - assert (Z.modulo i j < j) by apply (Z.mod_pos_bound _ _ H).
    assert (0 <= Z.min (fst a + snd a) (fst b + snd b)) by lia.
    pose proof (Z_size_Z_upper_bound (Z.min (fst a + snd a) (fst b + snd b)) H3). lia.
  - pose proof (tnum_ge_inv_gamma _ _ Hga Ha_inv).
    pose proof (tnum_ge_inv_gamma_bound _ _ Hga Ha_inv).
    destruct (Z.eqb_spec i 0).
    { subst i. pose proof (Z_size_Z_nonneg (Z.min (fst a + snd a) (fst b + snd b))).
      rewrite Z.mod_0_l; try lia. rewrite Z.ones_equiv. lia. }
    assert (0 <= i < j) by lia. rewrite (Z.mod_small _ _ H4).
    assert (0 <= Z.min (fst a + snd a) (fst b + snd b)) by lia.
    pose proof (Z_size_Z_upper_bound (Z.min (fst a + snd a) (fst b + snd b)) H5). lia.
Qed.

Lemma mod_ldiff_ones_0: forall a b i j
  (Ha_inv: tnum_ge_inv a)
  (Hb_inv: tnum_ge_inv b)
  (Hga: gamma a i)
  (Hgb: gamma b j),
  0 < j -> Z.ldiff (Z.modulo i j) (Z.ones (Z_size_Z (Z.min (fst a + snd a) (fst b + snd b)))) = 0.
Proof.
  intros. apply (Z_ldiff_ones _ _ (Z_size_Z_nonneg _)). split.
  - apply Z_mod_nonneg_nonneg; try lia. apply (tnum_ge_inv_gamma _ _ Hga Ha_inv).
  - apply (mod_upper_bound _ _ _ _ Ha_inv Hb_inv Hga Hgb H).
Qed.

Lemma Z_testbit_lt_lsb: forall x n,
  0 <= n ->
  Z.testbit ((Z.land x (-x)) - 1) n = true -> Z.testbit x n = false.
Proof.
  intros.
  assert (Heq: x + - x = Z.land x (- x) + Z.lor x (- x)). {
    rewrite Z.add_comm with (n := Z.land x (- x)).
    rewrite Z.add_lor_land.
    lia.
  }
  assert (Heq1: Z.lor x (- x)  = - (Z.land x (- x) - 1) - 1). {
    rewrite or_m_same_and_eq.
    lia.
  }
  assert (Heq2: Z.testbit (Z.lor x (- x)) n = false). {
    rewrite Heq1.
    assert (Hp: - (Z.land x (- x) - 1) - 1 = Z.pred (- (Z.land x (- x) - 1))). {
      unfold Z.pred.
      lia.
    }
    rewrite Hp; clear Hp.
    rewrite <- negb_true_iff.
    rewrite <- Z.bits_opp; try lia.
    rewrite Z.opp_involutive.
    assumption.
  }
  rewrite Z.lor_spec in Heq2.
  rewrite orb_false_iff in Heq2.
  destruct Heq2 as (Heq2 & Heq3).
  assumption.
Qed.

Lemma tnum_umod_sound : forall a b i j
  (Ha_inv: tnum_ge_inv a)
  (Hb_inv: tnum_ge_inv b)
  (Hga: gamma a i)
  (Hgb: gamma b j),
    gamma (tnum_umod a b) (Z.modulo i j).
Proof.
  intros. unfold tnum_umod.
  destruct (Z.eqb_spec (fst b) 0) as [Hb_v0|Hb_v0].
  (* Case 1: divisor can by 0 *)
  { destruct (Z.eqb_spec (snd b) 0) as [Hb_m0|Hb_m0]; simpl.
    - destruct b; simpl in *; subst.
      apply gamma_0 in Hgb. rewrite Hgb.
      rewrite Zmod_0_r. apply Hga.
    - rewrite andb_false_r. unfold gamma. simpl. apply Z.land_0_r. }
  destruct (andb (snd a =? 0) (snd b =? 0)) eqn:H_m0.
  (* Case 2: concrete umod *)
  { apply andb_prop in H_m0; destruct H_m0 as [Ha_m0 Hb_m0].
    apply Z.eqb_eq in Ha_m0, Hb_m0. unfold gamma in *; simpl.
    rewrite Ha_m0, Z.lnot_0, Z.land_m1_r in Hga.
    rewrite Hb_m0, Z.lnot_0, Z.land_m1_r in Hgb.
    rewrite Hga, Hgb, Z.lnot_0. apply Z.land_m1_r. }
  destruct (andb (snd b =? 0) (Z_is_pow2 (fst b))) eqn:Hp.
  (* Case 3: divisor is pow of 2 *)
  { apply andb_prop in Hp; destruct Hp as [Hp1 Hp2]; apply Z.eqb_eq in Hp1.
    apply (gamma_const_uniq _ _ Hp1) in Hgb; rewrite <- Hgb in *.
    pose proof (tnum_ge_inv_gamma _ _ Hga Ha_inv).
    apply Z_pow2_equiv in Hp2. destruct Hp2 as [H1 [x [H2 H3]]]. rewrite <- H3.
    rewrite <- H3 in H1. assert (0 <= x) by apply (Z_pow_nonneg_rev _ _ H1).
    rewrite <- Z.land_ones; try lia.
    unfold gamma in *. simpl. rewrite Z.sub_1_r; rewrite <- Z.ones_equiv.
    rewrite <- Hga. rewrite <- !Z.ldiff_land. apply Z_ldiff_land_ones. }
  assert (0 < j) by apply (tnum_gt_inv_gamma _ _ Hgb Hb_inv Hb_v0).
  unfold gamma; simpl. unfold mod_get_low_bits.
  destruct (Z.odd (fst b) || Z.odd (snd b)).
  (* Case 4.1: mod_get_low_bits return default (0, 1) *)
  { unfold snd at 1. rewrite Z_land_neg_1. simpl.
    rewrite <- Z.ldiff_land. apply (mod_ldiff_ones_0 _ _ _ _ Ha_inv Hb_inv Hga Hgb H). }
  (* Case 4.2: mod_get_low_bits return general value *)
  set (mask := Z.ones (Z_size_Z (Z.min (fst a + snd a) (fst b + snd b)))).
  set (mask0 := Z.land (fst b + snd b) (- (fst b + snd b)) - 1).
  unfold snd at 1. unfold fst at 1. rewrite Z.lnot_land. rewrite Z.land_lor_distr_r.
  rewrite Z.lnot_lor; rewrite Z.lnot_lnot.
  rewrite Z.lnot_land; rewrite Z.land_lor_distr_l.
  rewrite (Z.land_comm (Z.lnot mask0)). rewrite Z.land_lnot_diag; rewrite Z.lor_0_r.
  assert (Hmod_ldiff_ones: Z.land (Z.modulo i j) (Z.lnot mask) = 0).
  { rewrite <- Z.ldiff_land. apply (mod_ldiff_ones_0 _ _ _ _ Ha_inv Hb_inv Hga Hgb H). }
  rewrite Hmod_ldiff_ones; rewrite Z.lor_0_r.
  rewrite (Z_lor_recompose (Z.land (Z.modulo i j) (Z.land (Z.lnot (snd a)) mask0)) mask).
  rewrite (Z.land_comm (Z.modulo i j)); rewrite <- (Z.land_assoc (Z.lnot (snd a))).
  rewrite (Z.land_assoc (Z.lnot (snd a))); rewrite <- (Z.land_assoc _ (Z.modulo i j)).
  rewrite Hmod_ldiff_ones; rewrite Z.land_0_r; rewrite Z.lor_0_l.
  rewrite <- (Z.land_assoc _ mask0); rewrite (Z.land_comm mask0).
  assert (Z.land (Z.modulo i j) mask0 = Z.land i mask0).
  { assert (Hlow: Z.land j mask0 = 0).
    { apply Z.bits_inj; unfold Z.eqf; intros. rewrite Z.land_spec. rewrite Z.bits_0.
      assert (Hn: n < 0 \/ 0 <= n) by lia. destruct Hn.
      { destruct n; try lia. reflexivity. }
      destruct (Z.testbit mask0 n) eqn:Hmask0 ; try lia.
      apply andb_false_iff. left. subst mask0. apply Z_testbit_lt_lsb in Hmask0; try lia.
      rewrite (gamma_add_lor _ _ Hgb) in Hmask0. rewrite Z.lor_spec in Hmask0.
      rewrite orb_false_iff in Hmask0. destruct Hmask0.
      rewrite <- (gamma_testbit_mask_false_Z (fst b) (snd b) j n Hgb H2 H0). apply H1. }
    assert (Hmask_ones: exists n, 0 <= n /\ mask0 = Z.ones n).
    { pose proof (Z_lsb_is_pow2 (fst b + snd b)). unfold Z_pow2 in H0.
      destruct H0. unfold tnum_ge_inv in Hb_inv. lia.
      destruct H1 as [x [H1 H2]]. rewrite <- H2 in H0.
      subst mask0. rewrite <- H2. exists x. split.
      apply (Z_pow_nonneg_rev _ _ H0). rewrite Z.ones_equiv. reflexivity. }
    destruct Hmask_ones as [n [Hnge0 Hmask_ones]]. rewrite Hmask_ones.
    rewrite Hmask_ones in Hlow. rewrite (Z.land_ones _ _ Hnge0) in Hlow.
    apply Znumtheory.Zmod_divide in Hlow; try lia.
    rewrite !Z.land_ones; try lia.
    rewrite <- (Znumtheory.Zmod_div_mod (2 ^ n) j); try lia. apply Hlow. }
  rewrite H0. rewrite Z.land_assoc. rewrite (Z.land_comm _ i).
  unfold gamma in Hga. rewrite Hga. reflexivity.
Qed.

