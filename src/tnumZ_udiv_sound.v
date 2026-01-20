From Coq Require Import List ZArith Bool Lia.
From bpf.src Require Import Zmore tnumZ tnumZ_inv tnumZ_add_sound tnumZ_sub_sound tnumZ_shift_sound.
Import ListNotations.

Lemma tnum_udiv_sound : forall a b i j
  (Ha_inv: tnum_ge_inv a)
  (Hb_inv: tnum_ge_inv b)
  (Hga: gamma a i)
  (Hgb: gamma b j),
    gamma (tnum_udiv a b) (Z.div i j).
Proof.
  intros. unfold tnum_udiv.
  destruct (Z.eqb_spec (fst b) 0) as [Hb_v0|Hb_v0].
  (* Case 1: divisor can by 0 *)
  { destruct (Z.eqb_spec (snd b) 0) as [Hb_m0|Hb_m0]; simpl.
    - destruct b; simpl in *; subst.
      apply gamma_0 in Hgb. rewrite Hgb.
      rewrite Zdiv_0_r. reflexivity.
    - rewrite andb_false_r. unfold gamma. simpl. apply Z.land_0_r. }
  destruct (andb (snd a =? 0) (snd b =? 0)) eqn:H_m0.
  (* Case 2: concrete udiv *)
  { apply andb_prop in H_m0; destruct H_m0 as [Ha_m0 Hb_m0].
    apply Z.eqb_eq in Ha_m0, Hb_m0. unfold gamma in *; simpl.
    rewrite Ha_m0, Z.lnot_0, Z.land_m1_r in Hga.
    rewrite Hb_m0, Z.lnot_0, Z.land_m1_r in Hgb.
    rewrite Hga, Hgb, Z.lnot_0. apply Z.land_m1_r. }
  (* Case 3: general case *)
  destruct (Z.eqb_spec (Z.div (fst a + snd a) (fst b)) 0) as [Hres_0|Hres_0].
  + unfold gamma; simpl. rewrite Hres_0; rewrite Z.ones_equiv; simpl.
    rewrite Z.lnot_0, Z.land_m1_r. apply Z.div_small.
    apply (Z.div_small_iff _ _ Hb_v0) in Hres_0.
    pose proof (tnum_ge_inv_gamma_bound a i Hga Ha_inv).
    pose proof (tnum_ge_inv_gamma_bound b j Hgb Hb_inv).
    unfold tnum_ge_inv in Ha_inv, Hb_inv. lia.
  + unfold gamma; simpl. rewrite <- Z.ldiff_land. unfold Z_size_Z. apply Z_ldiff_ones.
    { pose proof (Z.log2_nonneg (Z.abs (Z.div (fst a + snd a) (fst b)))).
      destruct (Z.div (fst a + snd a) (fst b)); try lia. }
    pose proof (tnum_ge_inv_gamma a i Hga Ha_inv);
    pose proof (tnum_gt_inv_gamma b j Hgb Hb_inv Hb_v0). split.
    { apply (Z.div_pos _ _ H H0). }
    assert (Z.div i j <= Z.div (fst a + snd a) (fst b)).
    { assert (Z.div i j <= Z.div (fst a + snd a) j).
      { destruct (Z.eqb_spec j 0) as [Hj_0 | Hj_0].
        - rewrite Hj_0. lia.
        - apply Z.div_le_mono. lia. apply (tnum_ge_inv_gamma_bound a i Hga Ha_inv). }
      assert (Z.div (fst a + snd a) j <= Z.div (fst a + snd a) (fst b)).
      { apply Z.div_le_compat_l.
        - apply Z.add_nonneg_nonneg. apply Ha_inv. apply Ha_inv.
        - split. unfold tnum_ge_inv in Hb_inv. lia.
          apply (tnum_ge_inv_gamma_bound b j Hgb Hb_inv). }
      apply (Z.le_trans _ _ _ H1 H2). }
    assert (forall x, 0 < x -> x <= Z.ones (Z.log2 (Z.abs x) + 1)).
    { intros. assert (log_spec := Z.log2_spec x H2).
      destruct log_spec as [_ upper_bound].
      unfold Z.ones. apply Z.lt_le_pred. rewrite Z.shiftl_1_l. 
      rewrite Z.abs_eq. apply upper_bound. lia. }
    assert (0 < Z.div (fst a + snd a) (fst b)).
    {  unfold tnum_ge_inv in *.
      assert (0 <= fst a + snd a) by lia; assert (0 < fst b) by lia.
      assert (res_ge_0 := Z.div_pos _ _ H3 H4). lia. }
    destruct (Z.div (fst a + snd a) (fst b));
    try contradiction; try apply (Z.le_trans _ _ _ H1 (H2 _ H3)).
Qed.