From Coq Require Import ZArith Lia.
From bpf.src Require Import Zmore tnumZ.

Definition tnum_ge_inv (a: tnum): Prop :=
  0 <= fst a /\ 0 <= snd a.
  
Lemma tnum_ge_inv_gamma: forall a i,
  gamma a i ->
  tnum_ge_inv a ->
    0 <= i.
Proof.
  unfold gamma, tnum_ge_inv; simpl; intros.
  destruct a as (av, am); simpl in *; subst.
  destruct H0 as (Hv & Hm).
  rewrite Z.land_nonneg in Hv.
  destruct Hv as [Hv | Hv]; auto.
  rewrite Z.lnot_nonneg in Hv.
  lia.
Qed.

Lemma tnum_gt_inv_gamma: forall a i,
  gamma a i -> tnum_ge_inv a -> (fst a) <> 0 -> 0 < i.
Proof.
  intros. pose proof (tnum_ge_inv_gamma _ _ H H0).
  destruct i; try lia.
  unfold gamma in H. rewrite <- H in H1. rewrite Z.land_0_l in H1. lia.
Qed.

Lemma tnum_ge_inv_gamma_bound a i :
  gamma a i -> tnum_ge_inv a -> fst a <= i <= fst a + snd a.
Proof.
  intros Hgamma Hinv.
  assert (0 <= i) by (apply (tnum_ge_inv_gamma a i Hgamma Hinv); auto).
  destruct Hinv as [Hinv0 Hinv1].  
  split.
  - rewrite <- Hgamma. unfold gamma. apply (Z_land_leb i _ H).
  - unfold gamma in Hgamma.
    rewrite (Z_lor_recompose i (snd a)). rewrite <- add_lor_excl.
    + rewrite Hgamma; apply Zplus_le_compat_l.
      rewrite Z.land_comm; apply Z_land_leb, Hinv1.
    + apply Z_land_disjoint.
Qed.

Lemma tnum_ge_inv_add: forall a b,
  tnum_ge_inv a ->
  tnum_ge_inv b ->
  tnum_ge_inv (tnum_add a b).
Proof.
  unfold tnum_ge_inv, tnum_add; intros.
  destruct a as (av, am).
  destruct b as (bv, bm).
  simpl in *.
  destruct H as (Hav & Ham).
  destruct H0 as (Hbv & Hbm).
  rewrite ! Z.land_nonneg.
  rewrite ! Z.lor_nonneg.
  rewrite ! Z.lxor_nonneg.
  lia.
Qed.

Lemma tnum_ge_inv_lshift: forall a b,
  tnum_ge_inv a ->
  tnum_ge_inv (tnum_lshift a b).
Proof.
  unfold tnum_ge_inv, tnum_lshift; intros.
  destruct a as (av, am).
  simpl in *.
  destruct H as (Hav & Ham).
  rewrite ! Z.shiftl_nonneg.
  lia.
Qed.

Lemma tnum_ge_inv_rshift: forall a b,
  tnum_ge_inv a ->
  tnum_ge_inv (tnum_rshift a b).
Proof.
  unfold tnum_ge_inv, tnum_rshift; intros.
  destruct a as (av, am).
  simpl in *.
  destruct H as (Hav & Ham).
  rewrite ! Z.shiftr_nonneg.
  lia.
Qed.