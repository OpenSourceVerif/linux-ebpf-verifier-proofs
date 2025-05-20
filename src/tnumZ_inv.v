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