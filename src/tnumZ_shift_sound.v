From Coq Require Import ZArith Lia Btauto.
From bpf.src Require Import tnumZ.

Lemma tnum_lshift_sound : forall a i shift,
    gamma a i ->
    gamma (tnum_lshift a shift) (Z.shiftl i shift).
Proof.
  unfold gamma.
  intros a i shift Hg.
  unfold tnum_lshift.
  simpl.
  rewrite <- Hg.
  apply Z.bits_inj.
  unfold Z.eqf.
  simpl.  intros n.
  assert (Hn0: n < 0 \/ n >= 0) by lia.
  destruct Hn0.
  - destruct n ; try lia. simpl. reflexivity.
  - rewrite! Z.land_spec.
    rewrite! Z.shiftl_spec by lia.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite! Z.shiftl_spec by lia.
    remember (n - shift) as m.
    assert (Hm0: m < 0 \/ m >= 0) by lia.
    destruct Hm0 as [Hm0 | Hm0].
    + rewrite ! Z.testbit_neg_r by lia.
      auto.
    + rewrite! Z.lnot_spec by lia.
      f_equal.
Qed.

Lemma tnum_rshift_sound : forall a i shift,
    gamma a i ->
    gamma (tnum_rshift a shift) (Z.shiftr i shift).
Proof.
  unfold gamma.
  intros a i shift Hg.
  unfold tnum_rshift.
  simpl.
  rewrite <- Hg.
  apply Z.bits_inj.
  unfold Z.eqf.
  simpl.  intros n.
  assert (Hn0: n < 0 \/ n >= 0) by lia.
  destruct Hn0.
  - destruct n ; try lia. simpl. reflexivity.
  - rewrite! Z.land_spec.
    rewrite! Z.shiftr_spec by lia.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite! Z.shiftr_spec by lia.
    remember (n + shift) as m.
    assert (Hm0: m < 0 \/ m >= 0) by lia.
    destruct Hm0 as [Hm0 | Hm0].
    + rewrite ! Z.testbit_neg_r by lia.
      auto.
    + rewrite! Z.lnot_spec by lia.
      f_equal.
Qed.