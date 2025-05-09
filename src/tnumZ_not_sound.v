From Coq Require Import ZArith Lia Btauto.
From bpf.src Require Import tnumZ.

Lemma fst_tnum_not : forall a,
    fst (tnum_not a) = Z.lnot (Z.lor (fst a)  (snd a)).
Proof.
  unfold tnum_not.
  reflexivity.
Qed.

Lemma tnum_not_sound : forall a i,
    gamma a i ->
    gamma (tnum_not a) (Z.lnot i).
Proof.
  unfold gamma.
  intros.
  unfold tnum_not.
  simpl.
  rewrite <- H.
  apply Z.bits_inj.
  unfold Z.eqf.
  simpl.  intros.
  assert (n < 0 \/ n >= 0) by lia.
  destruct H0.
  - destruct n ; try lia. simpl. reflexivity.
  - rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite! Z.lor_spec.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    btauto.
Qed.