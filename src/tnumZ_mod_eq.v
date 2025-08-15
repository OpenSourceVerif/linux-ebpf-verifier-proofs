From Coq Require Import List ZArith Lia.
From bpf.src Require Import Zmore tnumZ tnumZ_shift_sound.

Lemma Z_testbit_mod : forall n i a b,
    0 <= i < n ->
    a mod (2 ^ n) = b mod (2 ^ n) ->
    Z.testbit a i = Z.testbit b i.
Proof.
  intros.
  rewrite <- Z.mod_pow2_bits_low with (n:=n) by lia.
  rewrite H0.
  rewrite Z.mod_pow2_bits_low with (n:=n) by lia.
  reflexivity.
Qed.

Lemma Z_lnot_mod: forall a1 a2 k,
  0 <= k ->
  let m := 2^k in
    a1 mod m = a2 mod m ->
    Z.lnot a1 mod m = Z.lnot a2 mod m.
Proof.
  intros.
  apply Z.bits_inj; unfold Z.eqf; intros.
  subst m.
  assert (n < 0 \/ 0 <= k <= n \/ 0 <= n < k) by lia.
  destruct H1 as [H1 | [H1 | H1]].
  - rewrite !Z.testbit_neg_r; auto.
  - rewrite !Z.mod_pow2_bits_high; auto.
  - rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.lnot_spec; try lia.
    rewrite (Z_testbit_mod k n a1 a2); auto.
Qed.

Lemma Z_land_mod: forall a1 b1 a2 b2 k,
  0 <= k ->
  let m := 2^k in
    a1 mod m = a2 mod m ->
    b1 mod m = b2 mod m ->
    Z.land a1 b1 mod m = Z.land a2 b2 mod m.
Proof.
  intros.
  apply Z.bits_inj; unfold Z.eqf; intros.
  subst m.
  assert (n < 0 \/ 0 <= k <= n \/ 0 <= n < k) by lia.
  destruct H2 as [H2 | [H2 | H2]].
  - rewrite !Z.testbit_neg_r; auto.
  - rewrite !Z.mod_pow2_bits_high; auto.
  - rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.land_spec.
    rewrite (Z_testbit_mod k n a1 a2); auto.
    rewrite (Z_testbit_mod k n b1 b2); auto.
Qed.

Lemma Z_lor_mod: forall a1 b1 a2 b2 k,
  0 <= k ->
  let m := 2^k in
    a1 mod m = a2 mod m ->
    b1 mod m = b2 mod m ->
    Z.lor a1 b1 mod m = Z.lor a2 b2 mod m.
Proof.
  intros.
  apply Z.bits_inj; unfold Z.eqf; intros.
  subst m.
  assert (n < 0 \/ 0 <= k <= n \/ 0 <= n < k) by lia.
  destruct H2 as [H2 | [H2 | H2]].
  - rewrite !Z.testbit_neg_r; auto.
  - rewrite !Z.mod_pow2_bits_high; auto.
  - rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.lor_spec.
    rewrite (Z_testbit_mod k n a1 a2); auto.
    rewrite (Z_testbit_mod k n b1 b2); auto.
Qed.

Lemma Z_lxor_mod: forall a1 b1 a2 b2 k,
  0 <= k ->
  let m := 2^k in
    a1 mod m = a2 mod m ->
    b1 mod m = b2 mod m ->
    Z.lxor a1 b1 mod m = Z.lxor a2 b2 mod m.
Proof.
  intros.
  apply Z.bits_inj; unfold Z.eqf; intros.
  subst m.
  assert (n < 0 \/ 0 <= k <= n \/ 0 <= n < k) by lia.
  destruct H2 as [H2 | [H2 | H2]].
  - rewrite !Z.testbit_neg_r; auto.
  - rewrite !Z.mod_pow2_bits_high; auto.
  - rewrite !Z.mod_pow2_bits_low; try lia.
    rewrite !Z.lxor_spec.
    rewrite (Z_testbit_mod k n a1 a2); auto.
    rewrite (Z_testbit_mod k n b1 b2); auto.
Qed.

Lemma Z_add_mod_eq: forall a1 b1 a2 b2 k,
  0 <= k ->
  let m := 2^k in
    a1 mod m = a2 mod m ->
    b1 mod m = b2 mod m ->
    Z.add a1 b1 mod m = Z.add a2 b2 mod m.
Proof.
  intros.
  rewrite (Zplus_mod a1 b1).
  rewrite (Zplus_mod a2 b2).
  rewrite H0, H1.
  reflexivity.
Qed.

Lemma Z_shiftl_mod_eq: forall a1 a2 k,
  0 <= k ->
  let m := 2^k in
    a1 mod m = a2 mod m ->
    (Z.shiftl a1 1) mod m = (Z.shiftl a2 1) mod m.
Proof.
  intros.
  rewrite !Z.shiftl_mul_pow2; try lia.
  rewrite <- (Zmult_mod_idemp_l a1 (2^1) m).
  rewrite <- (Zmult_mod_idemp_l a2 (2^1) m).
  rewrite H0.
  reflexivity.
Qed.

Lemma Z_shiftr_mod_eq: forall a1 a2 k,
  0 <= k ->
  let m := 2^k in
    0 <= a1 < m ->
    0 <= a2 < m ->
    a1 mod m = a2 mod m ->
    (Z.shiftr a1 1) mod m = (Z.shiftr a2 1) mod m.
Proof.
  intros.
  rewrite !Z.mod_small in H2; auto.
  rewrite H2.
  reflexivity.
Qed.

Definition mod_pair p m := (fst p mod m, snd p mod m).

Lemma pair_mod_mod: forall p m,
  mod_pair (mod_pair p m) m = mod_pair p m.
Proof.
  intros. unfold mod_pair. simpl.
  repeat rewrite Zmod_mod.
  reflexivity.
Qed.

Lemma tnumZ_add_mod: forall a1 b1 a2 b2 k,
  0 <= k ->
  let m := (2 ^ k) in
    mod_pair a1 m = mod_pair a2 m ->
    mod_pair b1 m = mod_pair b2 m ->
    mod_pair (tnum_add a1 b1) m
  = mod_pair (tnum_add a2 b2) m.
Proof.
  intros a1 b1 a2 b2 k Hkge0 m Heqa Heqb.
  unfold mod_pair.
  injection Heqa as Heqa1 Heqa2.
  injection Heqb as Heqb1 Heqb2.
  unfold tnum_add. simpl.
  subst m.
  assert (Z.lor (Z.lxor (snd a1 + snd b1 + (fst a1 + fst b1)) (fst a1 + fst b1)) 
                (Z.lor (snd a1) (snd b1)) mod 2 ^ k
        = Z.lor (Z.lxor (snd a2 + snd b2 + (fst a2 + fst b2)) (fst a2 + fst b2))
                (Z.lor (snd a2) (snd b2)) mod 2 ^ k).
  { apply Z_lor_mod; auto.
    - apply Z_lxor_mod; auto.
      repeat apply Z_add_mod_eq; auto.
      repeat apply Z_add_mod_eq; auto.
    - apply Z_lor_mod; auto. }
  f_equal.
  - apply Z_land_mod; auto.
    + apply Z_add_mod_eq; auto.
    + apply Z_lnot_mod; auto.
  - apply H.
Qed.

Lemma tnumZ_lshift1_mod: forall a1 a2 k,
  0 <= k ->
  let m := (2 ^ k) in
    mod_pair a1 m = mod_pair a2 m ->
    mod_pair (tnum_lshift a1 1) m
  = mod_pair (tnum_lshift a2 1) m.
Proof.
  intros a1 a2 k Hkge0 m Heqa.
  unfold mod_pair.
  injection Heqa as Heqa1 Heqa2.
  unfold tnum_lshift.
  unfold fst at 1. unfold snd at 1.
  unfold fst at 2. unfold snd at 2.
  f_equal; apply Z_shiftl_mod_eq; auto.
Qed.

Lemma tnumZ_rshift1_mod: forall a1 a2 k,
  0 <= k ->
  let m := (2 ^ k) in
    0 <= fst a1 < m ->
    0 <= snd a1 < m ->
    0 <= fst a2 < m ->
    0 <= snd a2 < m ->
    mod_pair a1 m = mod_pair a2 m ->
    mod_pair (tnum_rshift a1 1) m
  = mod_pair (tnum_rshift a2 1) m.
Proof.
  intros a1 a2 k Hkge0 m Ha1r1 Ha1r2 Ha2r1 Ha2r2 Heqa.
  unfold mod_pair.
  injection Heqa as Heqa1 Heqa2.
  unfold tnum_rshift.
  unfold fst at 1. unfold snd at 1.
  unfold fst at 2. unfold snd at 2.
  f_equal; apply Z_shiftr_mod_eq; auto.
Qed.

Lemma tnum_mul_rec_congr_mod : forall n a1 b1 f1 a2 b2 f2,
  let m := 2 ^ 64 in
    0 <= fst a1 < m ->
    0 <= snd a1 < m ->
    0 <= fst a2 < m ->
    0 <= snd a2 < m ->
  (* arguments equal (mod m) *)
  mod_pair a1 m = mod_pair a2 m ->
  mod_pair b1 m = mod_pair b2 m ->
  mod_pair f1 m = mod_pair f2 m ->
  (* output equal (mod m) *)
  mod_pair (tnum_mul_rec n a1 b1 f1) m = mod_pair (tnum_mul_rec n a2 b2 f2) m.
Proof.
  intros n.
  induction n as [| n' IHn'];
  intros a1 b1 f1 a2 b2 f2 m Ha1r1 Ha1r2 Ha2r1 Ha2r2 Heqa Heqb Heqf.
  - simpl. apply Heqf.
  - simpl.
    assert (Heqa': fst a1 mod m = fst a2 mod m /\ snd a1 mod m = snd a2 mod m).
    { injection Heqa as Heqa1 Heqa2. split; apply Heqa1 + apply Heqa2. }
    assert (Heqb': fst b1 mod m = fst b2 mod m /\ snd b1 mod m = snd b2 mod m).
    { injection Heqb as Heqb1 Heqb2. split; apply Heqb1 + apply Heqb2. }
    assert (Hcond: forall x y, x mod m = y mod m -> Z.land x 1 = Z.land y 1).
    { intros.
      assert (0 <= Z.land x 1) by (apply (Z.land_nonneg x 1); lia).
      assert (0 <= Z.land y 1) by (apply (Z.land_nonneg y 1); lia).
      pose proof (Z_land_1_eq x).
      pose proof (Z_land_1_eq y).
      rewrite <- (Z.mod_small (Z.land x 1) (2^64)).
      2:{  lia. }
      rewrite <- (Z.mod_small (Z.land y 1) (2^64)).
      2:{  lia. }
      apply Z_land_mod. lia. apply H. reflexivity. }
    rewrite (Hcond (fst a1) (fst a2)); try apply Heqa'.
    rewrite (Hcond (snd a1) (snd a2)); try apply Heqa'.
    clear Hcond.
    pose proof tnum_rshift1_range.
    destruct (Z.land (fst a2) 1 =? 1).
    + apply IHn'; try apply H;
      try apply Ha1r1 + apply Ha1r2 + apply Ha2r1 + apply Ha2r2.
      apply tnumZ_rshift1_mod; auto; try lia.
      apply tnumZ_lshift1_mod; auto; try lia.
      apply tnumZ_add_mod; auto. lia.
      unfold mod_pair; simpl; f_equal.
      injection Heqb as Heqb1 Heqb2. apply Heqb2.
    + destruct (Z.land (snd a2) 1 =? 1).
      * apply IHn'; try apply H;
        try apply Ha1r1 + apply Ha1r2 + apply Ha2r1 + apply Ha2r2.
        apply tnumZ_rshift1_mod; auto; try lia.
        apply tnumZ_lshift1_mod; auto; try lia.
        apply tnumZ_add_mod; auto. lia.
        unfold mod_pair; simpl; f_equal.
        apply (Z_lor_mod (fst b1) (snd b1) (fst b2) (snd b2) 64);
        try apply Heqb'; lia.
      * apply IHn'; try apply H;
        try apply Ha1r1 + apply Ha1r2 + apply Ha2r1 + apply Ha2r2.
        apply tnumZ_rshift1_mod; auto; try lia.
        apply tnumZ_lshift1_mod; auto; try lia.
        apply Heqf.
Qed.

Lemma tnum_mul_rec_mod_eq : forall n a b f,
  0 <= (Z.of_nat n) <= 64 ->
  let m := (2 ^ 64) in
    0 <= fst a < m ->
    0 <= snd a < m ->
    mod_pair (tnum_mul_rec n
      (mod_pair a m)
      (mod_pair b m)
      (mod_pair f m)) m
  = mod_pair (tnum_mul_rec n a b f) m.
Proof.
  intros.
  apply tnum_mul_rec_congr_mod.
  - simpl. apply Z_mod_lt. lia.
  - simpl. apply Z_mod_lt. lia.
  - lia.
  - lia.
  - unfold mod_pair. simpl.
    f_equal; apply Zmod_mod.
  - unfold mod_pair. simpl.
    f_equal; apply Zmod_mod.
  - unfold mod_pair. simpl.
    f_equal; apply Zmod_mod.
Qed. 
