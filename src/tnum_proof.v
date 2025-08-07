From Coq Require Import List ZArith Lia Bool.
From compcert.lib Require Import Integers.
(*From bpf.src Require Import tnum. *)
Require Import tnumZ tnumZ_inv tnumZ_add_sound tnumZ_sub_sound tnumZ_mul_sound tnumZ_udiv_sound tnumZ_umod_sound.
Require Import tnum.

Import ListNotations.

Definition mem_tnum (x: int64) (a: tnum): bool :=
  Int64.eq (Int64.and x (Int64.not (snd a))) (fst a).


Lemma int64_eq_if_same:
  forall x y : int64, x = y <-> Int64.eq x y = true.
Proof.
  intros.
  generalize (Int64.eq_spec x y).
  destruct (Int64.eq x y); intuition congruence.
Qed.

Open Scope Z_scope.

Lemma land_ub : forall x y,
    0 <= x ->
    0 <= y ->
    Z.land x y <= x.
Proof.
  intros.
  destruct x; destruct y;  try lia.
  - simpl. lia.
  - rewrite Z.land_0_l. lia.
  - rewrite Z.land_0_r. lia.
  - simpl. clear.  revert p0.
    induction p; destruct p0;
      try specialize (IHp p0); simpl; try lia.
Qed.

Lemma Zland_and : forall x y,
    Z.land (Int64.unsigned x) (Int64.unsigned y) = Int64.unsigned (Int64.and x y).
Proof.
  intros.
  unfold Int64.and.
  rewrite Int64.unsigned_repr_eq.
  rewrite Z.mod_small.
  split.
  rewrite Z.land_nonneg.
  assert (Rx := Int64.unsigned_range x).
  assert (Ry := Int64.unsigned_range y).
  split.
  - lia.
  - eapply Z.le_lt_trans.
    apply land_ub. lia.
    lia. lia.
Qed.

Lemma Zlnot_not : forall x,
    forall n , 0 <= n < Int64.zwordsize ->
    Z.testbit (Z.lnot (Int64.unsigned x)) n = Z.testbit (Int64.unsigned (Int64.not x)) n.
Proof.
  intros.
  change (Z.testbit (Int64.unsigned (Int64.not x)))
    with  (Int64.testbit (Int64.not x)).
  rewrite Int64.bits_not by lia.
  rewrite Z.lnot_spec by lia.
  reflexivity.
Qed.


(** [to_tnumZ] and [of_tnumZ] link tnum over int64 and Z *)

Definition to_tnumZ (x : tnum)  :=
  (Int64.unsigned (fst x) ,
    Int64.unsigned (snd x)).

Definition of_tnumZ (x : tnumZ.tnum)  :=
  (Int64.repr (fst x) , Int64.repr (snd x)).

Lemma mem_tnum_gamma : forall i a,
    mem_tnum i a = true ->
    gamma (to_tnumZ a) (Int64.unsigned i).
Proof.
  unfold mem_tnum,gamma.
  intros.
  rewrite <- int64_eq_if_same in H.
  unfold to_tnumZ.
  rewrite <- H.
  simpl.
  rewrite <- Zland_and.
  apply Z.bits_inj.
  unfold Z.eqf. intros.
  rewrite! Z.land_spec.
  change (Z.testbit (Int64.unsigned i) n) with (Int64.testbit i n).
  assert (n < 0 \/ n >= Int64.zwordsize \/ 0 <= n < Int64.zwordsize) by lia.
  destruct H0 as [N | [N | N]].
  - rewrite Int64.bits_below by lia.
    reflexivity.
  - rewrite Int64.bits_above by lia.
    reflexivity.
  - f_equal.
    apply Zlnot_not;auto.
Qed.

Lemma testbit_add : forall i x y,
    0 <= i < Int64.zwordsize ->
    Int64.testbit (Int64.add x y) i =
      Z.testbit (Int64.unsigned x + Int64.unsigned y) i.
Proof.
  intros. unfold Int64.add.
  rewrite Int64.testbit_repr by auto.
  reflexivity.
Qed.

Lemma testbit_sub : forall i x y,
    0 <= i < Int64.zwordsize ->
    Int64.testbit (Int64.sub x y) i =
      Z.testbit (Int64.unsigned x - Int64.unsigned y) i.
Proof.
  intros. unfold Int64.sub.
  rewrite Int64.testbit_repr by auto.
  reflexivity.
Qed.

Lemma testbit_divu : forall i x y,
    0 <= i < Int64.zwordsize ->
    Int64.testbit (Int64.divu x y) i =
      Z.testbit (Z.div (Int64.unsigned x) (Int64.unsigned y)) i.
Proof.
  intros. unfold Int64.divu.
  rewrite Int64.testbit_repr by auto.
  reflexivity.
Qed.

Lemma testbit_modu : forall i x y,
    0 <= i < Int64.zwordsize ->
    Int64.testbit (Int64.modu x y) i =
      Z.testbit (Z.modulo (Int64.unsigned x) (Int64.unsigned y)) i.
Proof.
  intros. unfold Int64.modu.
  rewrite Int64.testbit_repr by auto.
  reflexivity.
Qed.

(*
Lemma add_carry_bit_low : forall x1 x2 y1 y2 n c,
    (forall i, (i < n)%nat -> Z.testbit x1 (Z.of_nat i)  =
                                Z.testbit x2 (Z.of_nat i)) ->
    (forall i, (i < n)%nat -> Z.testbit y1 (Z.of_nat i)  =
                                Z.testbit y2 (Z.of_nat i)) ->
  add_carry_bit x1 y1 c n = add_carry_bit x2 y2 c n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    intros.
    rewrite IHn.
    rewrite H.
    rewrite H0.
    reflexivity.
    lia. lia.
    intros.
    apply H. lia. intros. apply H0. lia.
Qed.
*)

Lemma testbit_mod : forall n i a b,
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

Lemma testbit_pow2 : forall n i a,
    0 <= i < n ->
    Z.testbit a i = Z.testbit (a + 2 ^ n) i.
Proof.
  intros.
  apply (testbit_mod _ _ _ _ H).
  rewrite <- (Z_mod_plus _ 1).
  rewrite Z.mul_1_l. reflexivity.
  lia.
Qed.

Lemma tnum_add_eq : forall a b,
    tnum_add a b =
      of_tnumZ (tnumZ.tnum_add (to_tnumZ a) (to_tnumZ b)).
Proof.
  unfold tnum_add, tnumZ.tnum_add.
  unfold of_tnumZ.
  simpl. intros.
  f_equal.
  - apply Int64.same_bits_eq.
    intros.
    rewrite Int64.testbit_repr by auto.
    rewrite Int64.bits_and by auto.
    rewrite testbit_add by auto.
    rewrite Z.land_spec.
    f_equal.
    rewrite! Int64.bits_not by auto.
    rewrite Z.lnot_spec by tauto.
    f_equal.
    rewrite! Int64.bits_or by auto.
    rewrite Z.lor_spec by tauto.
    rewrite! Int64.bits_xor by auto.
    rewrite Z.lxor_spec by tauto.
    rewrite Z.lor_spec.
    f_equal.
    f_equal.
    +
      rewrite! testbit_add by auto.
      apply testbit_mod with (n:= Int64.zwordsize);auto.
      unfold Int64.add.
      rewrite! Int64.unsigned_repr_eq.
      change Int64.modulus with (2^Int64.zwordsize).
      change (Int64.zwordsize) with 64.
      lia.
    + rewrite! testbit_add by auto.
      reflexivity.
  - apply Int64.same_bits_eq.
    intros.
    rewrite Int64.testbit_repr by auto.
    rewrite Int64.bits_or by auto.
    rewrite Z.lor_spec.
    rewrite Int64.bits_xor by auto.
    rewrite Z.lxor_spec.
    rewrite Int64.bits_or by auto.
    rewrite Z.lor_spec.
    f_equal.
    f_equal.
    rewrite! testbit_add by auto.
    apply testbit_mod with (n:= Int64.zwordsize);auto.
    unfold Int64.add.
    rewrite! Int64.unsigned_repr_eq.
    change Int64.modulus with (2^Int64.zwordsize).
    change (Int64.zwordsize) with 64.
    lia.
    rewrite! testbit_add by auto.
    reflexivity.
Qed.

Lemma tnum_sub_eq : forall a b,
    tnum_sub a b =
      of_tnumZ (tnumZ.tnum_sub (to_tnumZ a) (to_tnumZ b)).
Proof.
  unfold tnum_sub, tnumZ.tnum_sub. unfold of_tnumZ.
  simpl. intros. f_equal.
  - apply Int64.same_bits_eq.
    intros.
    rewrite Int64.testbit_repr by auto.
    rewrite Int64.bits_and by auto.
    rewrite testbit_sub by auto.
    rewrite Z.land_spec.
    f_equal.
    rewrite! Int64.bits_not by auto.
    rewrite Z.lnot_spec by tauto.
    f_equal.
    rewrite! Int64.bits_or by auto.
    rewrite Z.lor_spec by tauto.
    rewrite! Int64.bits_xor by auto.
    rewrite Z.lxor_spec by tauto.
    rewrite Z.lor_spec.
    f_equal.
    f_equal.
    + rewrite! testbit_add by auto.
      apply testbit_mod with (n:= Int64.zwordsize);auto.
      unfold Int64.sub.
      rewrite! Int64.unsigned_repr_eq.
      change Int64.modulus with (2^Int64.zwordsize).
      change (Int64.zwordsize) with 64.
      lia.
    + rewrite! testbit_sub by auto.
      rewrite Int64.unsigned_sub_borrow.
      unfold Int64.sub_borrow.
      destruct (Coqlib.zlt (Int64.unsigned (fst a) - Int64.unsigned (fst b) - Int64.unsigned Int64.zero) 0).
      * rewrite Int64.unsigned_one; rewrite Z.mul_1_l.
        rewrite <- Z.add_opp_r.
        rewrite <- Z.add_assoc.
        rewrite (Z.add_comm Int64.modulus).
        rewrite Z.add_assoc.
        change Int64.modulus with (2^Int64.zwordsize).
        rewrite <- testbit_pow2 with (n := Int64.zwordsize);auto.
      * rewrite Int64.unsigned_zero. simpl.
        rewrite Z.add_0_r. reflexivity.
  - apply Int64.same_bits_eq.
    intros.
    rewrite Int64.testbit_repr by auto.
    rewrite Int64.bits_or by auto.
    rewrite Z.lor_spec.
    rewrite Int64.bits_xor by auto.
    rewrite Z.lxor_spec.
    rewrite Int64.bits_or by auto.
    rewrite Z.lor_spec.
    f_equal.
    f_equal.
    + rewrite! testbit_add by auto.
      apply testbit_mod with (n:= Int64.zwordsize);auto.
      unfold Int64.sub.
      rewrite! Int64.unsigned_repr_eq.
      change Int64.modulus with (2^Int64.zwordsize).
      change (Int64.zwordsize) with 64.
      lia.
    + rewrite! testbit_sub by auto.
      rewrite Int64.unsigned_sub_borrow.
      unfold Int64.sub_borrow.
      destruct (Coqlib.zlt (Int64.unsigned (fst a) - Int64.unsigned (fst b) - Int64.unsigned Int64.zero) 0).
      * rewrite Int64.unsigned_one; rewrite Z.mul_1_l.
        rewrite <- Z.add_opp_r.
        rewrite <- Z.add_assoc.
        rewrite (Z.add_comm Int64.modulus).
        rewrite Z.add_assoc.
        change Int64.modulus with (2^Int64.zwordsize).
        rewrite <- testbit_pow2 with (n := Int64.zwordsize);auto.
      * rewrite Int64.unsigned_zero. simpl.
        rewrite Z.add_0_r. reflexivity.
Qed.

Lemma Int64_unsigned_add_nonneg : forall (x y : int64),
  0 <= Int64.unsigned x + Int64.unsigned y.
Proof.
  intros. apply Z.add_nonneg_nonneg; apply Int64.unsigned_range.
Qed.

Lemma Int64_unsigned_add : forall (x y : int64),
  Int64.unsigned x + Int64.unsigned y <= Int64.max_unsigned ->
  Int64.unsigned (Int64.add x y) = Int64.unsigned x + Int64.unsigned y.
Proof.
  intros. unfold Int64.add.
  rewrite Int64.unsigned_repr. reflexivity.
  pose proof (Int64_unsigned_add_nonneg x y).
  lia.
Qed.

Lemma Int64_eq_unsigned : forall x y,
  Int64.eq x y = Z.eqb (Int64.unsigned x) (Int64.unsigned y).
Proof.
  intros. unfold Int64.eq.
  destruct (Z.eqb_spec (Int64.unsigned x) (Int64.unsigned y)) as [E|E].
  - rewrite E. rewrite Coqlib.zeq_true. reflexivity.
  - rewrite Coqlib.zeq_false; lia.
Qed.

Lemma tnum_udiv_eq : forall (a b : tnum),
    Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned ->
    tnum_udiv a b =
      of_tnumZ (tnumZ.tnum_udiv (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros. unfold tnum_udiv, tnumZ.tnum_udiv. simpl.
  rewrite !Int64_eq_unsigned. rewrite Int64.unsigned_zero.
  destruct (Z.eqb_spec (Int64.unsigned (fst b)) 0).
  { reflexivity. }
  destruct ((Int64.unsigned (snd a) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  unfold of_tnumZ. f_equal. simpl.
  unfold Int64_ones, Int64_size, Int64.divu.
  rewrite Int64_unsigned_add; try lia.
  rewrite Int64.unsigned_repr. reflexivity.
  pose proof (Int64.unsigned_range (fst b)).
  pose proof (Int64_unsigned_add_nonneg (fst a) (snd a)).
  split.
  - apply Z_div_nonneg_nonneg; lia.
  - apply Z.le_trans with (m := Int64.unsigned (fst a) + Int64.unsigned (snd a)).
    2:{ apply H. }
    rewrite <- Z.div_1_r.
    apply Z.div_le_compat_l; lia.
Qed.

Lemma Z_land_Int64_unsigned: forall x y,
  0 <= x <= Int64.max_unsigned ->
  Z.land x (Int64.unsigned (Int64.repr y)) = Z.land x y.
Proof.
  intros.
  rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  rewrite <- Z.land_ones; try lia.
  rewrite (Z.land_comm y).
  rewrite Z.land_assoc.
  rewrite Z.land_ones; try lia.
  rewrite Z.mod_small.
  - reflexivity.
  - unfold Int64.max_unsigned in H; simpl in H. lia.
Qed.

Lemma Z_land_range_Int64: forall x y,
  0 <= x <= Int64.max_unsigned ->
  0 <= Z.land x y <= Int64.max_unsigned.
Proof.
  intros. split.
  - apply Z.land_nonneg. left. lia.
  - apply (Z.le_trans _ x);
    try apply Zmore.Z_land_leb; lia.
Qed.

Lemma Z_lsb_range_int64 : forall x,
  0 < x <= Int64.max_unsigned ->
  0 < Z.land x (- x) <= Int64.max_unsigned.
Proof.
  intros. unfold Int64.max_unsigned in H.
  apply (Z_lsb_range x Int64.zwordsize).
  simpl in *. lia.
Qed.

Lemma Z_lor_eqm (a b c d: Z) :
  Int64.eqm a c -> Int64.eqm b d ->
  Int64.eqm (Z.lor a b) (Z.lor c d).
Proof.
  intros.
  unfold Int64.eqm in *.
  apply Zbits.eqmod_mod_eq in H, H0;
  try (change Int64.modulus with (2^64); lia).
  apply Zbits.eqmod_same_bits.
  intros.
  change Int64.modulus with (2^(Z.of_nat Int64.wordsize)) in *.
  rewrite !Z.lor_spec.
  rewrite (testbit_mod (Z.of_nat Int64.wordsize) _ a c); try lia.
  rewrite (testbit_mod (Z.of_nat Int64.wordsize) _ b d); try lia.
  reflexivity.
Qed.

Lemma mod_get_low_bits_eq : forall (a b : tnum),
  0 <= Int64.unsigned (fst b) + Int64.unsigned (snd b) <= Int64.max_unsigned ->
  mod_get_low_bits a b = of_tnumZ (tnumZ.mod_get_low_bits (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros. unfold mod_get_low_bits, tnumZ.mod_get_low_bits.
  unfold Int64_odd. simpl.
  destruct (Z.odd (Int64.unsigned (fst b)) || Z.odd (Int64.unsigned (snd b))).
  { reflexivity. }
  unfold of_tnumZ. simpl.
  assert (forall x,
    Int64.and x 
      (Int64.sub (Int64.and (Int64.add (fst b) (snd b)) 
        (Int64.neg (Int64.add (fst b) (snd b)))) Int64.one) = 
    Int64.repr (Z.land (Int64.unsigned x)
      (Z.land (Int64.unsigned (fst b) + Int64.unsigned (snd b))
        (- (Int64.unsigned (fst b) + Int64.unsigned (snd b))) - 1))).
  { intros.
    unfold Int64.and, Int64.sub, Int64.add.
    f_equal.
    destruct (Int64.unsigned (fst b) + Int64.unsigned (snd b)); try lia.
    { rewrite (Int64.unsigned_repr 0); try lia. simpl.
      rewrite (Int64.unsigned_repr 0); try lia. simpl.
      rewrite Int64.unsigned_one.
      apply Z_land_Int64_unsigned.
      apply Int64.unsigned_range_2. }
    f_equal.
    rewrite (Int64.unsigned_repr (Z.pos p)); try lia.
    rewrite Int64.neg_repr.
    rewrite Z_land_Int64_unsigned; try lia.
    rewrite !Int64.unsigned_repr.
    + reflexivity.
    + split.
      * apply Z.land_nonneg. left. lia.
      * apply (Z.le_trans _ (Z.pos p));
        try apply Zmore.Z_land_leb; lia.
    + split.
      * apply Zlt_0_le_0_pred.
        pose proof (Z_lsb_range_int64 (Z.pos p)).
        rewrite Int64.unsigned_repr; lia.
      * apply Z.le_le_pred.
        apply Int64.unsigned_range_2. }
  rewrite !H0. clear H0.
  f_equal.
  unfold Int64.or.
  rewrite Int64.unsigned_repr.
  2:{ apply Z_land_range_Int64. apply Int64.unsigned_range_2. }
  unfold Int64.and, Int64.sub, Int64.add.
  destruct (Int64.unsigned (fst b) + Int64.unsigned (snd b));
  try reflexivity; try lia.
  rewrite !Int64.unsigned_repr; try lia.
  2:{ apply Z_land_range_Int64. apply Int64.unsigned_range_2. }
  rewrite Int64.neg_repr.
  rewrite Z_land_Int64_unsigned; try lia.
  assert (forall x, 0 < x <= Int64.max_unsigned -> 
    Int64.unsigned (Int64.not (Int64.repr (x - 1))) = 2^64 - x).
  { intros. rewrite Int64.unsigned_not.
    rewrite Int64.unsigned_repr.
    - unfold Int64.max_unsigned. rewrite <- Z.sub_add_distr.
      rewrite Zplus_minus. reflexivity.
    - pose proof (Z_lsb_range_int64 x). lia. }
  rewrite H0. clear H0.
  2:{ apply Z_lsb_range_int64. lia. }
  rewrite Z.lnot_pred.
  apply Int64.eqm_samerepr.
  apply Z_lor_eqm.
  { apply Int64.eqm_refl. }
  unfold Int64.eqm. change Int64.modulus with (2^64).
  apply (Zbits.eqmod_trans _ _ ((- Z.land (Z.pos p) (- Z.pos p)) mod (2^64))).
  - apply Zbits.eqmod_refl2.
    rewrite <- (Z.mod_small _ (2^64)).
    + rewrite <- Z.add_opp_r.
      rewrite Z.add_comm.
      rewrite <- (Z.mul_1_l (2 ^ 64)).
      apply Z_mod_plus_full.
    + pose proof (Z_lsb_range_int64 (Z.pos p)).
      change Int64.max_unsigned with (2 ^ 64 - 1) in *. lia.
  - apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. 
    change Int64.modulus with (2^64). lia.
Qed.

Lemma Z_size_range_Int64 : forall x,
  0 <= x <= Int64.max_unsigned -> 0 <= Z_size_Z x <= Int64.zwordsize.
Proof.
  intros. split.
  - apply Z_size_Z_nonneg.
  - unfold Z_size_Z. change Int64.zwordsize with 64.
    destruct x; try lia.
    rewrite (Z.abs_eq _ (Pos2Z.is_nonneg p)).
    apply (Z.le_trans _ (Z.log2 (Int64.max_unsigned) + 1)).
    + pose proof (Z.log2_le_mono (Z.pos p) (Int64.max_unsigned)). lia.
    + simpl. lia.
Qed.

Lemma Z_ones_size_range_Int64 : forall x,
  0 <= x <= Int64.max_unsigned -> 0 <= Z.ones (Z_size_Z x) <= Int64.max_unsigned.
Proof.
  intros. split.
  - apply (Z.le_trans _ x).
    + apply H.
    + apply Z_size_Z_upper_bound. lia.
  - rewrite Z.ones_equiv. unfold Z_size_Z. destruct x; try lia.
    rewrite (Z.abs_eq _ (Pos2Z.is_nonneg p)).
    apply (Z.le_trans _ (Z.pred (2 ^ (Z.log2 (Int64.max_unsigned) + 1)))).
    + pose proof (Z.log2_le_mono (Z.pos p) (Int64.max_unsigned)).
      apply (Z.pred_le_mono (2 ^ (Z.log2 (Z.pos p) + 1))).
      apply Z.pow_le_mono_r; try lia.
    + unfold Int64.max_unsigned. simpl. lia.
Qed.

Lemma Z_land_ones_Int64_eq : forall (a n : Z),
      0 <= n <= Int64.zwordsize -> 
      Z.land (Int64.unsigned (Int64.repr a)) (Z.ones n) = Z.land a (Z.ones n).
Proof.
  intros. rewrite Int64.unsigned_repr_eq.
  rewrite !Z.land_ones; try lia.
  change Int64.modulus with (2^Int64.zwordsize).
  rewrite <- (Z.add_0_r Int64.zwordsize).
  rewrite <- (Z.add_opp_diag_r n).
  rewrite (Z.add_comm n).
  rewrite Z.add_assoc.
  rewrite Z.pow_add_r; try lia.
  rewrite Zaux.Zmod_mod_mult; try lia.
Qed.

Lemma tnum_umod_eq : forall (a b : tnum),
    Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned ->
    Int64.unsigned (fst b) + Int64.unsigned (snd b) <= Int64.max_unsigned ->
    tnum_umod a b =
      of_tnumZ (tnumZ.tnum_umod (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros. unfold tnum_umod, tnumZ.tnum_umod. simpl.
  rewrite !Int64_eq_unsigned. rewrite Int64.unsigned_zero.
  destruct (Z.eqb_spec (Int64.unsigned (fst b)) 0).
  { reflexivity. }
  destruct ((Int64.unsigned (snd a) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  unfold Int64_is_pow2.
  destruct ((Int64.unsigned (snd b) =? 0) && (Z_is_pow2 (Int64.unsigned (fst b)))).
  { unfold of_tnumZ. simpl. f_equal.
    all: unfold Int64.and, Int64.sub;
    rewrite Int64.unsigned_one;
    rewrite Int64.unsigned_repr;
    try reflexivity;
    pose proof (Int64.unsigned_range_2 (fst b));
    split; lia. }
  unfold of_tnumZ. simpl.
  pose proof (Int64_unsigned_add_nonneg (fst a) (snd a)).
  pose proof (Int64_unsigned_add_nonneg (fst b) (snd b)).
  assert (0 <= Z.min (Int64.unsigned (fst a) + Int64.unsigned (snd a))
    (Int64.unsigned (fst b) + Int64.unsigned (snd b)) <= Int64.max_unsigned) by lia.
  f_equal; unfold Int64.and, Int64_ones, Int64_min;
  rewrite mod_get_low_bits_eq; simpl; try lia.
  all: rewrite !Int64_unsigned_add; try lia;
  rewrite (Int64.unsigned_repr (Z.ones (Z_size_Z (Z.min
    (Int64.unsigned (fst a) + Int64.unsigned (snd a))
    (Int64.unsigned (fst b) + Int64.unsigned (snd b))))));
  (rewrite Z_land_ones_Int64_eq; reflexivity + (apply Z_size_range_Int64; lia))
    + (apply Z_ones_size_range_Int64; lia).
Qed.

Theorem tnum_binary_sound :
  forall a b i j f tnum_f tnum_fz fz
         (TNUM_FZ_SOUND : forall a i b j,
             gamma a i -> gamma b j -> gamma (tnum_fz a b) (fz i j))
         (FFZ : forall n,  0 <= n < Int64.zwordsize ->
                           forall i j ,  (Int64.testbit (f i j) n = Z.testbit (fz (Int64.unsigned i) (Int64.unsigned j)) n))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true)
         (EQ : tnum_f a b = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b)))
  ,
    mem_tnum (f i j) (tnum_f a b) = true.
Proof.
  intros.
  apply mem_tnum_gamma in MEMA.
  apply mem_tnum_gamma in MEMB.
  rewrite EQ.
  specialize (TNUM_FZ_SOUND _ _ _ _ MEMA MEMB).
  revert TNUM_FZ_SOUND.
  unfold to_tnumZ.
  generalize (Int64.unsigned (fst a), Int64.unsigned (snd a)) as az.
  generalize (Int64.unsigned (fst b), Int64.unsigned (snd b)) as bz.
  intros bz az.
  generalize (tnum_fz az bz) as r.
  destruct r.
  unfold gamma. simpl in *. intros. subst.
  unfold mem_tnum.
  simpl.
  apply int64_eq_if_same.
  apply Int64.same_bits_eq.
  intros.
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_and by auto.
  rewrite Z.land_spec.
  rewrite Z.lnot_spec by lia.
  rewrite Int64.bits_not by auto.
  rewrite! Int64.testbit_repr by auto.
  rewrite FFZ. reflexivity.
  auto.
Qed.


Theorem tnum_add_sound :
  forall a b i j
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true),
    mem_tnum (Int64.add i j) (tnum_add a b) = true.
Proof.
  intros.
  apply tnum_binary_sound with (tnum_fz := tnumZ.tnum_add) (fz:= Z.add); auto.
  - intros.
    apply tnumZ_add_sound.tnum_add_sound; auto.
  - intros.
    apply testbit_add ; auto.
  - apply tnum_add_eq.
Qed.

Theorem tnum_sub_sound :
  forall a b i j
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true),
    mem_tnum (Int64.sub i j) (tnum_sub a b) = true.
Proof.
  intros.
  apply tnum_binary_sound with (tnum_fz := tnumZ.tnum_sub) (fz:= Z.sub); auto.
  - intros.
    apply tnumZ_sub_sound.tnum_sub_sound; auto.
  - intros.
    apply testbit_sub ; auto.
  - apply tnum_sub_eq.
Qed.

Theorem tnum_binary_sound_ge_0 :
  forall a b i j f tnum_f tnum_fz fz
         (TNUM_FZ_SOUND : forall a i b j,
             tnum_ge_inv a -> tnum_ge_inv b -> gamma a i -> gamma b j -> gamma (tnum_fz a b) (fz i j))
         (FFZ : forall n,  0 <= n < Int64.zwordsize ->
                           forall i j ,  (Int64.testbit (f i j) n = Z.testbit (fz (Int64.unsigned i) (Int64.unsigned j)) n))
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true)
         (EQ : tnum_f a b = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b)))
  ,
    mem_tnum (f i j) (tnum_f a b) = true.
Proof.
  intros.
  apply mem_tnum_gamma in MEMA.
  apply mem_tnum_gamma in MEMB.
  rewrite EQ.
  specialize (TNUM_FZ_SOUND _ _ _ _ GEA GEB MEMA MEMB).
  revert TNUM_FZ_SOUND.
  unfold to_tnumZ.
  generalize (Int64.unsigned (fst a), Int64.unsigned (snd a)) as az.
  generalize (Int64.unsigned (fst b), Int64.unsigned (snd b)) as bz.
  intros bz az.
  generalize (tnum_fz az bz) as r.
  destruct r.
  unfold gamma. simpl in *. intros. subst.
  unfold mem_tnum.
  simpl.
  apply int64_eq_if_same.
  apply Int64.same_bits_eq.
  intros.
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_and by auto.
  rewrite Z.land_spec.
  rewrite Z.lnot_spec by lia.
  rewrite Int64.bits_not by auto.
  rewrite! Int64.testbit_repr by auto.
  rewrite FFZ. reflexivity.
  auto.
Qed.

Theorem tnum_udiv_sound :
  forall a b i j
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true)
         (Hrange_A : Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned),
    mem_tnum (Int64.divu i j) (tnum_udiv a b) = true.
Proof.
  intros.
  apply tnum_binary_sound_ge_0 with (tnum_fz := tnumZ.tnum_udiv) (fz:= Z.div); auto.
  - intros.
    apply tnumZ_udiv_sound.tnum_udiv_sound; auto.
  - intros.
    apply testbit_divu ; auto.
  - apply tnum_udiv_eq; auto.
Qed.

Theorem tnum_umod_sound :
  forall a b i j
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true)
         (Hrange_A : Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned)
         (Hrange_B : Int64.unsigned (fst b) + Int64.unsigned (snd b) <= Int64.max_unsigned),
         mem_tnum (Int64.modu i j) (tnum_umod a b) = true.
Proof.
  intros.
  apply tnum_binary_sound_ge_0 with (tnum_fz := tnumZ.tnum_umod) (fz:= Z.modulo); auto.
  - intros.
    apply tnumZ_umod_sound.tnum_umod_sound; auto.
  - intros.
    apply testbit_modu ; auto.
  - apply tnum_umod_eq; auto.
Qed.