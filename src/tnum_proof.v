From Coq Require Import List ZArith Lia Bool.
From compcert Require Import Integers Values.
From bpf.ebpf Require Import ebpfBinSem.

From bpf.tnum Require Import tnumZ tnumZ_inv tnumZ_add_sound tnumZ_sub_sound tnumZ_mul_sound tnumZ_udiv_sound tnumZ_umod_sound tnumZ_shift_sound tnumZ_mod_eq.
From bpf.tnum Require Import tnum.

Import ListNotations.

Definition mem_tnum (x: int64) (a: tnum): Prop :=
  Int64.and x (Int64.not (snd a)) = fst a.

Definition gamma_val (v: val) (t: tnum) : Prop :=
  match v with
  | Vlong n => mem_tnum n t
  | _ => False
  end.

Definition wf_tnum (a: tnum): Prop :=
  (Int64.and (fst a) (snd a) = Int64.zero).

(** gamma definition implies wf *)
Lemma mem_imply_wf: forall va ma i,
  mem_tnum i (va, ma) -> wf_tnum (va, ma).
Proof.
  unfold mem_tnum, wf_tnum; simpl.
  intros va ma i Hg.
  subst.
  rewrite Int64.and_assoc.
  rewrite Int64.and_commut with (y := ma).
  rewrite Int64.and_not_self.
  apply Int64.and_zero.
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

Lemma Zlor_or : forall x y,
    Z.lor (Int64.unsigned x) (Int64.unsigned y) = Int64.unsigned (Int64.or x y).
Proof.
  intros.
  unfold Int64.or.
  rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (2^64).
  apply Z.bits_inj; unfold Z.eqf; intros.
  assert (n < 0 \/ 0 <= n < 64 \/ n >= 64) by lia.
  destruct H as [H | [H | H]].
  - repeat rewrite Z.testbit_neg_r; auto.
  - rewrite Z.mod_pow2_bits_low; reflexivity + lia.
  - rewrite Z.lor_spec.
    rewrite <- (Z.mod_small (Int64.unsigned x) (2^64)).
    2:{ apply Int64.unsigned_range. }
    rewrite <- (Z.mod_small (Int64.unsigned y) (2^64)).
    2:{ apply Int64.unsigned_range. }
    rewrite !Z.mod_pow2_bits_high; try lia.
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

Lemma mem_tnum_range: forall x a, mem_tnum x a ->
  Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned.
Proof.
  intros. apply mem_imply_wf in H. clear x.
  unfold wf_tnum in H; simpl in H.
  assert (Int64.unsigned (Int64.and (fst a) (snd a)) = Int64.unsigned (Int64.zero)).
  { f_equal. apply H. }
  rewrite <- Zland_and in H0.
  rewrite Int64.unsigned_zero in H0.
  apply (Z.add_nocarry_lt_pow2 _ _ 64) in H0.
  - unfold Int64.max_unsigned; simpl. lia.
  - apply Int64.unsigned_range.
  - apply Int64.unsigned_range.
Qed.


(** [to_tnumZ] and [of_tnumZ] link tnum over int64 and Z *)

Definition to_tnumZ (x : tnum)  :=
  (Int64.unsigned (fst x) ,
    Int64.unsigned (snd x)).

Definition of_tnumZ (x : tnumZ.tnum)  :=
  (Int64.repr (fst x) , Int64.repr (snd x)).

Lemma tnumZ_tnum_id_eq : forall x,
  to_tnumZ (of_tnumZ x) = mod_pair x Int64.modulus.
Proof.
  intros. unfold mod_pair.
  unfold to_tnumZ, of_tnumZ. simpl.
  f_equal; apply Int64.unsigned_repr_eq; lia.
Qed.

Lemma tnum_tnumZ_id : forall x,
  of_tnumZ (to_tnumZ x) = x.
Proof.
  intros.
  unfold to_tnumZ, of_tnumZ. simpl.
  rewrite surjective_pairing.
  f_equal; apply Int64.repr_unsigned.
Qed.

Lemma tnum_shiftl_eq: forall x,
  tnum_lshift x Int64.one = of_tnumZ (tnumZ.tnum_lshift (to_tnumZ x) 1).
Proof.
  intros. unfold tnum_lshift, tnumZ.tnum_lshift.
  unfold of_tnumZ. f_equal.
Qed.

Lemma tnum_shiftr_eq: forall x,
  tnum_rshift x Int64.one = of_tnumZ (tnumZ.tnum_rshift (to_tnumZ x) 1).
Proof.
  intros. unfold tnum_rshift, tnumZ.tnum_rshift.
  unfold of_tnumZ. f_equal.
Qed.

Lemma to_tnumZ_ifelse: forall (c : bool) x1 x2,
  to_tnumZ (if c then x1 else x2) = if c then (to_tnumZ x1) else (to_tnumZ x2).
Proof.
  intros. destruct c; reflexivity.
Qed.

Lemma mem_tnum_gamma : forall i a,
    mem_tnum i a ->
    gamma (to_tnumZ a) (Int64.unsigned i).
Proof.
  unfold mem_tnum,gamma.
  intros.
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

Lemma testbit_mul : forall i x y,
    0 <= i < Int64.zwordsize ->
    Int64.testbit (Int64.mul x y) i =
      Z.testbit (Int64.unsigned x * Int64.unsigned y) i.
Proof.
  intros. unfold Int64.mul.
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

Lemma testbit_pow2 : forall n i a,
    0 <= i < n ->
    Z.testbit a i = Z.testbit (a + 2 ^ n) i.
Proof.
  intros.
  apply (Z_testbit_mod _ _ _ _ H).
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
      apply Z_testbit_mod with (n:= Int64.zwordsize);auto.
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
    apply Z_testbit_mod with (n:= Int64.zwordsize);auto.
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
      apply Z_testbit_mod with (n:= Int64.zwordsize);auto.
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
      apply Z_testbit_mod with (n:= Int64.zwordsize);auto.
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

Lemma Int64_repr_mod : forall x y,
  x mod Int64.modulus = y mod Int64.modulus ->
  Int64.repr x = Int64.repr y.
Proof.
  intros.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_same_bits.
  intros. apply (Z_testbit_mod 64).
  apply H0. apply H.
Qed.

Lemma tnum_mul_rec_eq : forall n a b acc_m,
    0 <= Z.of_nat n <= 64 ->
    tnum_mul_rec n a b acc_m =
      of_tnumZ (tnumZ.tnum_mul_rec n (to_tnumZ a) (to_tnumZ b) (to_tnumZ acc_m)).
Proof.
  intros n. induction n as [| n' IHn'].
  - intros. simpl. rewrite tnum_tnumZ_id. reflexivity.
  - intros. unfold tnum_mul_rec; fold tnum_mul_rec.
    unfold tnumZ.tnum_mul_rec; fold tnumZ.tnum_mul_rec.
    rewrite IHn'.
    2:{ lia. }
    unfold of_tnumZ. simpl.
    assert (Hmod_eq: forall f,
      mod_pair
      (tnumZ.tnum_mul_rec n' (mod_pair (tnumZ.tnum_rshift (to_tnumZ a) 1) (2^64))
      (mod_pair (tnumZ.tnum_lshift (to_tnumZ b) 1) (2^64))
      (mod_pair f (2^64))) (2^64) =
      mod_pair
      (tnumZ.tnum_mul_rec n' (tnumZ.tnum_rshift (to_tnumZ a) 1)
      (tnumZ.tnum_lshift (to_tnumZ b) 1)
      f) (2^64)
    ).
    { intros.
      pose proof tnum_rshift1_range.
      apply tnum_mul_rec_mod_eq;
      lia + (apply H0; unfold to_tnumZ; simpl; apply Int64.unsigned_range). }
    f_equal.
    + rewrite tnum_shiftl_eq, tnum_shiftr_eq.
      rewrite !tnumZ_tnum_id_eq.
      rewrite !to_tnumZ_ifelse.
      assert (Hcond: forall x, Int64.eq (Int64.and x Int64.one) Int64.one
              = (Z.land (Int64.unsigned x) 1 =? 1)).
      { intros. unfold Int64.eq. rewrite <- Zland_and. rewrite Int64.unsigned_one.
        destruct (Z.eqb_spec (Z.land (Int64.unsigned x) 1) 1) as [E|E].
        - rewrite E. reflexivity.
        - apply Coqlib.zeq_false. apply E. }
      rewrite !Hcond; clear Hcond.
      destruct (Z.land (Int64.unsigned (fst a)) 1 =? 1).
      { rewrite tnum_add_eq.
        rewrite tnumZ_tnum_id_eq.
        change (to_tnumZ (Int64.zero, snd b)) with (0, Int64.unsigned (snd b)).
        apply Int64_repr_mod.
        specialize (Hmod_eq (tnumZ.tnum_add (to_tnumZ acc_m) (0, Int64.unsigned (snd b)))).
        injection Hmod_eq as Hmod_eq1 Hmod_eq2.
        apply Hmod_eq1. }
      destruct (Z.land (Int64.unsigned (snd a)) 1 =? 1).
      { rewrite tnum_add_eq.
        rewrite tnumZ_tnum_id_eq.
        change (to_tnumZ (Int64.zero, Int64.or (fst b) (snd b)))
        with (0, Int64.unsigned (Int64.or (fst b) (snd b))).
        rewrite Zlor_or.
        apply Int64_repr_mod.
        specialize (Hmod_eq (tnumZ.tnum_add (to_tnumZ acc_m) (0, Int64.unsigned (Int64.or (fst b) (snd b))))).
        injection Hmod_eq as Hmod_eq1 Hmod_eq2.
        apply Hmod_eq1. }
      apply Int64_repr_mod.
      assert (to_tnumZ acc_m = mod_pair (to_tnumZ acc_m) (2^64)).
      { unfold to_tnumZ. unfold mod_pair. simpl.
        f_equal; rewrite Z.mod_small; reflexivity + apply Int64.unsigned_range. }
      rewrite H0 at 1; clear H0.
      specialize (Hmod_eq (to_tnumZ acc_m)).
      injection Hmod_eq as Hmod_eq1 Hmod_eq2.
      apply Hmod_eq1.
    + rewrite tnum_shiftl_eq, tnum_shiftr_eq.
      rewrite !tnumZ_tnum_id_eq.
      rewrite !to_tnumZ_ifelse.
      assert (Hcond: forall x, Int64.eq (Int64.and x Int64.one) Int64.one
              = (Z.land (Int64.unsigned x) 1 =? 1)).
      { intros. unfold Int64.eq. rewrite <- Zland_and. rewrite Int64.unsigned_one.
        destruct (Z.eqb_spec (Z.land (Int64.unsigned x) 1) 1) as [E|E].
        - rewrite E. reflexivity.
        - apply Coqlib.zeq_false. apply E. }
      rewrite !Hcond; clear Hcond.
      destruct (Z.land (Int64.unsigned (fst a)) 1 =? 1).
      { rewrite tnum_add_eq.
        rewrite tnumZ_tnum_id_eq.
        change (to_tnumZ (Int64.zero, snd b)) with (0, Int64.unsigned (snd b)).
        apply Int64_repr_mod.
        specialize (Hmod_eq (tnumZ.tnum_add (to_tnumZ acc_m) (0, Int64.unsigned (snd b)))).
        injection Hmod_eq as Hmod_eq1 Hmod_eq2.
        apply Hmod_eq2. }
      destruct (Z.land (Int64.unsigned (snd a)) 1 =? 1).
      { rewrite tnum_add_eq.
        rewrite tnumZ_tnum_id_eq.
        change (to_tnumZ (Int64.zero, Int64.or (fst b) (snd b)))
        with (0, Int64.unsigned (Int64.or (fst b) (snd b))).
        rewrite Zlor_or.
        apply Int64_repr_mod.
        specialize (Hmod_eq (tnumZ.tnum_add (to_tnumZ acc_m) (0, Int64.unsigned (Int64.or (fst b) (snd b))))).
        injection Hmod_eq as Hmod_eq1 Hmod_eq2.
        apply Hmod_eq2. }
      apply Int64_repr_mod.
      assert (to_tnumZ acc_m = mod_pair (to_tnumZ acc_m) (2^64)).
      { unfold to_tnumZ. unfold mod_pair. simpl.
        f_equal; rewrite Z.mod_small; reflexivity + apply Int64.unsigned_range. }
      rewrite H0 at 1; clear H0.
      specialize (Hmod_eq (to_tnumZ acc_m)).
      injection Hmod_eq as Hmod_eq1 Hmod_eq2.
      apply Hmod_eq2.
Qed.

Lemma tnum_mul_eq : forall a b (width : nat),
    0 <= (Z.of_nat width) <= 64 ->
    tnum_mul a b width =
      of_tnumZ (tnumZ.tnum_mul (to_tnumZ a) (to_tnumZ b) width).
Proof.
  intros. unfold tnum_mul, tnumZ.tnum_mul.
  rewrite tnum_add_eq.
  change (to_tnumZ (Int64.mul (fst a) (fst b), Int64.zero)) with
  (Int64.unsigned (Int64.mul (fst a) (fst b)), 0).
  change (fst (to_tnumZ a) * fst (to_tnumZ b), 0) with
  ((Int64.unsigned (fst a)) * (Int64.unsigned (fst b)), 0).
  unfold of_tnumZ.
  rewrite tnum_mul_rec_eq; try lia.
  change (to_tnumZ (Int64.zero, Int64.zero)) with (0, 0).
  assert (Hmod_eq:
    mod_pair (tnumZ.tnum_add 
      (mod_pair (Int64.unsigned (fst a) * Int64.unsigned (fst b), 0) (2^64))
      (mod_pair (tnumZ.tnum_mul_rec width (to_tnumZ a) (to_tnumZ b) (0, 0)) (2^64))) (2^64) =
    mod_pair (tnumZ.tnum_add
      (Int64.unsigned (fst a) * Int64.unsigned (fst b), 0)
      (tnumZ.tnum_mul_rec width (to_tnumZ a) (to_tnumZ b) (0, 0))) (2^64)).
  { apply tnumZ_add_mod; lia + apply pair_mod_mod. }
  injection Hmod_eq as Hmod_eq1 Hmod_eq2.
  assert ((Int64.unsigned (Int64.mul (fst a) (fst b)), 0) = 
  mod_pair (Int64.unsigned (fst a) * Int64.unsigned (fst b), 0) (2^64)).
  { unfold mod_pair. f_equal. unfold fst at 3.
    apply Z.bits_inj; unfold Z.eqf; intros.
    assert (n < 0 \/ 0 <= n < 64 \/ n >= 64) by lia.
    destruct H0 as [H0 | [H0 | H0]].
    - repeat rewrite Z.testbit_neg_r; auto.
    - rewrite !Z.mod_pow2_bits_low; try lia.
      apply testbit_mul; auto.
    - rewrite <- (Z.mod_small (Int64.unsigned (Int64.mul (fst a) (fst b))) (2^64)).
      2:{ apply Int64.unsigned_range. }
      rewrite !Z.mod_pow2_bits_high; try lia. }
  rewrite H0; clear H0.
  rewrite tnumZ_tnum_id_eq.
  f_equal; apply Int64_repr_mod; apply Hmod_eq1 + apply Hmod_eq2.
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
  destruct ((Int64.unsigned (fst b) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  destruct ((Int64.unsigned (snd a) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  destruct (Int64.unsigned (fst b) =? 0) eqn:Hb_v0.
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
  rewrite (Z_testbit_mod (Z.of_nat Int64.wordsize) _ a c); try lia.
  rewrite (Z_testbit_mod (Z.of_nat Int64.wordsize) _ b d); try lia.
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
  destruct ((Int64.unsigned (fst b) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { rewrite tnum_tnumZ_id. reflexivity. }
  destruct ((Int64.unsigned (snd a) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  unfold Int64_is_pow2.
  destruct ((Int64.unsigned (snd b) =? 0) && (Z_is_pow2 (Int64.unsigned (fst b)))) eqn:E.
  { unfold Z_is_pow2 in E.
    assert (0 < Int64.unsigned (fst b)) by lia.
    unfold of_tnumZ. simpl. f_equal.
    all: unfold Int64.and, Int64.sub;
    rewrite Int64.unsigned_one;
    rewrite Int64.unsigned_repr;
    try reflexivity;
    pose proof (Int64.unsigned_range_2 (fst b));
    split; lia. }
  destruct (Int64.unsigned (fst b) =? 0) eqn:Hb_v0.
  { reflexivity. }
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
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b)
         (EQ : tnum_f a b = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b)))
  ,
    mem_tnum (f i j) (tnum_f a b).
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
  forall dst_v v dst_t t
    (H_dst: gamma_val dst_v dst_t)
    (H_src: gamma_val v t),
  gamma_val (Val.addl dst_v v) (tnum_add dst_t t).
Proof.
  intros.
  destruct dst_v; simpl in H_dst; try contradiction.
  destruct v; simpl in H_src; try contradiction.
  simpl.
  apply tnum_binary_sound with (tnum_fz := tnumZ.tnum_add) (fz:= Z.add); auto.
  - intros.
    apply tnumZ_add_sound.tnum_add_sound; auto.
  - intros.
    apply testbit_add ; auto.
  - apply tnum_add_eq.
Qed.

Theorem tnum_sub_sound :
  forall a b i j
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    mem_tnum (Int64.sub i j) (tnum_sub a b).
Proof.
  intros.
  apply tnum_binary_sound with (tnum_fz := tnumZ.tnum_sub) (fz:= Z.sub); auto.
  - intros.
    apply tnumZ_sub_sound.tnum_sub_sound; auto.
  - intros.
    apply testbit_sub ; auto.
  - apply tnum_sub_eq.
Qed.

Theorem tnum_binary_sound_ge_0_width :
  forall a b i j f tnum_f tnum_fz fz
         (TNUM_FZ_SOUND : forall a i b j,
            tnum_ge_inv a -> tnum_ge_inv b -> gamma a i -> gamma b j -> gamma (tnum_fz a b (Z_size i)) (fz i j))
         (FFZ : forall n,  0 <= n < Int64.zwordsize ->
                           forall i j ,  (Int64.testbit (f i j) n = Z.testbit (fz (Int64.unsigned i) (Int64.unsigned j)) n))
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b)
         (EQ : tnum_f a b (Z_size (Int64.unsigned i)) = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b) (Z_size (Int64.unsigned i))))
  ,
    mem_tnum (f i j) (tnum_f a b (Z_size (Int64.unsigned i))).
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

Theorem tnum_mul_sound :
  forall a b i j
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    mem_tnum (Int64.mul i j) (tnum_mul a b (Z_size (Int64.unsigned i))).
Proof.
  intros.
  apply tnum_binary_sound_ge_0_width with (tnum_fz := tnumZ.tnum_mul) (fz:= Z.mul); auto.
  - intros.
    apply tnumZ_mul_sound.tnum_mul_sound; auto.
  - intros.
    apply testbit_mul ; auto.
  - apply tnum_mul_eq.
    rewrite Z_size_equiv.
    apply Z_size_range_Int64.
    apply Int64.unsigned_range_2.
Qed.

Theorem tnum_binary_sound_ge_0 :
  forall a b i j f tnum_f tnum_fz fz
         (TNUM_FZ_SOUND : forall a i b j,
             tnum_ge_inv a -> tnum_ge_inv b -> gamma a i -> gamma b j -> gamma (tnum_fz a b) (fz i j))
         (FFZ : forall n,  0 <= n < Int64.zwordsize ->
                           forall i j ,  (Int64.testbit (f i j) n = Z.testbit (fz (Int64.unsigned i) (Int64.unsigned j)) n))
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b)
         (EQ : tnum_f a b = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b)))
  ,
    mem_tnum (f i j) (tnum_f a b).
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
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    mem_tnum (Int64.divu i j) (tnum_udiv a b).
Proof.
  intros.
  apply tnum_binary_sound_ge_0 with (tnum_fz := tnumZ.tnum_udiv) (fz:= Z.div); auto.
  - intros.
    apply tnumZ_udiv_sound.tnum_udiv_sound; auto.
  - intros.
    apply testbit_divu ; auto.
  - apply tnum_udiv_eq; auto.
    apply (mem_tnum_range _ _ MEMA).
Qed.

Theorem tnum_umod_sound :
  forall a b i j
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
         mem_tnum (Int64.modu i j) (tnum_umod a b).
Proof.
  intros.
  apply tnum_binary_sound_ge_0 with (tnum_fz := tnumZ.tnum_umod) (fz:= Z.modulo); auto.
  - intros.
    apply tnumZ_umod_sound.tnum_umod_sound; auto.
  - intros.
    apply testbit_modu ; auto.
  - apply tnum_umod_eq; auto.
    apply (mem_tnum_range _ _ MEMA).
    apply (mem_tnum_range _ _ MEMB).
Qed.

Theorem tnum_neg_sound :
  forall a i
         (MEMA : mem_tnum i a),
    mem_tnum (Int64.neg i) (tnum_neg a).
Proof.
  intros.
  unfold tnum_neg.
  rewrite <- Int64.sub_zero_r.
  apply tnum_sub_sound.
  - unfold mem_tnum. reflexivity.
  - apply MEMA.
Qed.

Lemma tnum_unknown_gamma :
  forall i, mem_tnum i (Int64.zero, Int64.mone).
Proof.
  intros. unfold mem_tnum. simpl.
  rewrite Int64.not_mone.
  rewrite Int64.and_zero.
  reflexivity. 
Qed.

Lemma testbit_sign_pos:
  forall t,
    0 <= Int64.signed t <->
      Int64.testbit t (Int64.zwordsize - 1) = false.
Proof.
  split.
  - intros.
    unfold Int64.signed in H.
    unfold Int64.testbit.
    destruct (Coqlib.zlt _ _) as [Hl | Hl].
    + eapply Zbits.Zbits_unsigned_range with (n:= 63).
      * lia.
      * change Int64.half_modulus with (two_p 63) in Hl.
        lia.
      * change Int64.zwordsize with 64.
        lia.
    + pose proof (Int64.unsigned_range_2 t) as Heq.

      change Int64.half_modulus with 9223372036854775808 in Hl.
      change Int64.modulus with 18446744073709551616 in H.
      change Int64.max_unsigned with 18446744073709551615 in Heq.
      lia.
  - intros.
    unfold Int64.signed.
    unfold Int64.testbit in H.
    destruct (Coqlib.zlt _ _) as [Hl | Hl].
    + pose proof (Int64.unsigned_range_2 t) as Heq.
      lia.
    + rewrite Z.testbit_false in H.
      * change Int64.half_modulus with 9223372036854775808 in Hl.
        change Int64.zwordsize with 64 in H.
        change Int64.modulus with 18446744073709551616.
        lia.
      * change Int64.zwordsize with 64.
        lia.
Qed.

Lemma testbit_sign_neg:
  forall t,
    Int64.signed t < 0 <->
      Int64.testbit t (Int64.zwordsize - 1) = true.
Proof.
  split; intros.
  - unfold Int64.signed in H.
    unfold Int64.testbit.
    destruct (Coqlib.zlt _ _) as [Hl | Hl].
    + pose proof (Int64.unsigned_range_2 t) as Heq.
      lia.
    + change Int64.zwordsize with 64.
      rewrite Z.testbit_true; [| lia].
      simpl.
      change Int64.modulus with 18446744073709551616 in H.
      change Int64.half_modulus with 9223372036854775808 in Hl.
      change (Z.pow_pos 2 63) with 9223372036854775808.
      lia.
  - unfold Int64.signed.
    unfold Int64.testbit in H.
    destruct (Coqlib.zlt _ _) as [Hl | Hl].
    + rewrite Z.testbit_true in H.
      * change Int64.zwordsize with 64 in H.
        change Int64.half_modulus with 9223372036854775808 in Hl.
        lia.
      * change Int64.zwordsize with 64.
        lia.
    + pose proof (Int64.unsigned_range_2 t) as Heq.
      change Int64.max_unsigned with 18446744073709551615 in Heq.
      change Int64.modulus with 18446744073709551616.
      lia.
Qed.


Lemma Clt_Zlt_signed:
  forall ofs hi,
    Int64.lt ofs hi = true <-> Int64.signed ofs < Int64.signed hi.
Proof.
  intros.
  split; intro H.
  - unfold Int64.lt in H.
    destruct (Coqlib.zlt _ _) in H; try inversion H.
    assumption.
  - unfold Int64.lt.
    destruct (Coqlib.zlt _ _); lia.
Qed.

Lemma Clt_Zlt_signed_false:
  forall ofs hi,
    Int64.lt ofs hi = false <-> Int64.signed hi <= Int64.signed ofs.
Proof.
  intros.
  split; intro H.
  - unfold Int64.lt in H.
    destruct (Coqlib.zlt _ _) in H; try inversion H.
    lia.
  - unfold Int64.lt.
    destruct (Coqlib.zlt _ _); lia.
Qed.

Lemma tnum_msb: forall a,
  mem_tnum (Int64.repr Int64.min_signed) a ->
  Int64_msb (fst a) = true \/ Int64_msb (snd a) = true.
Proof.
  intros.
  unfold Int64_msb.
  unfold mem_tnum in *.
  rewrite <- H.
  clear. (*
  rewrite <- Int64.not_involutive with (x := Int64.repr Int64.min_signed).
  rewrite <- Int64.not_or_and_not. *)
  pose proof (Classical_Prop.classic (Int64.lt (snd a) Int64.zero = true)) as Heq.
  destruct Heq as [Heq | Heq].
  { auto. }

  left.
  apply not_true_is_false in Heq.
  remember (snd a) as t eqn: Ht.
  clear - Heq.

  rewrite Clt_Zlt_signed_false in Heq.
  rewrite Clt_Zlt_signed.
  change (Int64.signed Int64.zero) with 0 in *.
  rewrite testbit_sign_neg in *.
  rewrite testbit_sign_pos in *.

  rewrite Int64.bits_and.
  2:{ change (Int64.zwordsize) with 64. lia. }
  rewrite andb_true_iff.
  split.
  - change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
    auto.
  - rewrite Int64.bits_not.
    2:{ change (Int64.zwordsize) with 64. lia. }
    rewrite Heq.
    auto.
Qed.

Lemma tnum_union_sound:
  forall i a b,
  mem_tnum i a \/ mem_tnum i b -> mem_tnum i (tnum_union a b).
Proof.
  intros i a b Hm.
  unfold tnum_union.
  destruct a as (a_v & a_m) eqn: Ha.
  destruct b as (b_v & b_m) eqn: Hb.
  unfold mem_tnum in *.
  destruct Hm as [Hm | Hm].
  - simpl in *.
    rewrite <- Hm.
    apply Int64.same_bits_eq.
    intros n Hn.
    repeat (rewrite Int64.bits_and; [| lia]).
    repeat (rewrite Int64.bits_not; [| lia]).
    repeat (rewrite Int64.bits_or;  [| lia]).
    repeat (rewrite Int64.bits_xor; [| lia]).
    repeat (rewrite Int64.bits_and; [| lia]).
    repeat (rewrite Int64.bits_not; [| lia]).
    destruct (Int64.testbit i n); simpl; auto.
    destruct (Int64.testbit a_m n); simpl; auto.
    + rewrite orb_true_r.
      auto.
    + destruct (Int64.testbit b_v n); simpl; auto.
  - simpl in *.
    rewrite <- Hm.
    apply Int64.same_bits_eq.
    intros n Hn.
    repeat (rewrite Int64.bits_and; [| lia]).
    repeat (rewrite Int64.bits_not; [| lia]).
    repeat (rewrite Int64.bits_or;  [| lia]).
    repeat (rewrite Int64.bits_xor; [| lia]).
    repeat (rewrite Int64.bits_and; [| lia]).
    repeat (rewrite Int64.bits_not; [| lia]).
    destruct (Int64.testbit i n); simpl; auto; try lia.
    destruct (Int64.testbit a_m n); simpl; auto; try lia.
    destruct (Int64.testbit a_v n); simpl; auto; try lia.
    + destruct (Int64.testbit b_m n); simpl; auto; try lia.
    + destruct (Int64.testbit b_m n); simpl; auto; try lia.
Qed.

Lemma Int64_mone_msb : Int64_msb Int64.mone = true.
Proof. reflexivity. Qed.

Lemma Int64_zero_msb : Int64_msb Int64.zero = false.
Proof. reflexivity. Qed.

Lemma tnum_abs_ge :
  forall a, tnum_ge_inv (to_tnumZ (tnum_abs a)).
Proof.
  intros.
  unfold tnum_ge_inv, to_tnumZ, tnum_abs.
  split; simpl.
  - remember (@fst u64 u64 match Int64_msb (@fst u64 u64 a) return tnum with
            | true => tnum_neg a
            | false => a
            end) as t eqn: Ht.
    pose proof (Int64.unsigned_range_2 t) as Heq.
    lia.
  - remember (@snd u64 u64 match Int64_msb (@fst u64 u64 a) return tnum with
        | true => tnum_neg a
        | false => a
        end) as t eqn: Ht.
    pose proof (Int64.unsigned_range_2 t) as Heq.
    lia.
Qed.

Lemma mem_tnum_zero:
  forall i,
    mem_tnum i (i, Int64.zero).
Proof.
  unfold mem_tnum; intros.
  simpl.
  rewrite Int64.not_zero.
  rewrite Int64.and_mone.
  auto.
Qed.

Lemma Int64_msb_lt:
  forall b j,
  Int64_msb (fst b) = true -> mem_tnum j b -> Int64.lt j Int64.zero = true.
Proof.
  unfold Int64_msb, mem_tnum; intros.
  destruct b as (b_v & b_m).
  simpl in *.
  rewrite <- H0 in H.
  
  rewrite Clt_Zlt_signed in *.
  change (Int64.signed Int64.zero) with 0 in *.
  rewrite testbit_sign_neg in *.

  rewrite Int64.bits_and in H.
  2:{ change (Int64.zwordsize) with 64. lia. }
  rewrite Int64.bits_not in *.
  2:{ change (Int64.zwordsize) with 64. lia. }
  rewrite andb_true_iff in H.
  destruct H; auto.
Qed.

Lemma Int64_divs_eq:
  forall i j
  (Hi_neg : Int64.lt i Int64.zero = true)
  (Hj_neg : Int64.lt j Int64.zero = true),
  Int64.divs i j = Int64.divu (Int64.neg i) (Int64.neg j).
Proof.
  intros.
  rewrite Clt_Zlt_signed in *.
  change (Int64.signed Int64.zero) with 0 in *.
  apply Int64.same_bits_eq.
  intros n Hi.
  rewrite testbit_divu; [| auto].
  unfold Int64.divs.
  unfold Int64.testbit.
  rewrite <- Int64.repr_signed with (i := i) at 2.
  rewrite <- Int64.repr_signed with (i := j) at 2.
  rewrite ! Int64.neg_repr.
  rewrite <- Zquot.Zquot_opp_opp.
  rewrite Int64.unsigned_repr.
  2:{
    split.
    - apply Zquot.Z_quot_pos; lia.
    - pose proof (Int64.signed_range i) as Hl1.
      pose proof (Int64.signed_range j) as Hl2.
      change Int64.max_unsigned with 18446744073709551615 in *.
      change Int64.min_signed with (- 9223372036854775808) in *.
      lia.
  } 
  rewrite Int64.unsigned_repr with (z := (- Int64.signed i)).
  2:{
    split.
    - lia.
    - pose proof (Int64.signed_range i) as Hl1.
      change Int64.max_unsigned with 18446744073709551615 in *.
      change Int64.min_signed with (- 9223372036854775808) in *.
      lia.
  } 
  rewrite Int64.unsigned_repr with (z := (- Int64.signed j)).
  2:{
    split.
    - lia.
    - pose proof (Int64.signed_range j) as Hl1.
      change Int64.max_unsigned with 18446744073709551615 in *.
      change Int64.min_signed with (- 9223372036854775808) in *.
      lia.
  } 
  rewrite Zquot.Zquot_Zdiv_pos; try lia.
  rewrite Z.div_opp_opp; try lia.
  auto.
Qed.

Lemma Int64_eq_false: forall x y : int64, Int64.eq x y = false -> x <> y.
Proof.
  intros.
  intro HF.
  subst x.
  rewrite Int64.eq_true in H.
  lia.
Qed.

(*
Lemma Int64_divs_eq1:
  forall i j
  (Hi_neg : Int64.lt i Int64.zero = true)
  (Hj_neg : Int64.lt j Int64.zero = false)
  (Hj_neg1 : Int64.eq j Int64.zero = false),
  Int64.divs i j = Int64.neg (Int64.divu (Int64.neg i) j).
Proof.
  intros.
  rewrite Clt_Zlt_signed in *.
  rewrite Clt_Zlt_signed_false in *.
  change (Int64.signed Int64.zero) with 0 in *.
  apply Int64_eq_false in Hj_neg1.
  assert (Ht: Int64.signed j <> 0).
  {
    intro HF. apply Hj_neg1.
    unfold Int64.signed in HF.
    destruct (Coqlib.zlt (Int64.unsigned j)) eqn: Heq.
    - apply Int64.same_bits_eq.
      intros n Hn.
      unfold Int64.testbit, Int64.zero.
      rewrite HF.
      auto.
    - rewrite Z.sub_move_0_r in HF.
      apply Int64.same_bits_eq.
      intros n Hn.
      unfold Int64.testbit, Int64.zero.
      rewrite HF.
      change Int64.modulus with (2^64).
      change (Int64.unsigned (Int64.repr 0)) with 0.
      rewrite Z.bits_0.
      rewrite Z.pow2_bits_false.
      auto.
      change (Int64.zwordsize) with 64 in Hn; lia.
  }
  
  apply Int64.same_bits_eq.
  intros n Hi.
  rewrite Int64.bits_neg.
  rewrite testbit_divu; [| auto].
  unfold Int64.divs.
  unfold Int64.testbit.
  rewrite <- Int64.repr_signed with (i := i) at 2.
  rewrite <- Int64.repr_signed with (i := j) at 2.
  rewrite ! Int64.neg_repr. ../..
  rewrite <- Zquot.Zquot_opp_opp.
  rewrite Int64.unsigned_repr.
  2:{
    split.
    - rewrite Zquot.Zquot_opp_opp.
      Search (_ ÷ _).
      apply Zquot.Z_quot_pos; try lia.
    - pose proof (Int64.signed_range i) as Hl1.
      pose proof (Int64.signed_range j) as Hl2.
      change Int64.max_unsigned with 18446744073709551615 in *.
      change Int64.min_signed with (- 9223372036854775808) in *.
      lia.
  } 
  rewrite Int64.unsigned_repr with (z := (- Int64.signed i)).
  2:{
    split.
    - lia.
    - pose proof (Int64.signed_range i) as Hl1.
      change Int64.max_unsigned with 18446744073709551615 in *.
      change Int64.min_signed with (- 9223372036854775808) in *.
      lia.
  } 
  rewrite Int64.unsigned_repr with (z := (- Int64.signed j)).
  2:{
    split.
    - lia.
    - pose proof (Int64.signed_range j) as Hl1.
      change Int64.max_unsigned with 18446744073709551615 in *.
      change Int64.min_signed with (- 9223372036854775808) in *.
      lia.
  } 
  rewrite Zquot.Zquot_Zdiv_pos; try lia.
  rewrite Z.div_opp_opp; try lia.
  auto.
Qed.

Lemma tnum_udiv_1 :
  forall a, tnum_udiv a (Int64.one, Int64.zero) = a.
Proof.
  (* intros. destruct a as [a_v a_m]. unfold tnum_udiv. simpl.
  change (Int64.eq Int64.one Int64.zero) with false. simpl.
  change (Int64.eq Int64.zero Int64.zero) with true.
  destruct (Int64.eq a_m Int64.zero) eqn:Ha_m0.
  - apply Int64.same_if_eq in Ha_m0. simpl.
    rewrite Int64.divu_one. rewrite <- Ha_m0.
    reflexivity.
  - simpl.   *)
Admitted.
*)

Lemma mem_tnum_min_signed_iff:
  forall a,
  mem_tnum (Int64.repr Int64.min_signed) a <-> 
  mem_tnum (Int64.repr (2 ^ 63)) a.
Proof.
  unfold mem_tnum.
  split; intros H.
  - rewrite <- H.
    apply Int64.same_bits_eq.
    intros i Hi.
    rewrite Int64.bits_and; [| auto].
    rewrite Int64.bits_and; [| auto].
    destruct (Int64.testbit (Int64.not (snd a)) i).
    2:{ rewrite ! andb_false_r. auto. }
    rewrite ! andb_true_r.
    rewrite Int64.testbit_repr; [| auto].
    rewrite Int64.testbit_repr; [| auto].
    rewrite Z.pow2_bits_eqb; [| lia].
    change Int64.min_signed with (- two_p 63).
    rewrite Zbits.Ztestbit_neg_two_p; try lia.
    change Int64.zwordsize with 64 in Hi.
    destruct (Coqlib.zlt _ _); try lia.
  - rewrite <- H.
    apply Int64.same_bits_eq.
    intros i Hi.
    rewrite Int64.bits_and; [| auto].
    rewrite Int64.bits_and; [| auto].
    destruct (Int64.testbit (Int64.not (snd a)) i).
    2:{ rewrite ! andb_false_r. auto. }
    rewrite ! andb_true_r.
    rewrite Int64.testbit_repr; [| auto].
    rewrite Int64.testbit_repr; [| auto].
    rewrite Z.pow2_bits_eqb; [| lia].
    change Int64.min_signed with (- two_p 63).
    rewrite Zbits.Ztestbit_neg_two_p; try lia.
    change Int64.zwordsize with 64 in Hi.
    destruct (Coqlib.zlt _ _); try lia.
Qed.

Lemma Int64_unsigned_ge_0:
  forall i,
  0 <= Int64.unsigned i.
Proof.
  intros.
  pose proof (Int64.unsigned_range_2 i).
  lia.
Qed.

Lemma tnum_known_eq:
  forall j b,
    mem_tnum j b ->
    (snd b) = Int64.zero ->
      fst b = j.
Proof.
  intros.
  unfold mem_tnum in *.
  rewrite H0 in H.
  rewrite Int64.not_zero in H.
  rewrite Int64.and_mone in H.
  auto.
Qed.

Definition mem_tnum_opt (i: int64) (oa: option tnum) : Prop :=
  match oa with
  | Some a => mem_tnum i a
  | None => False
  end.

Theorem tnum_union_opt_sound :
  forall i a b,
  mem_tnum_opt i a \/ mem_tnum_opt i b -> mem_tnum_opt i (tnum_union_opt a b).
Proof.
  intros i oa ob H.
  unfold tnum_union_opt.
  destruct oa as [a|]; destruct ob as [b|]; simpl in *.
  - apply tnum_union_sound. exact H.
  - destruct H; auto; contradiction.
  - destruct H; auto; contradiction.
  - destruct H; contradiction.
Qed.

Lemma tnum_get_positive_sound :
  forall i a a_pos,
    mem_tnum i a ->
    Int64.signed i >= 0 ->
    tnum_get_positive a = Some a_pos ->
    mem_tnum i a_pos.
Proof.
  intros i a a_pos Hmem Hsign Hpos.
  unfold tnum_get_positive in Hpos.
  destruct a as [v m].
  destruct (Int64_msb v) eqn:Hmsbv.
  - discriminate Hpos.
  - destruct (Int64_msb m) eqn:Hmsbm.
    + injection Hpos as <-.
      unfold mem_tnum in *. simpl in *.
      rewrite <- Hmem.
      apply Int64.same_bits_eq. intros n Hn.
      repeat (rewrite Int64.bits_and; [| lia]).
      destruct (Int64.testbit i n) eqn:Hbit_i.
      * repeat (rewrite Int64.bits_not; [| lia]).
        f_equal.
        rewrite Int64.bits_and; [| lia].
        rewrite Int64.bits_not; [| lia].
        unfold Int64_min_signed.
        rewrite Int64.testbit_repr; [| auto].
        assert (Hlt: n < 63 \/ n = 63).
        { change Int64.zwordsize with 64 in Hn; lia. }
        destruct Hlt as [Hlt | Heq].
        --change Int64.min_signed with (- two_p 63).
          rewrite Zbits.Ztestbit_neg_two_p; try lia.
          destruct (Coqlib.zlt n 63).
          ++ simpl. rewrite andb_true_r. reflexivity.
          ++ lia.
        --subst n.
          assert (Hsign_le : 0 <= Int64.signed i) by lia.
          apply testbit_sign_pos in Hsign_le.
          change (Int64.zwordsize - 1) with 63 in Hsign_le.
          rewrite Hsign_le in Hbit_i. discriminate.
      * reflexivity.
    + injection Hpos as <-.
      exact Hmem.
Qed.

Lemma tnum_get_negative_sound :
  forall i a a_neg,
    mem_tnum i a ->
    Int64.signed i < 0 ->
    tnum_get_negative a = Some a_neg ->
    mem_tnum i a_neg.
Proof.
  intros i a a_neg Hmem Hsign Hneg.
  unfold tnum_get_negative in Hneg.
  destruct a as [v m].
  destruct (Int64_msb v) eqn:Hmsbv.
  - injection Hneg as <-.
    exact Hmem.
  - destruct (Int64_msb m) eqn:Hmsbm.
    + injection Hneg as <-.
      unfold mem_tnum in *. simpl in *.
      rewrite <- Hmem.
      apply Int64.same_bits_eq. intros n Hn.
      repeat (
        (rewrite Int64.bits_and; [| lia]) ||
        (rewrite Int64.bits_or;  [| lia]) ||
        (rewrite Int64.bits_not; [| lia])
      ).
      unfold Int64_min_signed.
      rewrite Int64.testbit_repr; [| auto].
      destruct (Int64.testbit i n) eqn:Hbit_i.
      *
        assert (Hlt: n < 63 \/ n = 63).
        { change Int64.zwordsize with 64 in Hn; lia. }
        destruct Hlt as [Hlt | Heq].
        --
          change Int64.min_signed with (- two_p 63).
          rewrite Zbits.Ztestbit_neg_two_p; try lia.
          destruct (Coqlib.zlt n 63); try lia.
          simpl. rewrite andb_true_r. rewrite orb_false_r. reflexivity.
        --
          subst n.
          change Int64.min_signed with (- two_p 63).
          rewrite Zbits.Ztestbit_neg_two_p; try lia.
          destruct (Coqlib.zlt 63 63); try lia.
      *
        assert (Hlt: n < 63 \/ n = 63).
        { change Int64.zwordsize with 64 in Hn; lia. }
        destruct Hlt as [Hlt | Heq].
        --
          change Int64.min_signed with (- two_p 63).
          rewrite Zbits.Ztestbit_neg_two_p; try lia.
          destruct (Coqlib.zlt n 63); try lia.
        --
          subst n.
          assert (Hsign_neg : Int64.signed i < 0) by lia.
          apply testbit_sign_neg in Hsign_neg.
          change (Int64.zwordsize - 1) with 63 in Hsign_neg.
          rewrite Hsign_neg in Hbit_i. discriminate.
    + discriminate Hneg.
Qed.

Lemma calc_pos_pos_sound: forall a b i j a_pos b_pos res,
  mem_tnum i a -> mem_tnum j b ->
  Int64.signed i >= 0 -> Int64.signed j >= 0 ->
  tnum_get_positive a = Some a_pos ->
  tnum_get_positive b = Some b_pos ->
  calc_pos_pos_opt (Some a_pos) (Some b_pos) = Some res -> 
  mem_tnum (Int64.divs i j) res.
Proof.
  intros a b i j a_pos b_pos res Hmem_a Hmem_b Hsign_i Hsign_j Hpos_a Hpos_b Hcalc.
  unfold calc_pos_pos_opt in Hcalc.
  injection Hcalc as <-.
  assert (H_div: Int64.divs i j = Int64.divu i j).
  {
    unfold Int64.divs, Int64.divu.
    assert (Hui: Int64.unsigned i = Int64.signed i).
    { 
      unfold Int64.signed in *. 
      pose proof (Int64.unsigned_range i).
      destruct (Coqlib.zlt (Int64.unsigned i) Int64.half_modulus); lia. 
    }
    assert (Huj: Int64.unsigned j = Int64.signed j).
    { 
      unfold Int64.signed in *. 
      pose proof (Int64.unsigned_range j).
      destruct (Coqlib.zlt (Int64.unsigned j) Int64.half_modulus); lia. 
    }
    rewrite Hui, Huj.
    destruct (Int64.signed j) eqn:Hj_val.
    - reflexivity. 
    - f_equal. apply Zquot.Zquot_Zdiv_pos; lia. 
    - lia. 
  }
  rewrite H_div.
  apply tnum_udiv_sound.
  - unfold tnum_ge_inv, to_tnumZ. split; simpl; apply Int64_unsigned_ge_0.
  - unfold tnum_ge_inv, to_tnumZ. split; simpl; apply Int64_unsigned_ge_0.
  - eapply tnum_get_positive_sound; eauto.
  - eapply tnum_get_positive_sound; eauto.
Qed.

Lemma calc_neg_neg_sound: forall a b i j a_neg b_neg res,
  mem_tnum i a -> mem_tnum j b ->
  Int64.signed i < 0 -> Int64.signed j < 0 ->
  tnum_get_negative a = Some a_neg ->
  tnum_get_negative b = Some b_neg ->
  calc_neg_neg_opt (Some a_neg) (Some b_neg) = Some res -> 
  mem_tnum (Int64.divs i j) res.
Proof.
  intros a b i j a_neg b_neg res Hmem_a Hmem_b Hsign_i Hsign_j Hneg_a Hneg_b Hcalc.
  unfold calc_neg_neg_opt in Hcalc.
  destruct (Int64.eq (get_signed_min a_neg) Int64_min_signed && Int64.eq (get_signed_max b_neg) Int64.mone) eqn:Heq.
  - injection Hcalc as <-. apply tnum_unknown_gamma.
  - injection Hcalc as <-.
    unfold mem_tnum. simpl.
    assert (Hmem_a_neg: mem_tnum i a_neg) by (eapply tnum_get_negative_sound; eauto).
    assert (Hmem_b_neg: mem_tnum j b_neg) by (eapply tnum_get_negative_sound; eauto).
    apply Int64.same_bits_eq; intros n Hn.
    rewrite Int64.bits_and by lia.
    rewrite Int64.bits_zero.
    destruct (Int64.testbit (Int64.divs i j) n) eqn:Hbit.
    + rewrite Int64.bits_not by lia.
      unfold Int64_ones, Int64_size.
      rewrite Int64.testbit_repr by auto.
      destruct (Coqlib.zlt n (Z_size_Z (Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))))).
      * rewrite Z.ones_spec_low by lia. auto.
      * exfalso.
        unfold Int64.testbit in Hbit.
        assert (H_bit_false: Z.testbit (Int64.unsigned (Int64.divs i j)) n = false).
        {
          apply Z.testbit_false; try lia.
          assert (H_bound: Int64.unsigned (Int64.divs i j) < 2 ^ n).
          {
            assert (H_le: Int64.unsigned (Int64.divs i j) <= Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))).
            {
              assert (H_i_min: Int64.signed (get_signed_min a_neg) <= Int64.signed i).
              {
                unfold get_signed_min.
                assert (H_ub: Int64.unsigned (fst a_neg) <= Int64.unsigned i).
                {
                  pose proof Hmem_a_neg as Hmem. unfold mem_tnum in Hmem.
                  rewrite <- Hmem. rewrite <- Zland_and.
                  apply land_ub; apply Int64.unsigned_range.
                }
                assert (H_sign: Int64.signed (fst a_neg) < 0).
                { 
                  unfold tnum_get_negative in Hneg_a. destruct a as [v m]. destruct (Int64_msb v) eqn:Hv.
                  - injection Hneg_a as <-. unfold Int64_msb in Hv. rewrite Clt_Zlt_signed in Hv. change (Int64.signed Int64.zero) with 0 in Hv. auto.
                  - destruct (Int64_msb m) eqn:Hm. 
                    + injection Hneg_a as <-. simpl. apply testbit_sign_neg. rewrite Int64.bits_or by lia. 
                      rewrite orb_true_iff. right. unfold Int64_min_signed. change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true. auto.
                    + discriminate. 
                }
                unfold Int64.signed in *. pose proof (Int64.unsigned_range (fst a_neg)).
                pose proof (Int64.unsigned_range i).
                unfold Int64.signed in *. 
                destruct (Coqlib.zlt (Int64.unsigned (fst a_neg)) Int64.half_modulus); 
                destruct (Coqlib.zlt (Int64.unsigned i) Int64.half_modulus); lia.
              }
              assert (H_j_max: Int64.signed j <= Int64.signed (get_signed_max b_neg)).
              {
                unfold get_signed_max. 
                assert (H_or_eq: Int64.or (fst b_neg) (snd b_neg) = Int64.or j (snd b_neg)).
                { 
                  pose proof Hmem_b_neg as Hmem. unfold mem_tnum in Hmem. rewrite <- Hmem. apply Int64.same_bits_eq. intros n0 Hn0.
                  rewrite !Int64.bits_or, Int64.bits_and, Int64.bits_not by auto. destruct (Int64.testbit j n0), (Int64.testbit (snd b_neg) n0); auto. 
                }
                rewrite H_or_eq. 
                
                assert (Hlor_j: Int64.unsigned j <= Int64.unsigned (Int64.or j (snd b_neg))).
                {
                  assert (H_not_or: Int64.not (Int64.or j (snd b_neg)) = Int64.and (Int64.not j) (Int64.not (snd b_neg))).
                  { apply Int64.same_bits_eq; intros n0 Hn0.
                    rewrite Int64.bits_not, Int64.bits_and, !Int64.bits_not, Int64.bits_or by auto.
                    destruct (Int64.testbit j n0), (Int64.testbit (snd b_neg) n0); auto. }
                  
                  pose proof (Int64.unsigned_not j) as Hnot_j.
                  pose proof (Int64.unsigned_not (Int64.or j (snd b_neg))) as Hnot_or.
                  
                  rewrite H_not_or in Hnot_or. 
                  rewrite <- Zland_and in Hnot_or.
                  
                  pose proof (land_ub (Int64.unsigned (Int64.not j)) (Int64.unsigned (Int64.not (snd b_neg)))).
                  pose proof (Int64.unsigned_range (Int64.not j)).
                  pose proof (Int64.unsigned_range (Int64.not (snd b_neg))).
                  lia.
                }

                assert (H_sign: Int64.signed (Int64.or j (snd b_neg)) < 0).
                { apply testbit_sign_neg. rewrite Int64.bits_or by lia. apply testbit_sign_neg in Hsign_j. rewrite Hsign_j. auto. }
                
                unfold Int64.signed in *.
                pose proof (Int64.unsigned_range j).
                pose proof (Int64.unsigned_range (Int64.or j (snd b_neg))).
                
                unfold Int64.signed in *.
                destruct (Coqlib.zlt (Int64.unsigned j) Int64.half_modulus); 
                destruct (Coqlib.zlt (Int64.unsigned (Int64.or j (snd b_neg))) Int64.half_modulus); 
                lia.
              }
              assert (H_j_max_neg: Int64.signed (get_signed_max b_neg) < 0).
              {
                unfold get_signed_max.
                assert (H_or_eq: Int64.or (fst b_neg) (snd b_neg) = Int64.or j (snd b_neg)).
                { 
                  pose proof Hmem_b_neg as Hmem. unfold mem_tnum in Hmem. rewrite <- Hmem. apply Int64.same_bits_eq. intros n0 Hn0.
                  rewrite !Int64.bits_or, Int64.bits_and, Int64.bits_not by auto. destruct (Int64.testbit j n0), (Int64.testbit (snd b_neg) n0); auto. 
                }
                rewrite H_or_eq.
                apply testbit_sign_neg. rewrite Int64.bits_or by lia. 
                apply testbit_sign_neg in Hsign_j. rewrite Hsign_j. auto.
              }
              assert (H_div_mono: forall n1 d1 n2 d2, 0 <= n1 <= n2 -> 0 < d2 <= d1 -> n1 / d1 <= n2 / d2).
              {
                intros n1 d1 n2 d2 Hnum Hden.
                apply Z.le_trans with (m := n2 / d1).
                - apply Z.div_le_mono; lia.
                - apply Z.div_le_compat_l; lia.
              }

              assert (H_neg_unsigned: forall x, Int64.signed x < 0 -> Int64.unsigned (Int64.neg x) = - Int64.signed x).
              {
                intros x Hx. 
                pose proof (Int64.unsigned_range x).
                unfold Int64.signed in *.
                destruct (Coqlib.zlt (Int64.unsigned x) Int64.half_modulus); try lia. 
                unfold Int64.neg. rewrite Int64.unsigned_repr_eq.
                replace (- Int64.unsigned x) with (Int64.modulus - Int64.unsigned x + (-1) * Int64.modulus) by lia.
                rewrite Z.mod_add by (change Int64.modulus with 18446744073709551616; lia).
                rewrite Z.mod_small.
                - lia.
                - change Int64.modulus with 18446744073709551616 in *.
                  change Int64.half_modulus with 9223372036854775808 in *.
                  lia.
              }

              assert (H_i_min_neg: Int64.signed (get_signed_min a_neg) < 0) by lia.
              
              assert (H_divs_i_j: Int64.divs i j = Int64.divu (Int64.neg i) (Int64.neg j)).
              { apply Int64_divs_eq; rewrite Clt_Zlt_signed; change (Int64.signed Int64.zero) with 0; lia. }
              
              assert (H_divs_ab: Int64.divs (get_signed_min a_neg) (get_signed_max b_neg) = Int64.divu (Int64.neg (get_signed_min a_neg)) (Int64.neg (get_signed_max b_neg))).
              { apply Int64_divs_eq; rewrite Clt_Zlt_signed; change (Int64.signed Int64.zero) with 0; lia. }
              
              rewrite H_divs_i_j, H_divs_ab. 
              unfold Int64.divu.
              
              rewrite !H_neg_unsigned by auto.
              
              assert (H_repr_div: forall x y, 0 <= x <= Int64.max_unsigned -> 0 < y -> Int64.unsigned (Int64.repr (x / y)) = x / y).
              {
                intros x y Hx Hy. apply Int64.unsigned_repr.
                split.
                - apply Z.div_pos; lia.
                - apply Z.le_trans with (m := x / 1).
                  + apply Z.div_le_compat_l; lia.
                  + rewrite Zdiv_1_r. lia.
              }
      
              pose proof (Int64.signed_range i).
              pose proof (Int64.signed_range j).
              pose proof (Int64.signed_range (get_signed_min a_neg)).
              pose proof (Int64.signed_range (get_signed_max b_neg)).
              
              change Int64.max_unsigned with 18446744073709551615 in *.
              change Int64.min_signed with (-9223372036854775808) in *.
              change Int64.max_signed with 9223372036854775807 in *.
              
              rewrite !H_repr_div by lia.
              
              apply H_div_mono; lia.
            }
            
            apply Z.le_lt_trans with (m := Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))).
            - apply H_le.
            - assert (H_size_prop: Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg)) < 2 ^ (Z_size_Z (Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))))).
              {
                unfold Z_size_Z.
                destruct (Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))) eqn:Hval.
                - simpl. lia.
               - pose proof (Z.log2_spec (Z.pos p) eq_refl) as Hlog.
                rewrite Z.abs_eq by lia. 
                replace (Z.log2 (Z.pos p) + 1) with (Z.succ (Z.log2 (Z.pos p))) by lia.
                lia.
                - pose proof (Int64.unsigned_range (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))).
                  lia.
              }
              apply Z.lt_le_trans with (m := 2 ^ (Z_size_Z (Int64.unsigned (Int64.divs (get_signed_min a_neg) (get_signed_max b_neg))))).
              + apply H_size_prop.
              + apply Z.pow_le_mono_r; lia.
          }
          rewrite Z.div_small; try lia.
          split.
          -- apply Int64_unsigned_ge_0.
          -- apply H_bound.
        }
        rewrite H_bit_false in Hbit.
        discriminate Hbit.
    + reflexivity.
Qed.
(*
Theorem tnum_sdiv_sound :
  forall a b i j
    (H_dst: gamma_val i a)
    (H_src: gamma_val j b),
  gamma_val (eval_div_s64 i j) (tnum_sdiv a b).
Proof.
  intros.
  destruct i as [ | | i | | | ]; simpl in H_dst; try contradiction.
  destruct j as [ | | j | | | ]; simpl in H_src; try contradiction.
  unfold tnum_sdiv.
  rewrite (surjective_pairing a), (surjective_pairing b).
  unfold gamma_val.
  destruct (Int64.eq (snd b) Int64.zero) eqn: Hb_m.
  {
    apply Int64.same_if_eq in Hb_m.
    apply tnum_known_eq in H_src as Hb_eq; auto.
    destruct (Int64.eq (fst b) Int64.zero) eqn: Hb_v.
    - apply Int64.same_if_eq in Hb_v.
      rewrite Hb_eq in *.
      subst j.
      rewrite Hb_v in *.
      unfold eval_div_s64; simpl.
      rewrite Int64.eq_true.
      simpl.
      destruct (Val.eq (Vlong Int64.zero) (Vlong Int64.zero)) as [Heq | Heq].
      + unfold mem_tnum.
        rewrite Int64.and_zero_l.
        simpl.
        auto.
      + exfalso.
        apply Heq; auto.
    - destruct (Int64.eq (snd a) Int64.zero) eqn: Ha_m.
      + destruct (Int64.eq (fst a) Int64_min_signed && Int64.eq (fst b) Int64.mone) eqn: Hm.
        * rewrite andb_true_iff in Hm.
          destruct Hm as (Ha_v & Hb_a).
          apply Int64.same_if_eq in Ha_v, Hb_a, Ha_m.
          unfold mem_tnum in *.
          rewrite Ha_v in *.
          rewrite Ha_m in *.
          rewrite Hb_a in *.
          rewrite Hb_m in *.
          rewrite Int64.not_zero in *.
          rewrite Int64.and_mone in *.
          subst j.
          subst i.
          unfold eval_div_s64; simpl.
          change (Int64.eq Int64.mone Int64.zero) with false.
          simpl.
          unfold Int64_min_signed.
          change (Int64.eq (Int64.repr Int64.min_signed) (Int64.repr Int64.min_signed) && Int64.eq Int64.mone Int64.mone) with true.
          simpl.
          destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.zero)) as [Heq | Heq].
          {
            inversion Heq.
          }
          clear Heq.

          destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [Heq | Heq].
          2:{ exfalso. apply Heq; auto. }
          simpl.
          clear Heq.

          unfold LLONG_MIN.
          destruct (Val.eq (Vlong (Int64.repr Int64.min_signed)) (Vlong (Int64.repr Int64.min_signed))) as [Heq | Heq].
          2:{ exfalso. apply Heq; auto. }
          simpl.
          clear Heq.
          
          rewrite Int64.not_zero.
          rewrite Int64.and_mone.
          auto.
        * apply Int64.same_if_eq in Ha_m.
          unfold mem_tnum in H_dst.
          rewrite Ha_m in H_dst.
          rewrite Int64.not_zero in *.
          rewrite Int64.and_mone in *.
          subst i.
          rewrite andb_false_iff in Hm.
          unfold eval_div_s64; simpl.
          assert (Heq: Int64.eq j Int64.zero || Int64.eq (fst a) (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone = false).
          { rewrite orb_false_iff.
            unfold Int64_min_signed, mem_tnum  in *.
            rewrite Hb_m in H_src.
            rewrite Int64.not_zero in *.
            rewrite Int64.and_mone in *.
            subst j.
            rewrite Hb_v.
            split; auto.
            destruct Hm as [Hm | Hm].
            - rewrite Hm.
              auto.
            - rewrite Hm.
              lia.
          }
          rewrite Heq; clear Heq.

          subst j.
          apply mem_tnum_zero.
        + unfold eval_div_s64; simpl.
          destruct (Int64.eq j Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone) eqn: Hm.
          * destruct (Val.eq (Vlong j) (Vlong Int64.zero)) as [Hj | Hj].
            { exfalso.
              inversion Hj.
              unfold mem_tnum in H_src.
              rewrite H0 in *.
              rewrite Int64.and_zero_l in H_src.
              rewrite Hb_eq in Hb_v.
              rewrite Int64.eq_true in Hb_v.
              lia.
            }

            rewrite orb_true_iff in Hm.
            destruct Hm as [Hm | Hm].
            { exfalso. apply Hj. f_equal. apply Int64.same_if_eq in Hm. auto. }

            rewrite andb_true_iff in *.
            destruct Hm as (Hm1 & Hm2).
            apply Int64.same_if_eq in Hm1, Hm2.
            assert (Heq: Coqlib.proj_sumbool (Val.eq (Vlong j) (Vlong Int64.mone)) && Coqlib.proj_sumbool (Val.eq (Vlong i) LLONG_MIN) = true).
            {
              rewrite andb_true_iff in *.
              rewrite Hm1, Hm2.
              destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [Heq | Heq].
              - simpl.
                split; auto.
              - exfalso. apply Heq; auto.
            }
            rewrite Heq; clear Heq.

            unfold LLONG_MIN.
            rewrite Hb_eq.
            rewrite Hb_m.
            rewrite Hm2.
            unfold tnum_sdiv_common; simpl.
            destruct (Int64_msb (fst a)) eqn: Hlt.
            {
              rewrite Int64_mone_msb.
              unfold tnum_union_opt.
              unfold tnum_sdiv_helper; simpl.
              rewrite Hlt. rewrite Int64_mone_msb. simpl.
              change (tnum_abs (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
              rewrite <- (Int64.divu_one (Int64.repr Int64.min_signed)).
              assert (Heq: a = (fst a, snd a)). { destruct a; simpl; auto. }
              rewrite <- Heq; clear Heq.
              apply tnum_udiv_sound.
              { apply tnum_abs_ge. }

              {
                unfold tnum_ge_inv, to_tnumZ, tnum_abs.
                split; simpl.
                - change (Int64.unsigned Int64.one) with 1.
                  lia.
                - change (Int64.unsigned Int64.zero) with 0.
                  lia.
              }

              {
                unfold tnum_abs.
                rewrite Hlt.
                rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
                apply tnum_neg_sound.
                unfold Int64_msb in Hlt.
                change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
                rewrite Hm1 in H_dst.
                auto.
              }

              {
                unfold mem_tnum.
                simpl.
                change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
                auto.
              }
            }
            
            destruct (Int64_msb (snd a)) eqn: Hlt1.
            { rewrite Int64_mone_msb. simpl.
              unfold tnum_sdiv_helper; simpl.
              rewrite Int64_mone_msb. simpl.
              change (tnum_abs (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
              assert (Heq: (Int64_msb (Int64.or (fst a) Int64_min_signed)) = true).
              { unfold Int64_msb in *.
                rewrite Clt_Zlt_signed_false in *.
                rewrite Clt_Zlt_signed in *.
                change (Int64.signed Int64.zero) with 0 in *.
                rewrite testbit_sign_pos in *.
                rewrite testbit_sign_neg in *.
                rewrite Int64.bits_or.
                2:{ change (Int64.zwordsize) with 64; lia. }
                rewrite orb_true_iff.
                right.
                change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                auto.
              }
              rewrite Heq; clear Heq.

              simpl.
              rewrite Hlt. simpl.

              apply tnum_union_sound.

              left.
              rewrite <- (Int64.divu_one (Int64.repr Int64.min_signed)).
              apply tnum_udiv_sound.
              - apply tnum_abs_ge.
              - unfold tnum_ge_inv, to_tnumZ, tnum_abs.
                split; simpl.
                + change (Int64.unsigned Int64.one) with 1.
                  lia.
                + change (Int64.unsigned Int64.zero) with 0.
                  lia.
              - unfold tnum_abs; simpl.
                assert (Heq: Int64_msb (Int64.or (fst a) Int64_min_signed) = true).
                { 
                  unfold Int64_msb, Int64_min_signed in *.
                  rewrite Clt_Zlt_signed_false in *.
                  rewrite Clt_Zlt_signed in *.
                  change (Int64.signed Int64.zero) with 0 in *.
                  rewrite testbit_sign_pos in *.
                  rewrite testbit_sign_neg in *.
                  rewrite Int64.bits_or.
                  2:{ change (Int64.zwordsize) with 64; lia. }
                  rewrite orb_true_iff.
                  right.
                  change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                  auto.
                }
                rewrite Heq; clear Heq.
                
                rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
                apply tnum_neg_sound.
                change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
                unfold mem_tnum in *.
                rewrite <- H_dst in *.
                simpl in *.
                rewrite Int64.not_and_or_not.
                rewrite Int64.not_involutive.
                rewrite <- Int64.and_commut with (x:= Int64.not (snd a)).
                rewrite Int64.or_and_distrib_l.
                unfold Int64_min_signed.
                rewrite Int64.and_commut. 
                rewrite Hm1.
                rewrite Int64.or_idem.
                auto.
              - unfold mem_tnum.
                simpl.
                change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
                auto.
            }

            rewrite Int64_mone_msb. simpl.
            unfold tnum_sdiv_helper; simpl.
            rewrite Hlt.
            rewrite Int64_mone_msb. simpl.
            
            rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
            apply tnum_neg_sound.
            change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
            (*
            change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).

            rewrite mem_tnum_min_signed_iff. *)
            replace (Int64.repr Int64.min_signed) with (Int64.divu (Int64.repr Int64.min_signed) Int64.one).
            2:{ rewrite Int64.divu_one. auto. }
            eapply tnum_udiv_sound.
            { apply tnum_abs_ge. }
            { unfold tnum_ge_inv, to_tnumZ, tnum_abs, tnum_neg.
              split; simpl.
              + apply Int64_unsigned_ge_0.
              + apply Int64_unsigned_ge_0.
            }
            { (* rewrite <- mem_tnum_min_signed_iff. *)
              unfold tnum_abs; simpl.
              rewrite Hlt.
              rewrite Hm1 in H_dst.
              unfold mem_tnum in *.
              simpl.
              auto.
            }
            { unfold tnum_abs.
              simpl.
              rewrite Int64_mone_msb. simpl.
              change (tnum_neg (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
              unfold mem_tnum.
              simpl.
              change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
              auto.
            }
             
          * rewrite orb_false_iff in Hm.
            destruct Hm as (Hm1 & Hm2).
            rewrite andb_false_iff in Hm2.
            unfold tnum_sdiv_common; simpl.
            destruct (Int64_msb (fst a)) eqn: Hlt.
            {
              destruct (Int64_msb (fst b)) eqn: Hlt1.
              { unfold tnum_union_opt; simpl.
                unfold tnum_sdiv_helper; simpl.
                rewrite Hlt, Hlt1.
                simpl.
                (** Here we know i and j are negitive because of Int64_msb (fst a) = true /\ Int64_msb (fst b) = true *)
                assert (Hi_neg: Int64.lt i Int64.zero = true).
                { apply Int64_msb_lt with (b:= a); eauto. }
                assert (Hj_neg: Int64.lt j Int64.zero = true).
                { apply Int64_msb_lt with (b:= b); eauto. }

                assert (Heq: Int64.divs i j = Int64.divu (Int64.neg i) (Int64.neg j)).
                {  apply Int64_divs_eq; auto. }
                rewrite Heq; clear Heq.

                eapply tnum_udiv_sound.
                - apply tnum_abs_ge.
                - unfold tnum_ge_inv, to_tnumZ, tnum_abs, tnum_neg.
                  split; simpl.
                  + apply Int64_unsigned_ge_0.
                  + apply Int64_unsigned_ge_0.
                - (* rewrite <- mem_tnum_min_signed_iff. *)
                  unfold tnum_abs; simpl.
                  rewrite Hlt.
                  apply tnum_neg_sound.
                  unfold mem_tnum in *.
                  simpl; auto.
                - unfold tnum_abs.
                  simpl.
                  rewrite Hlt1.
                  apply tnum_neg_sound.
                  unfold mem_tnum in *.
                  simpl; auto.
              }

              destruct (Int64_msb (snd b)) eqn: Hlt_b.
              {
                unfold tnum_union_opt; simpl.
                unfold tnum_sdiv_helper; simpl.
                rewrite Hlt, Hlt1.
                simpl.
                assert (Heq: Int64_msb (Int64.or (fst b) Int64_min_signed) = true).
                { 
                  unfold Int64_msb, Int64_min_signed in *.
                  rewrite Clt_Zlt_signed_false in *.
                  rewrite Clt_Zlt_signed in *.
                  change (Int64.signed Int64.zero) with 0 in *.
                  rewrite testbit_sign_pos in *.
                  rewrite testbit_sign_neg in *.
                  rewrite Int64.bits_or.
                  2:{ change (Int64.zwordsize) with 64; lia. }
                  rewrite orb_true_iff.
                  right.
                  change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                  auto.
                }
                rewrite Heq; clear Heq.

                apply tnum_union_sound.

                (** Here we only know i is negitive because of Int64_msb (fst a) = true
                  - when j is negitive i.e. Int64_msb j = true. Go right?
                  - when j is postive i.e. Int64_msb j = false. Go left?
                *)
                destruct (Int64_msb j) eqn: Hi_eq.
                {
                  right.
                  admit.
                }
                admit.
              }

              unfold tnum_union_opt; simpl.
              admit.
            }
              ../..

                (** Here we know i and j are negitive because of Int64_msb (fst a) = true /\ Int64_msb (fst b) = true *)
                assert (Hi_neg: Int64.lt i Int64.zero = true).
                { apply Int64_msb_lt with (b:= a); eauto. }
                assert (Hj_neg: Int64.lt j Int64.zero = true).
                { apply Int64_msb_lt with (b:= b); eauto. }

                assert (Heq: Int64.divs i j = Int64.divu (Int64.neg i) (Int64.neg j)).
                {  apply Int64_divs_eq; auto. }
                rewrite Heq; clear Heq.

                eapply tnum_udiv_sound.
                - apply tnum_abs_ge.
                - unfold tnum_ge_inv, to_tnumZ, tnum_abs, tnum_neg.
                  split; simpl.
                  + apply Int64_unsigned_ge_0.
                  + apply Int64_unsigned_ge_0.
                - (* rewrite <- mem_tnum_min_signed_iff. *)
                  unfold tnum_abs; simpl.
                  rewrite Hlt.
                  apply tnum_neg_sound.
                  unfold mem_tnum in *.
                  simpl; auto.
                - unfold tnum_abs.
                  simpl.
                  rewrite Hlt1.
                  apply tnum_neg_sound.
                  unfold mem_tnum in *.
                  simpl; auto.
              }


              rewrite Int64_mone_msb.
              unfold tnum_union_opt.
              unfold tnum_sdiv_helper; simpl.
              rewrite Hlt. rewrite Int64_mone_msb. simpl.
              change (tnum_abs (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
              rewrite <- (Int64.divu_one (Int64.repr Int64.min_signed)).
              assert (Heq: a = (fst a, snd a)). { destruct a; simpl; auto. }
              rewrite <- Heq; clear Heq.
              apply tnum_udiv_sound.
              { apply tnum_abs_ge. }

              {
                unfold tnum_ge_inv, to_tnumZ, tnum_abs.
                split; simpl.
                - change (Int64.unsigned Int64.one) with 1.
                  lia.
                - change (Int64.unsigned Int64.zero) with 0.
                  lia.
              }

              {
                unfold tnum_abs.
                rewrite Hlt.
                rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
                apply tnum_neg_sound.
                unfold Int64_msb in Hlt.
                change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
                rewrite Hm1 in H_dst.
                auto.
              }

              {
                unfold mem_tnum.
                simpl.
                change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
                auto.
              }
            }
            
            destruct (Int64_msb (snd a)) eqn: Hlt1.
            { rewrite Int64_mone_msb. simpl.
              unfold tnum_sdiv_helper; simpl.
              rewrite Int64_mone_msb. simpl.
              change (tnum_abs (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
              assert (Heq: (Int64_msb (Int64.or (fst a) Int64_min_signed)) = true).
              { unfold Int64_msb in *.
                rewrite Clt_Zlt_signed_false in *.
                rewrite Clt_Zlt_signed in *.
                change (Int64.signed Int64.zero) with 0 in *.
                rewrite testbit_sign_pos in *.
                rewrite testbit_sign_neg in *.
                rewrite Int64.bits_or.
                2:{ change (Int64.zwordsize) with 64; lia. }
                rewrite orb_true_iff.
                right.
                change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                auto.
              }
              rewrite Heq; clear Heq.

              simpl.
              rewrite Hlt. simpl.

              apply tnum_union_sound.

              left.
              rewrite <- (Int64.divu_one (Int64.repr Int64.min_signed)).
              apply tnum_udiv_sound.
              - apply tnum_abs_ge.
              - unfold tnum_ge_inv, to_tnumZ, tnum_abs.
                split; simpl.
                + change (Int64.unsigned Int64.one) with 1.
                  lia.
                + change (Int64.unsigned Int64.zero) with 0.
                  lia.
              - unfold tnum_abs; simpl.
                assert (Heq: Int64_msb (Int64.or (fst a) Int64_min_signed) = true).
                { 
                  unfold Int64_msb, Int64_min_signed in *.
                  rewrite Clt_Zlt_signed_false in *.
                  rewrite Clt_Zlt_signed in *.
                  change (Int64.signed Int64.zero) with 0 in *.
                  rewrite testbit_sign_pos in *.
                  rewrite testbit_sign_neg in *.
                  rewrite Int64.bits_or.
                  2:{ change (Int64.zwordsize) with 64; lia. }
                  rewrite orb_true_iff.
                  right.
                  change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                  auto.
                }
                rewrite Heq; clear Heq.
                
                rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
                apply tnum_neg_sound.
                change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
                unfold mem_tnum in *.
                rewrite <- H_dst in *.
                simpl in *.
                rewrite Int64.not_and_or_not.
                rewrite Int64.not_involutive.
                rewrite <- Int64.and_commut with (x:= Int64.not (snd a)).
                rewrite Int64.or_and_distrib_l.
                unfold Int64_min_signed.
                rewrite Int64.and_commut. 
                rewrite Hm1.
                rewrite Int64.or_idem.
                auto.
              - unfold mem_tnum.
                simpl.
                change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
                auto.
            }

            rewrite Int64_mone_msb. simpl.
            unfold tnum_sdiv_helper; simpl.
            rewrite Hlt.
            rewrite Int64_mone_msb. simpl.
            
            rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
            apply tnum_neg_sound.
            change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
            (*
            change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).

            rewrite mem_tnum_min_signed_iff. *)
            replace (Int64.repr Int64.min_signed) with (Int64.divu (Int64.repr Int64.min_signed) Int64.one).
            2:{ rewrite Int64.divu_one. auto. }
            eapply tnum_udiv_sound.
            { apply tnum_abs_ge. }
            { unfold tnum_ge_inv, to_tnumZ, tnum_abs, tnum_neg.
              split; simpl.
              + apply Int64_unsigned_ge_0.
              + apply Int64_unsigned_ge_0.
            }
            { (* rewrite <- mem_tnum_min_signed_iff. *)
              unfold tnum_abs; simpl.
              rewrite Hlt.
              rewrite Hm1 in H_dst.
              unfold mem_tnum in *.
              simpl.
              auto.
            }
            { unfold tnum_abs.
              simpl.
              rewrite Int64_mone_msb. simpl.
              change (tnum_neg (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
              unfold mem_tnum.
              simpl.
              change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
              auto.
            }
      + simpl. apply tnum_unknown_gamma.
      + simpl.
        unfold tnum_sdiv_common.
        unfold tnum_get_positive.
        destruct (Int64_msb (fst a)) eqn: Ha_v.
        * unfold tnum_get_negative; simpl.
          rewrite Ha_v; simpl.
          destruct (Int64_msb (fst b)) eqn: Hb_v.
          {
            unfold tnum_union_opt; simpl.
            unfold tnum_sdiv_helper; simpl.
            rewrite Ha_v, Hb_v.
            simpl.
            replace (Int64.repr Int64.min_signed) with (Int64.divu (Int64.repr Int64.min_signed) Int64.one).
            2:{ rewrite Int64.divu_one. auto. }  (*
            rewrite mem_tnum_min_signed_iff.
            change (Int64.repr (2 ^ 63)) with (Int64.divu (Int64.repr (2 ^ 63)) Int64.one). *)
            eapply tnum_udiv_sound.
            - apply tnum_abs_ge.
            - unfold tnum_ge_inv, to_tnumZ, tnum_abs, tnum_neg.
              split; simpl.
              + apply Int64_unsigned_ge_0.
              + apply Int64_unsigned_ge_0.
            - (* rewrite <- mem_tnum_min_signed_iff. *)
              unfold tnum_abs; simpl.
              rewrite Ha_v.
              rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
              apply tnum_neg_sound.
              change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
              auto.
            - unfold tnum_abs.
              simpl.
              rewrite Hb_v.
              replace Int64.one with (Int64.neg Int64.mone).
              apply tnum_neg_sound.
              auto.
              unfold Int64.neg.
              unfold Int64.mone, Int64.one.
              change (Int64.unsigned (Int64.repr (-1))) with 18446744073709551615.
              simpl. 
              Search Int64.neg. 
          }


              assert (Heq: Int64_msb Int64.mone = true).
              { Search Int64_msb. unfold  }
              subst i.
              unfold mem_tnum in H_dst.
              rewrite <- H_dst.
              rewrite Clt_Zlt_signed.
              change (Int64.signed Int64.zero) with 0 in *.
              rewrite testbit_sign_neg in *.
              rewrite Int64.bits_and.
              2:{ change (Int64.zwordsize) with 64; lia. }
              rewrite Int64.bits_not.
              2:{ change (Int64.zwordsize) with 64; lia. }
              change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
              rewrite andb_true_l.
              simpl.
              rewrite orb_true_iff.
              right.
              change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
              auto.

              Search Int64.lt.
            }
            rewrite orb_true_iff in Hm.
            unfold Int64_min_signed, mem_tnum  in *.
            rewrite Hb_m in H_src.
            rewrite Int64.not_zero in *.
            rewrite Int64.and_mone in *.
            subst j.
            rewrite Hb_v.
            split; auto.
            destruct Hm as [Hm | Hm].
            - rewrite Hm.
              auto.
            - rewrite Hm.
              lia.
          }
  }
  ../..
  unfold eval_div_s64; simpl.
  unfold tnum_sdiv.
  rewrite (surjective_pairing a), (surjective_pairing b).
  destruct (Val.eq (Vlong j) (Vlong Int64.zero)) as [Hn | Hn] eqn:E1; simpl.
  { injection Hn as E_j0.
    rewrite E_j0. rewrite Int64.eq_true. simpl.
    rewrite E_j0 in H_src. unfold mem_tnum in H_src.
    rewrite Int64.and_zero_l in H_src.
    rewrite <- H_src. rewrite Int64.eq_true.
    destruct (Int64.eq (snd b) Int64.zero) eqn:Hb_m0; reflexivity.
  }
  
  assert (Heq: Int64.eq j Int64.zero = false).
  {
    clear - Hn.
    apply Int64.eq_false.
    intro HF.
    apply Hn.
    subst j.
    auto.
  }
  rewrite Heq; clear Heq.
  simpl.

  destruct (Coqlib.proj_sumbool (Val.eq (Vlong j) (Vlong Int64.mone)) &&
            Coqlib.proj_sumbool (Val.eq (Vlong i) LLONG_MIN)) eqn:E2.
  { apply andb_prop in E2. destruct E2 as [E2 E2'].
    apply Coqlib.proj_sumbool_true in E2, E2'.
    unfold LLONG_MIN in E2'.
    injection E2 as E2. injection E2' as E2'.
    rewrite E2, E2'.
    rewrite! Int64.eq_true. simpl.
    rewrite E2 in H_src. rewrite E2' in H_dst.
    (*
    unfold mem_tnum in H_src.
    rewrite Int64.and_mone_l in H_src. *)
    destruct (Int64.eq (snd b) Int64.zero) eqn:Hb_m0.
    - apply Int64.same_if_eq in Hb_m0.
      unfold mem_tnum in H_src.
      rewrite Int64.and_mone_l in H_src.
      rewrite Hb_m0 in *.
      rewrite Int64.not_zero in H_src.
      rewrite <- H_src.
      change (Int64.eq Int64.mone Int64.zero) with false; simpl.
      destruct (Int64.eq (snd a) Int64.zero) eqn:Ha_m0.
      + apply Int64.same_if_eq in Ha_m0.
        unfold mem_tnum in H_dst.
        rewrite Ha_m0 in H_dst.
        rewrite Int64.not_zero in H_dst.
        rewrite <- H_dst.
        change (Int64.eq (Int64.and (Int64.repr Int64.min_signed) Int64.mone) Int64_min_signed
             && Int64.eq Int64.mone Int64.mone) with true; simpl.
        unfold mem_tnum. unfold Int64_min_signed. simpl.
        rewrite Int64.not_zero. rewrite Int64.and_mone. reflexivity.
      + unfold tnum_sdiv_common. simpl.
        apply tnum_msb in H_dst as H. destruct H.
        * rewrite H. rewrite Int64_mone_msb. simpl.
          unfold tnum_sdiv_helper; simpl.
          rewrite H. rewrite Int64_mone_msb. simpl.
          change (tnum_abs (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
          rewrite <- (Int64.divu_one (Int64.repr Int64.min_signed)).
          assert (Heq: a = (fst a, snd a)). { destruct a; simpl; auto. }
          rewrite <- Heq; clear Heq.
          apply tnum_udiv_sound.
          { apply tnum_abs_ge. }

          {
            unfold tnum_ge_inv, to_tnumZ, tnum_abs.
            split; simpl.
            - change (Int64.unsigned Int64.one) with 1.
              lia.
            - change (Int64.unsigned Int64.zero) with 0.
              lia.
          }

          {
            unfold tnum_abs.
            rewrite H.
            rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
            apply tnum_neg_sound.
            clear - H_dst Ha_m0 H.
            unfold Int64_msb in H.
            change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
            auto.
          }

          {
            unfold mem_tnum.
            simpl.
            change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
            auto.
          }
        * rewrite H. rewrite Int64_mone_msb. simpl.
          unfold tnum_sdiv_helper; simpl.
          rewrite Int64_mone_msb. simpl.
          change (tnum_abs (Int64.mone, Int64.zero)) with (Int64.one, Int64.zero).
          assert (Heq: a = (fst a, snd a)). { destruct a; simpl; auto. }
          rewrite <- Heq; clear Heq.
          destruct (Int64_msb (fst a)) eqn: Hlt.
          {
            rewrite Hlt.
            simpl.
            replace (Int64.repr Int64.min_signed) with (Int64.divu (Int64.repr Int64.min_signed) Int64.one).
            2:{ rewrite Int64.divu_one. auto. } 
            apply tnum_udiv_sound.
            - apply tnum_abs_ge.
            - unfold tnum_ge_inv, to_tnumZ, tnum_abs.
              split; simpl.
              + change (Int64.unsigned Int64.one) with 1.
                lia.
              + change (Int64.unsigned Int64.zero) with 0.
                lia.
            - unfold tnum_abs.
              rewrite Hlt.
              rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
              apply tnum_neg_sound.
              clear - H_dst Ha_m0 H.
              unfold Int64_msb in H.
              change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
              auto.
            - unfold mem_tnum.
              simpl.
              change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
              auto.
          }

          {
            simpl.
            assert (Heq: (Int64_msb (Int64.or (fst a) Int64_min_signed)) = true).
            { unfold Int64_msb, Int64_min_signed.
              rewrite Clt_Zlt_signed.
              change (Int64.signed Int64.zero) with 0 in *.
              rewrite testbit_sign_neg.
              rewrite Int64.bits_or.
              2:{ change (Int64.zwordsize) with 64; lia. }
              rewrite orb_true_iff.
              right.
              change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
              auto.
            }
            rewrite Heq; clear Heq.
            simpl.
            rewrite Hlt; simpl.
            apply tnum_union_sound.

            left.
            rewrite <- (Int64.divu_one (Int64.repr Int64.min_signed)).
            apply tnum_udiv_sound.
            - apply tnum_abs_ge.
            - unfold tnum_ge_inv, to_tnumZ, tnum_abs.
              split; simpl.
              + change (Int64.unsigned Int64.one) with 1.
                lia.
              + change (Int64.unsigned Int64.zero) with 0.
                lia.
            - unfold tnum_abs; simpl.
              assert (Heq: Int64_msb (Int64.or (fst a) Int64_min_signed) = true).
              { 
                unfold Int64_msb, Int64_min_signed in *.
                rewrite Clt_Zlt_signed_false in *.
                rewrite Clt_Zlt_signed in *.
                change (Int64.signed Int64.zero) with 0 in *.
                rewrite testbit_sign_pos in *.
                rewrite testbit_sign_neg in *.
                rewrite Int64.bits_or.
                2:{ change (Int64.zwordsize) with 64; lia. }
                rewrite orb_true_iff.
                right.
                change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                auto.
              }
              rewrite Heq; clear Heq.
              clear - H_dst H Hlt.
              rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
              apply tnum_neg_sound.
              change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
              unfold mem_tnum in *.
              rewrite <- H_dst in *.
              simpl in *.
              rewrite Int64.not_and_or_not.
              rewrite Int64.not_involutive.
              rewrite <- Int64.and_commut with (x:= Int64.not (snd a)).
              rewrite Int64.or_and_distrib_l.
              unfold Int64_min_signed. 
              rewrite Int64.or_idem.
              rewrite Int64.and_commut.
              auto.
            - unfold mem_tnum.
              simpl.
              change (Int64.and Int64.one (Int64.not Int64.zero)) with Int64.one.
              auto.
          }

    - 
      destruct (Int64.eq (fst b) Int64.zero) eqn:Hb_v0.
      + simpl. apply tnum_unknown_gamma.
      + simpl.
        unfold tnum_sdiv_common.
        unfold tnum_get_positive.
        destruct (Int64_msb (fst a)) eqn: Ha_v.
        * unfold tnum_get_negative; simpl.
          rewrite Ha_v; simpl.
          destruct (Int64_msb (fst b)) eqn: Hb_v.
          {
            unfold tnum_union_opt; simpl.
            unfold tnum_sdiv_helper; simpl.
            rewrite Ha_v, Hb_v.
            simpl.
            replace (Int64.repr Int64.min_signed) with (Int64.divu (Int64.repr Int64.min_signed) Int64.one).
            2:{ rewrite Int64.divu_one. auto. }  (*
            rewrite mem_tnum_min_signed_iff.
            change (Int64.repr (2 ^ 63)) with (Int64.divu (Int64.repr (2 ^ 63)) Int64.one). *)
            eapply tnum_udiv_sound.
            - apply tnum_abs_ge.
            - unfold tnum_ge_inv, to_tnumZ, tnum_abs, tnum_neg.
              split; simpl.
              + apply Int64_unsigned_ge_0.
              + apply Int64_unsigned_ge_0.
            - (* rewrite <- mem_tnum_min_signed_iff. *)
              unfold tnum_abs; simpl.
              rewrite Ha_v.
              rewrite <- Int64.neg_involutive with (x := Int64.repr Int64.min_signed).
              apply tnum_neg_sound.
              change (Int64.neg (Int64.repr Int64.min_signed)) with (Int64.repr Int64.min_signed).
              auto.
            - unfold tnum_abs.
              simpl.
              rewrite Hb_v.
              replace Int64.one with (Int64.neg Int64.mone).
              apply tnum_neg_sound.
              auto.
              unfold Int64.neg.
              unfold Int64.mone, Int64.one.
              change (Int64.unsigned (Int64.repr (-1))) with 18446744073709551615.
              simpl. 
              Search Int64.neg. 
          }
          unfold tnum_union_opt; simpl.
        ../..
        rewrite <- H_src in *.
        clear - Hb_m0 Hb_v0.
        apply Int64_eq_false in Hb_m0, Hb_v0.
        apply Hb_m0; clear Hb_m0.
        Search (Int64.not).
        admit.
  }
  admit.
Admitted.
*)