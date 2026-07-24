From Coq Require Import List ZArith Lia Bool Btauto.
From compcert Require Import Integers Values.
From bpf.semantics Require Import ebpfBinSem.

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

Lemma tnum_union_eq : forall a b,
    tnum_union a b =
      of_tnumZ (tnumZ.tnum_union (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros [a_v a_m] [b_v b_m].
  unfold tnum_union, tnumZ.tnum_union, to_tnumZ, of_tnumZ.
  simpl.
  f_equal; apply Int64.same_bits_eq; intros n Hn;
    rewrite Int64.testbit_repr by auto;
    repeat rewrite Int64.bits_and by auto;
    repeat rewrite Int64.bits_not by auto;
    repeat rewrite Int64.bits_or by auto;
    repeat rewrite Int64.bits_xor by auto;
    repeat rewrite Z.land_spec;
    repeat rewrite Z.lnot_spec by lia;
    repeat rewrite Z.lor_spec;
    repeat rewrite Z.lxor_spec;
    reflexivity.
Qed.

(*
  Old multiplication correspondence proof.  It splits the concrete value and
  uncertainty into separate accumulators, so it does not state the invariant
  used by the new union-based long multiplication.

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
*)

Lemma of_tnumZ_mod_eq : forall x y,
    mod_pair x Int64.modulus = mod_pair y Int64.modulus ->
    of_tnumZ x = of_tnumZ y.
Proof.
  intros [xv xm] [yv ym] Hmod.
  unfold mod_pair in Hmod; simpl in Hmod.
  injection Hmod as Hv Hm.
  unfold of_tnumZ; simpl. f_equal; apply Int64_repr_mod; assumption.
Qed.

Lemma Int64_eq_zero_eqb : forall x,
    Int64.eq x Int64.zero = Z.eqb (Int64.unsigned x) 0.
Proof.
  intros x. unfold Int64.eq. rewrite Int64.unsigned_zero.
  destruct (Z.eqb_spec (Int64.unsigned x) 0) as [Heq | Hneq].
  - rewrite Heq. reflexivity.
  - destruct (Coqlib.zeq (Int64.unsigned x) 0); congruence.
Qed.

Lemma Int64_lsb_eqb : forall x,
    Int64.eq (Int64.and x Int64.one) Int64.one =
      Z.eqb (Z.land (Int64.unsigned x) 1) 1.
Proof.
  intros x. unfold Int64.eq. rewrite <- Zland_and.
  rewrite Int64.unsigned_one.
  destruct (Z.eqb_spec (Z.land (Int64.unsigned x) 1) 1) as [Heq | Hneq].
  - rewrite Heq. reflexivity.
  - destruct (Coqlib.zeq (Z.land (Int64.unsigned x) 1) 1); congruence.
Qed.

Lemma Int64_unsigned_shiftr1_range : forall x,
    0 <= Z.shiftr (Int64.unsigned x) 1 < Int64.modulus.
Proof.
  intros x. change (0 <= Z.shiftr (Int64.unsigned x) 1 < 2 ^ 64).
  apply tnum_rshift1_range. apply Int64.unsigned_range.
Qed.

Lemma tnum_mul_rec_eq : forall fuel a b acc,
    (fuel <= 64)%nat ->
    tnum_mul_rec fuel a b acc =
      of_tnumZ
        (tnumZ.tnum_mul_rec_new fuel
          (to_tnumZ a) (to_tnumZ b) (to_tnumZ acc)).
Proof.
  intros fuel; induction fuel as [| fuel IH]; intros a b acc Hfuel.
  - simpl. rewrite tnum_tnumZ_id. reflexivity.
  - unfold tnum_mul_rec; fold tnum_mul_rec.
    unfold tnumZ.tnum_mul_rec_new; fold tnumZ.tnum_mul_rec_new.
    change (fst (to_tnumZ a)) with (Int64.unsigned (fst a)).
    change (snd (to_tnumZ a)) with (Int64.unsigned (snd a)).
    rewrite !Int64_eq_zero_eqb.
    replace (negb (Int64.unsigned (fst a) =? 0) ||
             negb (Int64.unsigned (snd a) =? 0))%bool
      with (negb ((Int64.unsigned (fst a) =? 0) &&
                  (Int64.unsigned (snd a) =? 0)))%bool by btauto.
    destruct (negb ((Int64.unsigned (fst a) =? 0) &&
                    (Int64.unsigned (snd a) =? 0))) eqn:Hnonzero.
    2:{ symmetry. apply tnum_tnumZ_id. }
    rewrite !Int64_lsb_eqb.
    destruct (Z.land (Int64.unsigned (fst a)) 1 =? 1) eqn:Hvalue.
    + rewrite tnum_add_eq.
      rewrite IH by lia.
      rewrite tnum_shiftl_eq, tnum_shiftr_eq, !tnumZ_tnum_id_eq.
      apply of_tnumZ_mod_eq.
      apply tnum_mul_rec_new_mod_eq;
        unfold to_tnumZ; simpl; apply Int64_unsigned_shiftr1_range.
    + destruct (Z.land (Int64.unsigned (snd a)) 1 =? 1) eqn:Hmask.
      * rewrite tnum_union_eq, tnum_add_eq.
        rewrite IH by lia.
        rewrite tnum_shiftl_eq, tnum_shiftr_eq, !tnumZ_tnum_id_eq.
        apply of_tnumZ_mod_eq.
        apply tnum_mul_rec_new_congr_mod.
        -- simpl. apply Z.mod_pos_bound. lia.
        -- simpl. apply Z.mod_pos_bound. lia.
        -- unfold to_tnumZ; simpl. apply Int64_unsigned_shiftr1_range.
        -- unfold to_tnumZ; simpl. apply Int64_unsigned_shiftr1_range.
        -- apply pair_mod_mod.
        -- apply pair_mod_mod.
        -- rewrite pair_mod_mod.
           apply tnumZ_union_mod; try lia.
           ++ reflexivity.
           ++ apply pair_mod_mod.
      * rewrite IH by lia.
        rewrite tnum_shiftl_eq, tnum_shiftr_eq, !tnumZ_tnum_id_eq.
        assert (Haccmod : to_tnumZ acc =
          mod_pair (to_tnumZ acc) Int64.modulus).
        { unfold to_tnumZ, mod_pair; simpl. f_equal.
          - rewrite Z.mod_small.
            + reflexivity.
            + apply Int64.unsigned_range.
          - rewrite Z.mod_small.
            + reflexivity.
            + apply Int64.unsigned_range. }
        rewrite Haccmod at 1.
        apply of_tnumZ_mod_eq.
        apply tnum_mul_rec_new_mod_eq;
          unfold to_tnumZ; simpl; apply Int64_unsigned_shiftr1_range.
Qed.

Lemma tnum_mul_eq : forall a b,
    tnum_mul a b =
      of_tnumZ (tnumZ.tnum_mul_new (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros a b. unfold tnum_mul, tnumZ.tnum_mul_new.
  apply tnum_mul_rec_eq. lia.
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

(** Bit-level view of [mem_tnum].  It is the common proof interface
    for bitwise operations and shifts. *)
Lemma mem_tnum_bit :
  forall i a bit,
    mem_tnum i a ->
    0 <= bit < Int64.zwordsize ->
    Int64.testbit i bit &&
      negb (Int64.testbit (snd a) bit) =
    Int64.testbit (fst a) bit.
Proof.
  intros i a bit Hmem Hbit.
  apply (f_equal (fun x => Int64.testbit x bit)) in Hmem.
  rewrite Int64.bits_and, Int64.bits_not in Hmem by lia.
  exact Hmem.
Qed.

Theorem tnum_and_mem_sound :
  forall a b i j,
    mem_tnum i a ->
    mem_tnum j b ->
    mem_tnum (Int64.and i j) (tnum_and a b).
Proof.
  intros [av am] [bv bm] i j Ha Hb.
  unfold mem_tnum, tnum_and in *; simpl in *.
  apply Int64.same_bits_eq; intros bit Hbit.
  repeat first
    [ rewrite Int64.bits_and by lia
    | rewrite Int64.bits_or by lia
    | rewrite Int64.bits_not by lia ].
  pose proof (mem_tnum_bit i (av, am) bit Ha Hbit) as Hai.
  pose proof (mem_tnum_bit j (bv, bm) bit Hb Hbit) as Hbj.
  simpl in Hai, Hbj.
  destruct (Int64.testbit i bit), (Int64.testbit j bit),
    (Int64.testbit av bit), (Int64.testbit am bit),
    (Int64.testbit bv bit), (Int64.testbit bm bit);
    simpl in Hai, Hbj |- *; congruence.
Qed.

Theorem tnum_or_mem_sound :
  forall a b i j,
    mem_tnum i a ->
    mem_tnum j b ->
    mem_tnum (Int64.or i j) (tnum_or a b).
Proof.
  intros [av am] [bv bm] i j Ha Hb.
  unfold mem_tnum, tnum_or in *; simpl in *.
  apply Int64.same_bits_eq; intros bit Hbit.
  repeat first
    [ rewrite Int64.bits_and by lia
    | rewrite Int64.bits_or by lia
    | rewrite Int64.bits_not by lia ].
  pose proof (mem_tnum_bit i (av, am) bit Ha Hbit) as Hai.
  pose proof (mem_tnum_bit j (bv, bm) bit Hb Hbit) as Hbj.
  simpl in Hai, Hbj.
  destruct (Int64.testbit i bit), (Int64.testbit j bit),
    (Int64.testbit av bit), (Int64.testbit am bit),
    (Int64.testbit bv bit), (Int64.testbit bm bit);
    simpl in Hai, Hbj |- *; congruence.
Qed.

Theorem tnum_xor_mem_sound :
  forall a b i j,
    mem_tnum i a ->
    mem_tnum j b ->
    mem_tnum (Int64.xor i j) (tnum_xor a b).
Proof.
  intros [av am] [bv bm] i j Ha Hb.
  unfold mem_tnum, tnum_xor in *; simpl in *.
  apply Int64.same_bits_eq; intros bit Hbit.
  repeat first
    [ rewrite Int64.bits_and by lia
    | rewrite Int64.bits_or by lia
    | rewrite Int64.bits_xor by lia
    | rewrite Int64.bits_not by lia ].
  pose proof (mem_tnum_bit i (av, am) bit Ha Hbit) as Hai.
  pose proof (mem_tnum_bit j (bv, bm) bit Hb Hbit) as Hbj.
  simpl in Hai, Hbj.
  destruct (Int64.testbit i bit), (Int64.testbit j bit),
    (Int64.testbit av bit), (Int64.testbit am bit),
    (Int64.testbit bv bit), (Int64.testbit bm bit);
    simpl in Hai, Hbj |- *; congruence.
Qed.

Theorem tnum_lshift_mem_sound :
  forall a i shift,
    mem_tnum i a ->
    mem_tnum (Int64.shl i shift) (tnum_lshift a shift).
Proof.
  intros [av am] i shift Hmem.
  unfold mem_tnum, tnum_lshift in *; simpl in *.
  apply Int64.same_bits_eq; intros bit Hbit.
  rewrite Int64.bits_and, Int64.bits_not, !Int64.bits_shl by lia.
  destruct (Coqlib.zlt bit (Int64.unsigned shift)) eqn:Hlt;
    simpl; try reflexivity.
  pose proof
    (mem_tnum_bit i (av, am) (bit - Int64.unsigned shift)
      Hmem) as Hmem_bit.
  simpl in Hmem_bit. apply Hmem_bit.
  pose proof (Int64.unsigned_range shift).
  lia.
Qed.

Theorem tnum_rshift_mem_sound :
  forall a i shift,
    mem_tnum i a ->
    mem_tnum (Int64.shru i shift) (tnum_rshift a shift).
Proof.
  intros [av am] i shift Hmem.
  unfold mem_tnum, tnum_rshift in *; simpl in *.
  apply Int64.same_bits_eq; intros bit Hbit.
  rewrite Int64.bits_and, Int64.bits_not, !Int64.bits_shru by lia.
  destruct
    (Coqlib.zlt (bit + Int64.unsigned shift) Int64.zwordsize)
    eqn:Hlt; simpl; try reflexivity.
  pose proof
    (mem_tnum_bit i (av, am) (bit + Int64.unsigned shift)
      Hmem) as Hmem_bit.
  simpl in Hmem_bit. apply Hmem_bit.
  pose proof (Int64.unsigned_range shift).
  lia.
Qed.

Theorem tnum_arshift_mem_sound :
  forall a i shift,
    mem_tnum i a ->
    mem_tnum (Int64.shr i shift) (tnum_arshift a shift).
Proof.
  intros [av am] i shift Hmem.
  unfold mem_tnum, tnum_arshift in *; simpl in *.
  apply Int64.same_bits_eq; intros bit Hbit.
  rewrite Int64.bits_and, Int64.bits_not, !Int64.bits_shr by lia.
  pose proof
    (mem_tnum_bit i (av, am)
      (if Coqlib.zlt (bit + Int64.unsigned shift) Int64.zwordsize
       then bit + Int64.unsigned shift
       else Int64.zwordsize - 1)
      Hmem) as Hmem_bit.
  simpl in Hmem_bit. apply Hmem_bit.
  destruct
    (Coqlib.zlt (bit + Int64.unsigned shift) Int64.zwordsize)
    eqn:Hlt.
  - pose proof (Int64.unsigned_range shift).
    lia.
  - change Int64.zwordsize with 64. lia.
Qed.

(** Public, value-level interfaces for bitwise operations. *)
Theorem tnum_and_sound :
  forall a b dst src,
    gamma_val dst a ->
    gamma_val src b ->
    gamma_val (Val.andl dst src) (tnum_and a b).
Proof.
  intros a b dst src Hdst Hsrc.
  destruct dst; simpl in Hdst; try contradiction.
  destruct src; simpl in Hsrc; try contradiction.
  simpl. apply tnum_and_mem_sound; assumption.
Qed.

Theorem tnum_or_sound :
  forall a b dst src,
    gamma_val dst a ->
    gamma_val src b ->
    gamma_val (Val.orl dst src) (tnum_or a b).
Proof.
  intros a b dst src Hdst Hsrc.
  destruct dst; simpl in Hdst; try contradiction.
  destruct src; simpl in Hsrc; try contradiction.
  simpl. apply tnum_or_mem_sound; assumption.
Qed.

Theorem tnum_xor_sound :
  forall a b dst src,
    gamma_val dst a ->
    gamma_val src b ->
    gamma_val (Val.xorl dst src) (tnum_xor a b).
Proof.
  intros a b dst src Hdst Hsrc.
  destruct dst; simpl in Hdst; try contradiction.
  destruct src; simpl in Hsrc; try contradiction.
  simpl. apply tnum_xor_mem_sound; assumption.
Qed.

(** CompCert represents 64-bit shift counts as 32-bit integers at the
    value level, while [tnum] stores the same count in an [int64]. *)
Lemma Int64_shl'_shl :
  forall x n,
    Int64.shl' x n =
    Int64.shl x (Int64.repr (Int.unsigned n)).
Proof.
  intros x n. unfold Int64.shl', Int64.shl.
  rewrite Int64.unsigned_repr; auto.
  pose proof (Int.unsigned_range n) as Hn.
  change Int.modulus with 4294967296 in Hn.
  change Int64.max_unsigned with 18446744073709551615.
  lia.
Qed.

Lemma Int64_shru'_shru :
  forall x n,
    Int64.shru' x n =
    Int64.shru x (Int64.repr (Int.unsigned n)).
Proof.
  intros x n. unfold Int64.shru', Int64.shru.
  rewrite Int64.unsigned_repr; auto.
  pose proof (Int.unsigned_range n) as Hn.
  change Int.modulus with 4294967296 in Hn.
  change Int64.max_unsigned with 18446744073709551615.
  lia.
Qed.

Lemma Int64_shr'_shr :
  forall x n,
    Int64.shr' x n =
    Int64.shr x (Int64.repr (Int.unsigned n)).
Proof.
  intros x n. unfold Int64.shr', Int64.shr.
  rewrite Int64.unsigned_repr; auto.
  pose proof (Int.unsigned_range n) as Hn.
  change Int.modulus with 4294967296 in Hn.
  change Int64.max_unsigned with 18446744073709551615.
  lia.
Qed.

Theorem tnum_lshift_sound :
  forall a dst count,
    gamma_val dst a ->
    Int.ltu count Int64.iwordsize' = true ->
    gamma_val
      (Val.shll dst (Vint count))
      (tnum_lshift a (Int64.repr (Int.unsigned count))).
Proof.
  intros a dst count Hdst Hcount.
  destruct dst; simpl in Hdst; try contradiction.
  simpl. rewrite Hcount. simpl.
  rewrite Int64_shl'_shl.
  apply tnum_lshift_mem_sound. exact Hdst.
Qed.

Theorem tnum_rshift_sound :
  forall a dst count,
    gamma_val dst a ->
    Int.ltu count Int64.iwordsize' = true ->
    gamma_val
      (Val.shrlu dst (Vint count))
      (tnum_rshift a (Int64.repr (Int.unsigned count))).
Proof.
  intros a dst count Hdst Hcount.
  destruct dst; simpl in Hdst; try contradiction.
  simpl. rewrite Hcount. simpl.
  rewrite Int64_shru'_shru.
  apply tnum_rshift_mem_sound. exact Hdst.
Qed.

Theorem tnum_arshift_sound :
  forall a dst count,
    gamma_val dst a ->
    Int.ltu count Int64.iwordsize' = true ->
    gamma_val
      (Val.shrl dst (Vint count))
      (tnum_arshift a (Int64.repr (Int.unsigned count))).
Proof.
  intros a dst count Hdst Hcount.
  destruct dst; simpl in Hdst; try contradiction.
  simpl. rewrite Hcount. simpl.
  rewrite Int64_shr'_shr.
  apply tnum_arshift_mem_sound. exact Hdst.
Qed.

Theorem tnum_add_mem_sound :
  forall a b i j,
    mem_tnum i a ->
    mem_tnum j b ->
    mem_tnum (Int64.add i j) (tnum_add a b).
Proof.
  intros.
  apply tnum_binary_sound
    with (tnum_fz := tnumZ.tnum_add) (fz := Z.add); auto.
  - intros.
    apply tnumZ_add_sound.tnum_add_sound; auto.
  - intros.
    apply testbit_add; auto.
  - apply tnum_add_eq.
Qed.

Theorem tnum_add_sound :
  forall a b dst src,
    gamma_val dst a ->
    gamma_val src b ->
    gamma_val (Val.addl dst src) (tnum_add a b).
Proof.
  intros a b dst src Hdst Hsrc.
  destruct dst; simpl in Hdst; try contradiction.
  destruct src; simpl in Hsrc; try contradiction.
  simpl.
  apply tnum_add_mem_sound; assumption.
Qed.

Theorem tnum_sub_mem_sound :
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

Theorem tnum_sub_sound :
  forall a b dst src,
    gamma_val dst a ->
    gamma_val src b ->
    gamma_val (Val.subl dst src) (tnum_sub a b).
Proof.
  intros a b dst src Hdst Hsrc.
  destruct dst; simpl in Hdst; try contradiction.
  destruct src; simpl in Hsrc; try contradiction.
  simpl. apply tnum_sub_mem_sound; assumption.
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

(* Old multiplication soundness theorem; retained during migration.
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
*)

Theorem tnum_mul_mem_sound :
  forall a b i j
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    mem_tnum (Int64.mul i j) (tnum_mul a b).
Proof.
  intros a b i j MEMA MEMB.
  pose proof (mem_tnum_gamma i a MEMA) as Hga.
  pose proof (mem_tnum_gamma j b MEMB) as Hgb.
  pose proof (tnumZ_mul_sound.tnum_mul_new_sound
    (to_tnumZ a) (to_tnumZ b)
    (Int64.unsigned i) (Int64.unsigned j)
    Hga Hgb (Int64.unsigned_range i)) as Hsound.
  rewrite tnum_mul_eq.
  destruct (tnumZ.tnum_mul_new (to_tnumZ a) (to_tnumZ b))
    as [rv rm] eqn:Hmul in Hsound |- *.
  unfold gamma in Hsound; simpl in Hsound.
  unfold mem_tnum, of_tnumZ; simpl.
  apply Int64.same_bits_eq.
  intros n Hn.
  rewrite Int64.bits_and by auto.
  rewrite Int64.bits_not by auto.
  rewrite !Int64.testbit_repr by auto.
  rewrite testbit_mul by auto.
  rewrite <- Hsound.
  rewrite Z.land_spec, Z.lnot_spec by lia.
  reflexivity.
Qed.

Theorem tnum_mul_sound :
  forall a b dst src,
    gamma_val dst a ->
    gamma_val src b ->
    gamma_val (Val.mull dst src) (tnum_mul a b).
Proof.
  intros a b dst src Hdst Hsrc.
  destruct dst; simpl in Hdst; try contradiction.
  destruct src; simpl in Hsrc; try contradiction.
  simpl. apply tnum_mul_mem_sound; assumption.
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

Lemma testbit_sign_pos_smod:
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

Lemma testbit_sign_neg_smod:
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

Lemma Clt_Zlt_signed_smod:
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

Lemma Clt_Zlt_signed_false_smod:
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

Lemma tnum_nonnegative_sound :
  forall a i
         (MEMA : mem_tnum i a),
    tnum_nonnegative a = true ->
    0 <= Int64.signed i.
Proof.
  intros a i MEMA Hnonneg.
  unfold tnum_nonnegative in Hnonneg.
  apply negb_true_iff in Hnonneg.
  unfold Int64_msb in Hnonneg.
  rewrite Clt_Zlt_signed_false_smod in Hnonneg.
  unfold get_signed_max in Hnonneg.
  change (Int64.signed Int64.zero) with 0 in Hnonneg.
  apply testbit_sign_pos_smod.
  apply Bool.not_true_iff_false.
  intro Hi63.
  assert (Hor63 : Int64.testbit (Int64.or (fst a) (snd a))
                    (Int64.zwordsize - 1) = true).
  {
    unfold mem_tnum in MEMA.
    assert (Hbit : Int64.testbit (Int64.and i (Int64.not (snd a)))
                    (Int64.zwordsize - 1) =
                   Int64.testbit (fst a) (Int64.zwordsize - 1)).
    { rewrite MEMA. reflexivity. }
    rewrite Int64.bits_and in Hbit by (change Int64.zwordsize with 64; lia).
    rewrite Int64.bits_not in Hbit by (change Int64.zwordsize with 64; lia).
    rewrite Hi63 in Hbit.
    rewrite Int64.bits_or by (change Int64.zwordsize with 64; lia).
    destruct (Int64.testbit (snd a) (Int64.zwordsize - 1)) eqn:Hm63.
    - apply Bool.orb_true_intro. right. reflexivity.
    - apply Bool.orb_true_intro. left.
      simpl in Hbit. symmetry. exact Hbit.
  }
  apply testbit_sign_neg_smod in Hor63.
  lia.
Qed.

Lemma tnum_negative_sound :
  forall a i
         (MEMA : mem_tnum i a),
    tnum_negative a = true ->
    Int64.signed i < 0.
Proof.
  intros a i MEMA Hneg.
  unfold tnum_negative, Int64_msb in Hneg.
  rewrite Clt_Zlt_signed_smod in Hneg.
  apply testbit_sign_neg_smod.
  assert (Hv63 : Int64.testbit (fst a) (Int64.zwordsize - 1) = true).
  { apply testbit_sign_neg_smod. exact Hneg. }
  unfold mem_tnum in MEMA.
  assert (Hbit : Int64.testbit (Int64.and i (Int64.not (snd a)))
                  (Int64.zwordsize - 1) =
                 Int64.testbit (fst a) (Int64.zwordsize - 1)).
  { rewrite MEMA. reflexivity. }
  rewrite Int64.bits_and in Hbit by (change Int64.zwordsize with 64; lia).
  rewrite Int64.bits_not in Hbit by (change Int64.zwordsize with 64; lia).
  rewrite Hv63 in Hbit.
  destruct (Int64.testbit i (Int64.zwordsize - 1));
    destruct (Int64.testbit (snd a) (Int64.zwordsize - 1));
    simpl in Hbit; try discriminate; auto.
Qed.

Lemma tnum_low_bits_zero_sound :
  forall a i low_bits
         (MEMA : mem_tnum i a),
    tnum_low_bits_zero a low_bits = true ->
    Int64.and i low_bits = Int64.zero.
Proof.
  intros a i low_bits MEMA Hzero.
  unfold tnum_low_bits_zero in Hzero.
  apply Int64.same_if_eq in Hzero.
  unfold get_signed_max in Hzero.
  apply Int64.same_bits_eq.
  intros n Hn.
  rewrite Int64.bits_and by auto.
  rewrite Int64.bits_zero by auto.
  destruct (Int64.testbit low_bits n) eqn:Hlow; simpl.
  2:{ rewrite Bool.andb_false_r. reflexivity. }
  assert (Hzero_bit :
    Int64.testbit (Int64.and (Int64.or (fst a) (snd a)) low_bits) n =
    Int64.testbit Int64.zero n).
  { rewrite Hzero. reflexivity. }
  rewrite Int64.bits_and in Hzero_bit by auto.
  rewrite Int64.bits_or in Hzero_bit by auto.
  rewrite Int64.bits_zero in Hzero_bit by auto.
  rewrite Hlow in Hzero_bit.
  rewrite Bool.andb_true_r in Hzero_bit.
  simpl in Hzero_bit.
  apply Bool.orb_false_iff in Hzero_bit.
  destruct Hzero_bit as [Hv Hm].
  unfold mem_tnum in MEMA.
  assert (Hmem_bit :
    Int64.testbit (Int64.and i (Int64.not (snd a))) n =
    Int64.testbit (fst a) n).
  { rewrite MEMA. reflexivity. }
  rewrite Int64.bits_and in Hmem_bit by auto.
  rewrite Int64.bits_not in Hmem_bit by auto.
  rewrite Hv, Hm in Hmem_bit.
  destruct (Int64.testbit i n); simpl in Hmem_bit.
  - discriminate Hmem_bit.
  - reflexivity.
Qed.

Lemma Z_size_range_Int64_smod : forall x,
  0 <= x <= Int64.max_unsigned -> 0 <= Z_size_Z x <= Int64.zwordsize.
Proof.
  intros. split.
  - apply Z_size_Z_nonneg.
  - unfold Z_size_Z. change Int64.zwordsize with 64.
    destruct x; try lia.
    rewrite (Z.abs_eq _ (Pos2Z.is_nonneg p)).
    apply (Z.le_trans _ (Z.log2 Int64.max_unsigned + 1)).
    + pose proof (Z.log2_le_mono (Z.pos p) Int64.max_unsigned). lia.
    + simpl. lia.
Qed.

Lemma Int64_ones_testbit_low_smod :
  forall n bit,
    0 <= bit < n ->
    n <= Int64.zwordsize ->
    Int64.testbit (Int64_ones n) bit = true.
Proof.
  intros n bit Hbit Hn.
  unfold Int64_ones.
  rewrite Int64.testbit_repr by (change Int64.zwordsize with 64 in *; lia).
  apply Z.ones_spec_low. lia.
Qed.

Lemma Int64_ones_testbit_high_smod :
  forall n bit,
    0 <= n <= bit ->
    bit < Int64.zwordsize ->
    Int64.testbit (Int64_ones n) bit = false.
Proof.
  intros n bit Hn Hbit.
  unfold Int64_ones.
  rewrite Int64.testbit_repr by (change Int64.zwordsize with 64 in *; lia).
  apply Z.ones_spec_high. lia.
Qed.

Lemma tnum_smod_high_bits_sound :
  forall a res r
         (MEMR : mem_tnum r res),
    (forall bit,
        Int64_size (Int64.or (fst a) (snd a)) <= bit < Int64.zwordsize ->
        Int64.testbit r bit = false) ->
    mem_tnum r (tnum_smod_high_bits a res).
Proof.
  intros a res r MEMR Hhigh.
  unfold tnum_smod_high_bits, mem_tnum in *.
  cbn [fst snd].
  apply Int64.same_bits_eq.
  intros bit Hbit.
  repeat rewrite Int64.bits_and by auto.
  rewrite Int64.bits_not by auto.
  repeat rewrite Int64.bits_and by auto.
  set (size := Int64_size (Int64.or (fst a) (snd a))).
  fold size.
  assert (Hmem_bit :
    Int64.testbit (Int64.and r (Int64.not (snd res))) bit =
    Int64.testbit (fst res) bit).
  { rewrite MEMR. reflexivity. }
  rewrite Int64.bits_and in Hmem_bit by auto.
  rewrite Int64.bits_not in Hmem_bit by auto.
  pose proof (Int64.unsigned_range_2 (Int64.or (fst a) (snd a))) as Hrange.
  assert (Hsize_range : 0 <= size <= Int64.zwordsize).
  { subst size. apply Z_size_range_Int64_smod. lia. }
  destruct (Coqlib.zlt bit size) as [Hlt | Hge].
  - assert (Hmask : Int64.testbit (Int64_ones size) bit = true).
    { apply Int64_ones_testbit_low_smod; lia. }
    change (Int64_size (Int64.or (fst a) (snd a))) with size.
    rewrite Hmask.
    repeat rewrite Bool.andb_true_r.
    exact Hmem_bit.
  - assert (Hmask : Int64.testbit (Int64_ones size) bit = false).
    { apply Int64_ones_testbit_high_smod; lia. }
    change (Int64_size (Int64.or (fst a) (snd a))) with size.
    rewrite Hmask.
    repeat rewrite Bool.andb_false_r.
    simpl.
    rewrite Hhigh; auto.
    subst size. lia.
Qed.

Lemma Int64_mods_min_mone_zero :
  Int64.mods (Int64.repr Int64.min_signed) Int64.mone = Int64.zero.
Proof.
  unfold Int64.mods.
  change (Int64.signed (Int64.repr Int64.min_signed)) with Int64.min_signed.
  change (Int64.signed Int64.mone) with (-1).
  change (Int64.repr (Int64.min_signed mod (-1))) with Int64.zero.
  reflexivity.
Qed.

Lemma Z_rem_mod_divide_smod :
  forall a b d,
    b <> 0 ->
    d <> 0 ->
    (d | b) ->
    (Z.rem a b) mod d = a mod d.
Proof.
  intros a b d Hb Hd Hdiv.
  rewrite Z.rem_eq by auto.
  destruct Hdiv as [q Hq].
  subst b.
  replace (a - q * d * (a ÷ (q * d))) with
    (a + (-(q * (a ÷ (q * d)))) * d) by ring.
  rewrite (Z_mod_plus_full a (-(q * (a ÷ (q * d)))) d).
  reflexivity.
Qed.

Lemma testbit_mods_smod : forall bit x y,
    0 <= bit < Int64.zwordsize ->
    Int64.testbit (Int64.mods x y) bit =
      Z.testbit (Z.rem (Int64.signed x) (Int64.signed y)) bit.
Proof.
  intros. unfold Int64.mods.
  rewrite Int64.testbit_repr by auto.
  reflexivity.
Qed.

Lemma Int64_signed_nonzero_smod :
  forall x,
    x <> Int64.zero ->
    Int64.signed x <> 0.
Proof.
  intros x Hx Hsigned.
  apply Hx.
  rewrite <- (Int64.repr_signed x).
  rewrite Hsigned.
  reflexivity.
Qed.

Lemma Int64_signed_testbit_smod :
  forall x bit,
    0 <= bit < Int64.zwordsize ->
    Z.testbit (Int64.signed x) bit = Int64.testbit x bit.
Proof.
  intros x bit Hbit.
  change (Int64.testbit x bit) with (Z.testbit (Int64.unsigned x) bit).
  apply Int64.same_bits_eqm.
  - apply Int64.eqm_signed_unsigned.
  - exact Hbit.
Qed.

Lemma Z_land_ones_zero_divide_smod :
  forall x k,
    0 <= k ->
    Z.land x (Z.ones k) = 0 ->
    (2 ^ k | x).
Proof.
  intros x k Hk Hland.
  apply Znumtheory.Zmod_divide.
  - apply Z.pow_nonzero; lia.
  - rewrite <- Z.land_ones by auto.
    exact Hland.
Qed.

Lemma Z_rem_testbit_divide_smod :
  forall a b bit,
    b <> 0 ->
    0 <= bit ->
    (2 ^ (bit + 1) | b) ->
    Z.testbit (Z.rem a b) bit = Z.testbit a bit.
Proof.
  intros a b bit Hb Hbit Hdiv.
  apply Z_testbit_mod with (n := bit + 1).
  - lia.
  - apply Z_rem_mod_divide_smod with (d := 2 ^ (bit + 1)).
    + exact Hb.
    + apply Z.pow_nonzero; lia.
    + exact Hdiv.
Qed.

Lemma Int64_mods_low_bit_divide_smod :
  forall i j bit,
    j <> Int64.zero ->
    0 <= bit < Int64.zwordsize ->
    (2 ^ (bit + 1) | Int64.signed j) ->
    Int64.testbit (Int64.mods i j) bit = Int64.testbit i bit.
Proof.
  intros i j bit Hj Hbit Hdiv.
  rewrite testbit_mods_smod by auto.
  rewrite Z_rem_testbit_divide_smod.
  - apply Int64_signed_testbit_smod. exact Hbit.
  - apply Int64_signed_nonzero_smod. exact Hj.
  - lia.
  - exact Hdiv.
Qed.

Lemma smod_masked_low_bits_sound :
  forall a i j mask
         (MEMA : mem_tnum i a),
    j <> Int64.zero ->
    (forall bit,
        0 <= bit < Int64.zwordsize ->
        Int64.testbit mask bit = true ->
        (2 ^ (bit + 1) | Int64.signed j)) ->
    mem_tnum (Int64.mods i j)
      (Int64.and (fst a) mask,
       Int64.or (Int64.and (snd a) mask) (Int64.not mask)).
Proof.
  intros a i j mask MEMA Hj Hdiv.
  unfold mem_tnum in *.
  cbn [fst snd].
  apply Int64.same_bits_eq.
  intros bit Hbit.
  rewrite Int64.bits_and by auto.
  repeat rewrite Int64.bits_not by auto.
  rewrite Int64.bits_or by auto.
  rewrite Int64.bits_and by auto.
  rewrite Int64.bits_and by auto.
  repeat rewrite Int64.bits_not by auto.
  destruct (Int64.testbit mask bit) eqn:Hmask.
  - repeat rewrite Bool.andb_true_r.
    simpl.
    rewrite Bool.orb_false_r.
    rewrite Int64_mods_low_bit_divide_smod by eauto.
    assert (Hmem_bit :
      Int64.testbit (Int64.and i (Int64.not (snd a))) bit =
      Int64.testbit (fst a) bit).
    { rewrite MEMA. reflexivity. }
    rewrite Int64.bits_and in Hmem_bit by auto.
    rewrite Int64.bits_not in Hmem_bit by auto.
    exact Hmem_bit.
  - simpl.
    rewrite Bool.orb_true_r.
    repeat rewrite Bool.andb_false_r.
    reflexivity.
Qed.

Lemma Z_pow_divide_mono_smod :
  forall k n,
    0 <= k <= n ->
    (2 ^ k | 2 ^ n).
Proof.
  intros k n Hkn.
  exists (2 ^ (n - k)).
  rewrite <- Z.pow_add_r by lia.
  replace (n - k + k) with n by lia.
  reflexivity.
Qed.

Lemma Int64_signed_divide_unsigned_smod :
  forall j k,
    0 <= k <= Int64.zwordsize ->
    (2 ^ k | Int64.unsigned j) ->
    (2 ^ k | Int64.signed j).
Proof.
  intros j k Hk Hdiv.
  assert (Hmoddiv : (2 ^ k | Int64.modulus)).
  { change Int64.modulus with (2 ^ Int64.zwordsize).
    apply Z_pow_divide_mono_smod. exact Hk. }
  pose proof (Zbits.eqmod_divides _ _ _ _
                (Int64.eqm_signed_unsigned j) Hmoddiv) as Heqm.
  destruct Heqm as [q Hq].
  destruct Hdiv as [p Hp].
  exists (q + p).
  rewrite Hq, Hp.
  ring.
Qed.

Lemma Int64_unsigned_divide_signed_smod :
  forall j k,
    0 <= k <= Int64.zwordsize ->
    (2 ^ k | Int64.signed j) ->
    (2 ^ k | Int64.unsigned j).
Proof.
  intros j k Hk Hdiv.
  assert (Hmoddiv : (2 ^ k | Int64.modulus)).
  { change Int64.modulus with (2 ^ Int64.zwordsize).
    apply Z_pow_divide_mono_smod. exact Hk. }
  pose proof (Zbits.eqmod_divides _ _ _ _
                (Zbits.eqmod_sym _ _ _ (Int64.eqm_signed_unsigned j))
                Hmoddiv) as Heqm.
  destruct Heqm as [q Hq].
  destruct Hdiv as [p Hp].
  exists (q + p).
  rewrite Hq, Hp.
  ring.
Qed.

Lemma Int64_lsb_mask_testbit_smod :
  forall x bit,
    0 <= bit < Int64.zwordsize ->
    Int64.testbit
      (Int64.sub (Int64.and x (Int64.neg x)) Int64.one) bit =
    Z.testbit (Z.land (Int64.unsigned x) (- Int64.unsigned x) - 1) bit.
Proof.
  intros x bit Hbit.
  unfold Int64.sub.
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.unsigned_one.
  assert (Hlsb :
    Int64.unsigned (Int64.and x (Int64.neg x)) =
    Z.land (Int64.unsigned x) (- Int64.unsigned x)).
  { rewrite <- Zland_and.
    unfold Int64.neg.
    rewrite Z_land_Int64_unsigned.
    - reflexivity.
    - apply Int64.unsigned_range_2. }
  rewrite Hlsb.
  reflexivity.
Qed.

Lemma Z_pow2_minus_one_testbit_down_smod :
  forall p bit n,
    Z_pow2 p ->
    Z.testbit (p - 1) bit = true ->
    0 <= n <= bit ->
    Z.testbit (p - 1) n = true.
Proof.
  intros p bit n Hpow Hbit Hn.
  destruct Hpow as [_ [k [Hk Hp]]].
  subst p.
  replace (2 ^ k - 1) with (Z.ones k) in * by
    (rewrite Z.ones_equiv; reflexivity).
  destruct (Coqlib.zlt bit k) as [Hlt | Hge].
  - apply Z.ones_spec_low. lia.
  - rewrite Z.ones_spec_high in Hbit by lia.
    discriminate.
Qed.

Lemma Z_land_ones_zero_of_bits_smod :
  forall x k,
    0 <= k ->
    (forall n, 0 <= n < k -> Z.testbit x n = false) ->
    Z.land x (Z.ones k) = 0.
Proof.
  intros x k Hk Hbits.
  apply Z.bits_inj. unfold Z.eqf. intros n.
  rewrite Z.land_spec.
  rewrite Z.bits_0.
  destruct (Coqlib.zlt n 0) as [Hnneg | Hnnonneg].
  - rewrite Z.testbit_neg_r by exact Hnneg. reflexivity.
  - destruct (Coqlib.zlt n k) as [Hnlt | Hnge].
    + rewrite Hbits by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia.
      rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma mem_tnum_unsigned_bound_smod :
  forall i a,
    mem_tnum i a ->
    Int64.unsigned i <= Int64.unsigned (Int64.or (fst a) (snd a)).
Proof.
  intros i a MEMA.
  pose proof (mem_tnum_gamma _ _ MEMA) as Hgamma.
  assert (Hinv : tnum_ge_inv (to_tnumZ a)).
  { unfold tnum_ge_inv, to_tnumZ. cbn.
    split; [pose proof (Int64.unsigned_range_2 (fst a)) |
            pose proof (Int64.unsigned_range_2 (snd a))]; lia. }
  pose proof (tnum_ge_inv_gamma_bound _ _ Hgamma Hinv) as [_ Hub].
  pose proof (gamma_add_lor _ _ Hgamma) as Hlor.
  simpl in Hub.
  simpl in Hlor.
  rewrite Hlor in Hub.
  rewrite Zlor_or in Hub.
  exact Hub.
Qed.

Lemma Z_testbit_bound_ones_false_smod :
  forall x n bit,
    0 <= x ->
    0 <= n ->
    x <= Z.ones n ->
    n <= bit ->
    Z.testbit x bit = false.
Proof.
  intros x n bit Hx Hn Hbound Hbit.
  destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
  - subst. apply Z.bits_0.
  - apply Z.bits_above_log2.
    + exact Hx.
    + apply Z.log2_lt_pow2; try lia.
      rewrite Z.ones_equiv in Hbound.
      pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn).
      assert (2 ^ n <= 2 ^ bit) by (apply Z.pow_le_mono_r; lia).
      lia.
Qed.

Lemma Int64_mods_high_bits_smod :
  forall a i j bit,
    mem_tnum i a ->
    j <> Int64.zero ->
    Int64_size (Int64.or (fst a) (snd a)) <= bit < Int64.zwordsize ->
    Int64.testbit (Int64.mods i j) bit = false.
Proof.
  intros a i j bit MEMA Hj Hbit.
  set (amax := Int64.unsigned (Int64.or (fst a) (snd a))).
  set (size := Int64_size (Int64.or (fst a) (snd a))).
  pose proof (Int64.unsigned_range_2 (Int64.or (fst a) (snd a))) as Hamax_range.
  fold amax in Hamax_range.
  assert (Hsize_range : 0 <= size <= Int64.zwordsize).
  { subst size. apply Z_size_range_Int64_smod. exact Hamax_range. }
  rewrite testbit_mods_smod by lia.
  destruct (Z.eq_dec size Int64.zwordsize) as [Hsize64 | Hsize64].
  { lia. }
  assert (Hsize_lt : size < Int64.zwordsize) by lia.
  assert (Hamax_ones : amax <= Z.ones size).
  { subst size amax. apply Z_size_Z_upper_bound. lia. }
  assert (Hi_ub : Int64.unsigned i <= amax).
  { subst amax. apply mem_tnum_unsigned_bound_smod. exact MEMA. }
  assert (Hi_signed : Int64.signed i = Int64.unsigned i).
  { apply Int64.signed_eq_unsigned.
    unfold Int64.max_signed.
    rewrite Z.ones_equiv in Hamax_ones.
    change Int64.zwordsize with 64 in *.
    change Int64.half_modulus with (2 ^ 63).
    change Int64.max_signed with (2 ^ 63 - 1).
    assert (2 ^ size <= 2 ^ 63).
    { apply Z.pow_le_mono_r; lia. }
    lia. }
  rewrite Hi_signed.
  assert (Hj_signed : Int64.signed j <> 0).
  { apply Int64_signed_nonzero_smod. exact Hj. }
  assert (Hrem_nonneg : 0 <= Z.rem (Int64.unsigned i) (Int64.signed j)).
  { apply Z.rem_nonneg; auto.
    pose proof (Int64.unsigned_range_2 i). lia. }
  assert (Hrem_bound : Z.rem (Int64.unsigned i) (Int64.signed j) <= Int64.unsigned i).
  { rewrite <- (Z.rem_abs_r (Int64.unsigned i) (Int64.signed j)) by auto.
    apply Z.rem_le.
    - pose proof (Int64.unsigned_range_2 i). lia.
    - apply Z.abs_pos. exact Hj_signed. }
  apply Z_testbit_bound_ones_false_smod with (n := size).
  - exact Hrem_nonneg.
  - lia.
  - lia.
  - lia.
Qed.

Lemma mod_get_low_bits_smod_sound :
  forall a b i j
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    j <> Int64.zero ->
    mem_tnum (Int64.mods i j) (mod_get_low_bits a b).
Proof.
  intros a b i j MEMA MEMB Hj.
  unfold mod_get_low_bits, Int64_odd.
  destruct (Z.odd (Int64.unsigned (fst b)) ||
            Z.odd (Int64.unsigned (snd b))) eqn:Hodd.
  - unfold mem_tnum. cbn [fst snd].
    rewrite Int64.not_mone.
    rewrite Int64.and_zero.
    reflexivity.
  - eapply smod_masked_low_bits_sound; eauto.
    intros bit Hbit Hmask.
    apply Int64_signed_divide_unsigned_smod.
    { lia. }
    apply Z_land_ones_zero_divide_smod with (k := bit + 1).
    { lia. }
    apply Z_land_ones_zero_of_bits_smod.
    { lia. }
    intros n Hn.
    pose proof (mem_tnum_range _ _ MEMB) as Hb_range.
    set (bword := Int64.add (fst b) (snd b)) in *.
    assert (Hbword_unsigned :
      Int64.unsigned bword =
      Int64.unsigned (fst b) + Int64.unsigned (snd b)).
    { subst bword. apply Int64_unsigned_add. exact Hb_range. }
    assert (Hbword_pos : 0 < Int64.unsigned bword).
    { destruct (Z.eq_dec (Int64.unsigned bword) 0) as [Hbword0 | Hbword0].
      2:{ pose proof (Int64.unsigned_range_2 bword). lia. }
      exfalso. apply Hj.
      rewrite Hbword_unsigned in Hbword0.
      assert (Hfst0u : Int64.unsigned (fst b) = 0) by
        (pose proof (Int64.unsigned_range_2 (fst b));
         pose proof (Int64.unsigned_range_2 (snd b)); lia).
      assert (Hsnd0u : Int64.unsigned (snd b) = 0) by
        (pose proof (Int64.unsigned_range_2 (fst b));
         pose proof (Int64.unsigned_range_2 (snd b)); lia).
      assert (Hfst0 : fst b = Int64.zero).
      { rewrite <- (Int64.repr_unsigned (fst b)).
        rewrite Hfst0u. reflexivity. }
      assert (Hsnd0 : snd b = Int64.zero).
      { rewrite <- (Int64.repr_unsigned (snd b)).
        rewrite Hsnd0u. reflexivity. }
      unfold mem_tnum in MEMB.
      rewrite Hsnd0 in MEMB.
      rewrite Int64.not_zero in MEMB.
      rewrite Int64.and_mone in MEMB.
      rewrite Hfst0 in MEMB.
      exact MEMB. }
    assert (HmaskZbit :
      Z.testbit
        (Z.land (Int64.unsigned bword) (- Int64.unsigned bword) - 1)
        bit = true).
    { rewrite <- Int64_lsb_mask_testbit_smod by lia.
      exact Hmask. }
    assert (HmaskZn :
      Z.testbit
        (Z.land (Int64.unsigned bword) (- Int64.unsigned bword) - 1)
        n = true).
    { apply Z_pow2_minus_one_testbit_down_smod with (bit := bit).
      - apply Z_lsb_is_pow2. exact Hbword_pos.
      - exact HmaskZbit.
      - lia. }
    pose proof (Z_testbit_lt_lsb _ _ (proj1 Hn) HmaskZn) as Hbword_n.
    rewrite Hbword_unsigned in Hbword_n.
    pose proof (mem_tnum_gamma _ _ MEMB) as Hgb.
    pose proof (gamma_add_lor _ _ Hgb) as Hlor.
    simpl in Hlor.
    rewrite Hlor in Hbword_n.
    rewrite Z.lor_spec in Hbword_n.
    apply Bool.orb_false_iff in Hbword_n.
    destruct Hbword_n as [Hb_v_n Hb_m_n].
    rewrite <- (gamma_testbit_mask_false_Z _ _ _ _ Hgb Hb_m_n (proj1 Hn)).
    exact Hb_v_n.
Qed.

Lemma mem_tnum_and_mask_refine_smod :
  forall r res mask,
    mem_tnum r res ->
    (forall bit,
        0 <= bit < Int64.zwordsize ->
        Int64.testbit mask bit = false ->
        Int64.testbit r bit = false) ->
    mem_tnum r (Int64.and (fst res) mask, Int64.and (snd res) mask).
Proof.
  intros r res mask MEMR Hmasked.
  unfold mem_tnum in *.
  cbn [fst snd].
  apply Int64.same_bits_eq.
  intros bit Hbit.
  repeat rewrite Int64.bits_and by auto.
  repeat rewrite Int64.bits_not by auto.
  repeat rewrite Int64.bits_and by auto.
  assert (Hmem_bit :
    Int64.testbit (Int64.and r (Int64.not (snd res))) bit =
    Int64.testbit (fst res) bit).
  { rewrite MEMR. reflexivity. }
  rewrite Int64.bits_and in Hmem_bit by auto.
  rewrite Int64.bits_not in Hmem_bit by auto.
  destruct (Int64.testbit mask bit) eqn:Hmask.
  - repeat rewrite Bool.andb_true_r.
    exact Hmem_bit.
  - rewrite Hmasked by auto.
    repeat rewrite Bool.andb_false_l.
    repeat rewrite Bool.andb_false_r.
    reflexivity.
Qed.

Lemma mem_tnum_or_not_and_mask_refine_smod :
  forall r res mask,
    mem_tnum r res ->
    (forall bit,
        0 <= bit < Int64.zwordsize ->
        Int64.testbit mask bit = false ->
        Int64.testbit r bit = true) ->
    mem_tnum r (Int64.or (fst res) (Int64.not mask),
                Int64.and (snd res) mask).
Proof.
  intros r res mask MEMR Hmasked.
  unfold mem_tnum in *.
  cbn [fst snd].
  apply Int64.same_bits_eq.
  intros bit Hbit.
  repeat rewrite Int64.bits_and by auto.
  repeat rewrite Int64.bits_or by auto.
  repeat rewrite Int64.bits_not by auto.
  repeat rewrite Int64.bits_and by auto.
  assert (Hmem_bit :
    Int64.testbit (Int64.and r (Int64.not (snd res))) bit =
    Int64.testbit (fst res) bit).
  { rewrite MEMR. reflexivity. }
  rewrite Int64.bits_and in Hmem_bit by auto.
  rewrite Int64.bits_not in Hmem_bit by auto.
  destruct (Int64.testbit mask bit) eqn:Hmask.
  - repeat rewrite Bool.andb_true_r.
    rewrite Bool.orb_false_r.
    exact Hmem_bit.
  - rewrite Hmasked by auto.
    repeat rewrite Bool.andb_false_r.
    repeat rewrite Bool.andb_true_l.
    rewrite Bool.orb_true_r.
    reflexivity.
Qed.

Lemma tnum_smod_common_sound :
  forall a b i j
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    j <> Int64.zero ->
    mem_tnum (Int64.mods i j)
      (tnum_smod_high_bits a (mod_get_low_bits a b)).
Proof.
  intros a b i j MEMA MEMB Hj.
  eapply tnum_smod_high_bits_sound.
  - apply mod_get_low_bits_smod_sound; auto.
  - intros bit Hbit.
    eapply Int64_mods_high_bits_smod; eauto.
Qed.

Lemma tnum_known_eq_smod :
  forall j b,
    mem_tnum j b ->
    snd b = Int64.zero ->
    fst b = j.
Proof.
  intros.
  unfold mem_tnum in *.
  rewrite H0 in H.
  rewrite Int64.not_zero in H.
  rewrite Int64.and_mone in H.
  auto.
Qed.

Lemma Int64_nonzero_testbit_smod :
  forall x,
    x <> Int64.zero ->
    exists bit,
      0 <= bit < Int64.zwordsize /\
      Int64.testbit x bit = true.
Proof.
  intros x Hx.
  assert (Hunsigned_nonzero : Int64.unsigned x <> 0).
  { intro Hzero.
    apply Hx.
    rewrite <- (Int64.repr_unsigned x).
    rewrite Hzero.
    reflexivity. }
  assert (Hpos : 0 < Int64.unsigned x).
  { pose proof (Int64.unsigned_range_2 x). lia. }
  exists (Z.log2 (Int64.unsigned x)).
  split.
  - split.
    + apply Z.log2_nonneg.
    + pose proof (Int64.unsigned_range_2 x) as Hrange.
      apply Z.log2_lt_pow2.
      * exact Hpos.
      * change Int64.zwordsize with 64.
        change Int64.max_unsigned with (2 ^ 64 - 1) in Hrange.
        lia.
  - change (Int64.testbit x (Z.log2 (Int64.unsigned x))) with
      (Z.testbit (Int64.unsigned x) (Z.log2 (Int64.unsigned x))).
    apply Z.bit_log2. exact Hpos.
Qed.

Lemma Int64_pow2_unsigned_exponent_smod :
  forall x,
    Int64_is_pow2 x = true ->
    exists k,
      0 <= k <= Int64.zwordsize - 1 /\
      Int64.unsigned x = 2 ^ k.
Proof.
  intros x Hpow.
  unfold Int64_is_pow2 in Hpow.
  apply Z_pow2_equiv in Hpow.
  destruct Hpow as [_ [k [Hk Hx]]].
  exists k. split; auto.
  pose proof (Int64.unsigned_range_2 x) as Hrange.
  rewrite <- Hx in Hrange.
  change Int64.zwordsize with 64.
  assert (k < 64).
  { destruct (Coqlib.zlt k 64); auto.
    assert (2 ^ 64 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
    change Int64.max_unsigned with (2 ^ 64 - 1) in Hrange.
    lia. }
  lia.
Qed.

Lemma Int64_pow2_low_bits_false_ge_smod :
  forall x k bit,
    Int64.unsigned x = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    0 <= bit < Int64.zwordsize ->
    Int64.testbit (Int64.sub x Int64.one) bit = false ->
    k <= bit.
Proof.
  intros x k bit Hx Hk Hbit Hmask.
  destruct (Coqlib.zlt bit k) as [Hlt | Hge]; try lia.
  exfalso.
  unfold Int64.sub in Hmask.
  rewrite Int64.testbit_repr in Hmask by auto.
  rewrite Hx, Int64.unsigned_one in Hmask.
  replace (2 ^ k - 1) with (Z.ones k) in Hmask by
    (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.ones_spec_low in Hmask by lia.
  discriminate.
Qed.

Lemma Int64_pow2_low_bits_true_lt_smod :
  forall x k bit,
    Int64.unsigned x = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    0 <= bit < Int64.zwordsize ->
    Int64.testbit (Int64.sub x Int64.one) bit = true ->
    bit < k.
Proof.
  intros x k bit Hx Hk Hbit Hmask.
  unfold Int64.sub in Hmask.
  rewrite Int64.testbit_repr in Hmask by auto.
  rewrite Hx, Int64.unsigned_one in Hmask.
  replace (2 ^ k - 1) with (Z.ones k) in Hmask by
    (rewrite Z.ones_equiv; reflexivity).
  destruct (Coqlib.zlt bit k) as [Hlt | Hge]; auto.
  rewrite Z.ones_spec_high in Hmask by lia.
  discriminate.
Qed.

Lemma Int64_pow2_abs_signed_smod :
  forall x k,
    Int64.unsigned x = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    Z.abs (Int64.signed x) = 2 ^ k.
Proof.
  intros x k Hx Hk.
  unfold Int64.signed.
  rewrite Hx.
  destruct (Coqlib.zlt (2 ^ k) Int64.half_modulus) as [Hlt | Hge].
  - apply Z.abs_eq. lia.
  - change Int64.half_modulus with (2 ^ 63) in Hge.
    change Int64.modulus with (2 ^ 64).
    change Int64.zwordsize with 64 in Hk.
    assert (k = 63).
    { destruct (Coqlib.zlt k 63); auto.
      - assert (2 ^ k < 2 ^ 63) by (apply Z.pow_lt_mono_r; lia).
        lia.
      - lia. }
    subst k.
    replace (2 ^ 63 - 2 ^ 64) with (-(2 ^ 63)) by lia.
    rewrite Z.abs_opp.
    apply Z.abs_eq. lia.
Qed.

Lemma Z_testbit_negative_bound_true_smod :
  forall x k bit,
    0 <= bit ->
    x < 0 ->
    Z.abs x < 2 ^ k ->
    k <= bit ->
    Z.testbit x bit = true.
Proof.
  intros x k bit Hbit_nonneg Hx Habs Hbit.
  destruct (Z.eq_dec x (-1)) as [Hx_m1 | Hx_m1].
  - subst x.
    apply Z_testbit_neg_1.
    exact Hbit_nonneg.
  - apply Z.bits_above_log2_neg.
    + exact Hx.
    + apply Z.log2_lt_pow2.
      * assert (1 < - x) by lia.
        unfold Z.pred. lia.
      * unfold Z.pred.
        rewrite (Z.abs_neq x) in Habs by lia.
        assert (2 ^ k <= 2 ^ bit) by (apply Z.pow_le_mono_r; lia).
        lia.
Qed.

Lemma Z_abs_divisor_divide_smod :
  forall d x p,
    Z.abs d = p ->
    (p | x) ->
    (d | x).
Proof.
  intros d x p Habs [q Hq].
  subst x.
  destruct (Coqlib.zlt d 0) as [Hdneg | Hdnonneg].
  - exists (-q).
    rewrite (Z.abs_neq d) in Habs by lia.
    lia.
  - exists q.
    rewrite (Z.abs_eq d) in Habs by lia.
    lia.
Qed.

Lemma Int64_and_pow2_low_bits_zero_divide_signed_smod :
  forall i j k,
    Int64.unsigned j = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    Int64.and i (Int64.sub j Int64.one) = Int64.zero ->
    (Int64.signed j | Int64.signed i).
Proof.
  intros i j k Hj Hk Hand.
  apply Z_abs_divisor_divide_smod with (p := 2 ^ k).
  - apply Int64_pow2_abs_signed_smod; auto.
  - apply Int64_signed_divide_unsigned_smod.
    + change Int64.zwordsize with 64 in *. lia.
    + apply Z_land_ones_zero_divide_smod.
      * lia.
      * apply Z_land_ones_zero_of_bits_smod.
        { lia. }
        intros n Hn.
        assert (Hlow : Int64.testbit (Int64.sub j Int64.one) n = true).
        { unfold Int64.sub.
          rewrite Int64.testbit_repr by (change Int64.zwordsize with 64 in *; lia).
          rewrite Hj, Int64.unsigned_one.
          replace (2 ^ k - 1) with (Z.ones k) by
            (rewrite Z.ones_equiv; reflexivity).
          apply Z.ones_spec_low. lia. }
        assert (Hzero_bit :
          Int64.testbit (Int64.and i (Int64.sub j Int64.one)) n =
          Int64.testbit Int64.zero n).
        { rewrite Hand. reflexivity. }
        rewrite Int64.bits_and in Hzero_bit by (change Int64.zwordsize with 64 in *; lia).
        rewrite Int64.bits_zero in Hzero_bit by (change Int64.zwordsize with 64 in *; lia).
        rewrite Hlow in Hzero_bit.
        rewrite Bool.andb_true_r in Hzero_bit.
        exact Hzero_bit.
Qed.

Lemma Int64_mods_pow2_nonneg_high_false_smod :
  forall i j k bit,
    Int64.unsigned j = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    j <> Int64.zero ->
    0 <= Int64.signed i ->
    k <= bit < Int64.zwordsize ->
    Int64.testbit (Int64.mods i j) bit = false.
Proof.
  intros i j k bit Hj Hk Hj_nonzero Hi_nonneg Hbit.
  rewrite testbit_mods_smod by lia.
  assert (Hj_signed_nonzero : Int64.signed j <> 0).
  { apply Int64_signed_nonzero_smod. exact Hj_nonzero. }
  set (r := Z.rem (Int64.signed i) (Int64.signed j)).
  assert (Hr_nonneg : 0 <= r).
  { subst r. apply Z.rem_nonneg; auto. }
  assert (Hr_abs : Z.abs r < 2 ^ k).
  { subst r.
    rewrite <- (Int64_pow2_abs_signed_smod j k Hj Hk).
    apply Z.rem_bound_abs. exact Hj_signed_nonzero. }
  assert (Hr_bound : r <= Z.ones k).
  { rewrite Z.ones_equiv.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
    rewrite (Z.abs_eq r) in Hr_abs by lia.
    lia. }
  apply Z_testbit_bound_ones_false_smod with (n := k).
  - exact Hr_nonneg.
  - lia.
  - exact Hr_bound.
  - lia.
Qed.

Lemma Int64_mods_divisor_zero_smod :
  forall i j,
    j <> Int64.zero ->
    (Int64.signed j | Int64.signed i) ->
    Int64.mods i j = Int64.zero.
Proof.
  intros i j Hj Hdiv.
  apply Int64.same_bits_eq.
  intros bit Hbit.
  rewrite testbit_mods_smod by auto.
  rewrite Int64.bits_zero by auto.
  assert (Hj_signed_nonzero : Int64.signed j <> 0).
  { apply Int64_signed_nonzero_smod. exact Hj. }
  rewrite (proj2 (Z.rem_divide _ _ Hj_signed_nonzero) Hdiv).
  apply Z.bits_0.
Qed.

Lemma Z_divide_abs_divisor_smod :
  forall d x,
    (d | x) ->
    (Z.abs d | x).
Proof.
  intros d x [q Hq].
  destruct (Coqlib.zlt d 0) as [Hdneg | Hdnonneg].
  - exists (-q).
    rewrite (Z.abs_neq d) by lia.
    lia.
  - exists q.
    rewrite (Z.abs_eq d) by lia.
    exact Hq.
Qed.

Lemma mem_tnum_low_value_nonzero_not_divide_pow2_smod :
  forall a i j k,
    mem_tnum i a ->
    Int64.unsigned j = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    Int64.and (fst a) (Int64.sub j Int64.one) <> Int64.zero ->
    ~ (2 ^ k | Int64.signed i).
Proof.
  intros a i j k MEMA Hj Hk Hnz Hdiv_signed.
  apply Hnz.
  apply Int64.same_bits_eq.
  intros bit Hbit.
  rewrite Int64.bits_and by auto.
  rewrite Int64.bits_zero by auto.
  destruct (Int64.testbit (Int64.sub j Int64.one) bit) eqn:Hmask.
  2:{ rewrite Bool.andb_false_r. reflexivity. }
  assert (Hbit_lt : bit < k).
  { eapply Int64_pow2_low_bits_true_lt_smod; eauto. }
  assert (Hdiv_unsigned : (2 ^ k | Int64.unsigned i)).
  { apply Int64_unsigned_divide_signed_smod.
    - change Int64.zwordsize with 64 in *. lia.
    - exact Hdiv_signed. }
  assert (Hi_low_zero : Z.land (Int64.unsigned i) (Z.ones k) = 0).
  { rewrite Z.land_ones by lia.
    apply Znumtheory.Zdivide_mod. exact Hdiv_unsigned. }
  assert (Hi_bit_false : Int64.testbit i bit = false).
  { assert (Hzero_bit :
      Z.testbit (Z.land (Int64.unsigned i) (Z.ones k)) bit =
      Z.testbit 0 bit).
    { rewrite Hi_low_zero. reflexivity. }
    rewrite Z.land_spec in Hzero_bit.
    rewrite Z.ones_spec_low in Hzero_bit by lia.
    rewrite Z.bits_0 in Hzero_bit.
    rewrite Bool.andb_true_r in Hzero_bit.
    exact Hzero_bit. }
  unfold mem_tnum in MEMA.
  assert (Hmem_bit :
    Int64.testbit (Int64.and i (Int64.not (snd a))) bit =
    Int64.testbit (fst a) bit).
  { rewrite MEMA. reflexivity. }
  rewrite Int64.bits_and in Hmem_bit by auto.
  rewrite Int64.bits_not in Hmem_bit by auto.
  rewrite Hi_bit_false in Hmem_bit.
  simpl in Hmem_bit.
  rewrite <- Hmem_bit.
  reflexivity.
Qed.

Lemma Int64_mods_pow2_negative_high_true_smod :
  forall i j k bit,
    Int64.unsigned j = 2 ^ k ->
    0 <= k <= Int64.zwordsize - 1 ->
    j <> Int64.zero ->
    Int64.signed i < 0 ->
    ~ (Int64.signed j | Int64.signed i) ->
    k <= bit < Int64.zwordsize ->
    Int64.testbit (Int64.mods i j) bit = true.
Proof.
  intros i j k bit Hj Hk Hj_nonzero Hi_neg Hnot_div Hbit.
  rewrite testbit_mods_smod by lia.
  assert (Hj_signed_nonzero : Int64.signed j <> 0).
  { apply Int64_signed_nonzero_smod. exact Hj_nonzero. }
  set (r := Z.rem (Int64.signed i) (Int64.signed j)).
  assert (Hr_nonzero : r <> 0).
  { intro Hr0. apply Hnot_div.
    apply (proj1 (Z.rem_divide _ _ Hj_signed_nonzero)).
    subst r. exact Hr0. }
  assert (Hr_nonpos : r <= 0).
  { subst r. apply Z.rem_nonpos; lia. }
  assert (Hr_neg : r < 0) by lia.
  assert (Hr_abs : Z.abs r < 2 ^ k).
  { subst r.
    rewrite <- (Int64_pow2_abs_signed_smod j k Hj Hk).
    apply Z.rem_bound_abs. exact Hj_signed_nonzero. }
  apply Z_testbit_negative_bound_true_smod with (k := k).
  - lia.
  - exact Hr_neg.
  - exact Hr_abs.
  - lia.
Qed.

Lemma tnum_smod_pow2_sound :
  forall a b i j
         (MEMA : mem_tnum i a)
         (MEMB : mem_tnum j b),
    snd b = Int64.zero ->
    Int64_is_pow2 (fst b) = true ->
    mem_tnum (Int64.mods i j) (tnum_smod_pow2 a b).
Proof.
  intros a b i j MEMA MEMB Hb_mask Hpow2.
  unfold tnum_smod_pow2.
  set (res := mod_get_low_bits a b).
  set (low_bits := Int64.sub (fst b) Int64.one).
  assert (Hb_eq : fst b = j).
  { eapply tnum_known_eq_smod; eauto. }
  assert (Hj_nonzero : j <> Int64.zero).
  { intro Hj0.
    unfold Int64_is_pow2, Z_is_pow2 in Hpow2.
    rewrite Hb_eq in Hpow2.
    rewrite Hj0 in Hpow2.
    rewrite Int64.unsigned_zero in Hpow2.
    simpl in Hpow2.
    discriminate. }
  assert (Hres : mem_tnum (Int64.mods i j) res).
  { subst res. eapply mod_get_low_bits_smod_sound; eauto. }
  destruct (Int64_pow2_unsigned_exponent_smod _ Hpow2)
    as [k [Hk Hfst_unsigned]].
  assert (Hj_unsigned : Int64.unsigned j = 2 ^ k).
  { rewrite <- Hb_eq. exact Hfst_unsigned. }
  destruct (tnum_nonnegative a || tnum_low_bits_zero a low_bits) eqn:Hcase1.
  - eapply mem_tnum_and_mask_refine_smod; eauto.
    intros bit Hbit Hmask.
    assert (Hkbit : k <= bit).
    { eapply Int64_pow2_low_bits_false_ge_smod with (x := fst b).
      - exact Hfst_unsigned.
      - exact Hk.
      - exact Hbit.
      - subst low_bits. exact Hmask. }
    apply Bool.orb_true_iff in Hcase1.
    destruct Hcase1 as [Hnonneg | Hlowzero].
    + eapply Int64_mods_pow2_nonneg_high_false_smod.
      * exact Hj_unsigned.
      * exact Hk.
      * exact Hj_nonzero.
      * apply tnum_nonnegative_sound with (a := a); auto.
      * lia.
    + assert (Hlowzero_i : Int64.and i low_bits = Int64.zero).
      { apply tnum_low_bits_zero_sound with (a := a); auto. }
      assert (Hmods0 : Int64.mods i j = Int64.zero).
      { apply Int64_mods_divisor_zero_smod.
        - exact Hj_nonzero.
        - eapply Int64_and_pow2_low_bits_zero_divide_signed_smod with (k := k).
          + exact Hj_unsigned.
          + exact Hk.
          + subst low_bits.
            rewrite <- Hb_eq.
            exact Hlowzero_i. }
      rewrite Hmods0; apply Int64.bits_zero; exact Hbit.
  - destruct (tnum_negative a &&
              negb (Int64.eq (Int64.and (fst a) low_bits) Int64.zero)) eqn:Hcase2.
    + eapply mem_tnum_or_not_and_mask_refine_smod; eauto.
      intros bit Hbit Hmask.
      assert (Hkbit : k <= bit).
      { eapply Int64_pow2_low_bits_false_ge_smod with (x := fst b).
        - exact Hfst_unsigned.
        - exact Hk.
        - exact Hbit.
        - subst low_bits. exact Hmask. }
      apply Bool.andb_true_iff in Hcase2.
      destruct Hcase2 as [Hneg Hlow_nonzero_bool].
      apply negb_true_iff in Hlow_nonzero_bool.
      assert (Hlow_nonzero :
        Int64.and (fst a) low_bits <> Int64.zero).
      { intro Hzero.
        rewrite Hzero in Hlow_nonzero_bool.
        rewrite Int64.eq_true in Hlow_nonzero_bool.
        discriminate. }
      eapply Int64_mods_pow2_negative_high_true_smod.
      * exact Hj_unsigned.
      * exact Hk.
      * exact Hj_nonzero.
      * apply tnum_negative_sound with (a := a); auto.
      * intro Hdivj.
        apply (mem_tnum_low_value_nonzero_not_divide_pow2_smod
                 a i j k MEMA Hj_unsigned Hk).
        -- subst low_bits. rewrite Hb_eq in Hlow_nonzero. exact Hlow_nonzero.
        -- apply Z_divide_abs_divisor_smod in Hdivj.
           rewrite (Int64_pow2_abs_signed_smod j k Hj_unsigned Hk) in Hdivj.
           exact Hdivj.
      * lia.
    + exact Hres.
Qed.

Lemma mem_tnum_zero_smod :
  forall i,
    mem_tnum i (i, Int64.zero).
Proof.
  unfold mem_tnum; intros.
  simpl.
  rewrite Int64.not_zero.
  rewrite Int64.and_mone.
  auto.
Qed.

Lemma tnum_unknown_gamma_smod :
  forall i, mem_tnum i (Int64.zero, Int64.mone).
Proof.
  intros. unfold mem_tnum. simpl.
  rewrite Int64.not_mone.
  rewrite Int64.and_zero.
  reflexivity.
Qed.

Theorem tnum_smod_sound :
  forall a b i j
    (H_dst: gamma_val i a)
    (H_src: gamma_val j b),
  gamma_val (eval_mod_s64 i j) (tnum_smod a b).
Proof.
  intros.
  destruct i as [ | | i | | | ]; simpl in H_dst; try contradiction.
  destruct j as [ | | j | | | ]; simpl in H_src; try contradiction.
  unfold tnum_smod.
  rewrite (surjective_pairing a), (surjective_pairing b).
  unfold gamma_val.
  assert (H_dst_pair : mem_tnum i (fst a, snd a)) by
    (rewrite <- (surjective_pairing a); exact H_dst).
  assert (H_src_pair : mem_tnum j (fst b, snd b)) by
    (rewrite <- (surjective_pairing b); exact H_src).
  destruct (Int64.eq (snd b) Int64.zero) eqn:Hb_m.
  {
    apply Int64.same_if_eq in Hb_m.
    apply tnum_known_eq_smod in H_src as Hb_eq; auto.
    destruct (Int64.eq (fst b) Int64.zero) eqn:Hb_v.
    - apply Int64.same_if_eq in Hb_v.
      rewrite Hb_eq in *.
      subst j.
      rewrite Hb_v.
      unfold eval_mod_s64; simpl.
      simpl.
      destruct (Val.eq (Vlong Int64.zero) (Vlong Int64.zero)) as [_ | Hneq].
      + exact H_dst.
      + exfalso. apply Hneq; auto.
    - destruct (Int64.eq (snd a) Int64.zero) eqn:Ha_m.
      + apply Int64.same_if_eq in Ha_m.
        apply tnum_known_eq_smod in H_dst as Ha_eq; auto.
        subst i.
        subst j.
        unfold eval_mod_s64; simpl.
        destruct (Int64.eq (fst b) Int64.zero
                  || Int64.eq (fst a) (Int64.repr Int64.min_signed)
                     && Int64.eq (fst b) Int64.mone) eqn:Hmod.
        * rewrite orb_true_iff in Hmod.
          destruct Hmod as [Hb_zero | Hover].
          -- rewrite Hb_v in Hb_zero. discriminate.
          -- rewrite andb_true_iff in Hover.
             destruct Hover as [Ha_min Hb_mone].
             apply Int64.same_if_eq in Ha_min, Hb_mone.
             rewrite Ha_min, Hb_mone.
             rewrite Int64_mods_min_mone_zero.
             apply mem_tnum_zero_smod.
        * apply mem_tnum_zero_smod.
      + destruct (Int64_is_pow2 (fst b)) eqn:Hpow2.
        * unfold eval_mod_s64; simpl.
          destruct (Int64.eq j Int64.zero
                    || Int64.eq i (Int64.repr Int64.min_signed)
                       && Int64.eq j Int64.mone) eqn:Hmod.
          -- rewrite orb_true_iff in Hmod.
             destruct Hmod as [Hj_zero | Hover].
             ++ apply Int64.same_if_eq in Hj_zero.
                rewrite Hb_eq in Hb_v.
                rewrite Hj_zero in Hb_v.
                rewrite Int64.eq_true in Hb_v.
                discriminate.
             ++ rewrite andb_true_iff in Hover.
                destruct Hover as [Hi_min Hj_mone].
                apply Int64.same_if_eq in Hi_min, Hj_mone.
                subst i; subst j.
                rewrite Hj_mone in *.
                simpl.
                destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.zero)) as [Heq | Heq].
                { inversion Heq. }
                simpl.
                destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [Heq_mone | Hneq].
                2:{ exfalso. apply Hneq; auto. }
                simpl.
                unfold LLONG_MIN.
                destruct (Val.eq (Vlong (Int64.repr Int64.min_signed))
                                 (Vlong (Int64.repr Int64.min_signed))) as [Heq_min | Hneq].
                2:{ exfalso. apply Hneq; auto. }
                simpl.
                rewrite <- Int64_mods_min_mone_zero.
                eapply tnum_smod_pow2_sound; eauto.
          -- eapply tnum_smod_pow2_sound; eauto.
        * unfold eval_mod_s64; simpl.
          destruct (Int64.eq j Int64.zero
                    || Int64.eq i (Int64.repr Int64.min_signed)
                       && Int64.eq j Int64.mone) eqn:Hmod.
          -- rewrite orb_true_iff in Hmod.
             destruct Hmod as [Hj_zero | Hover].
             ++ apply Int64.same_if_eq in Hj_zero.
                rewrite Hb_eq in Hb_v.
                rewrite Hj_zero in Hb_v.
                rewrite Int64.eq_true in Hb_v.
                discriminate.
             ++ rewrite andb_true_iff in Hover.
                destruct Hover as [Hi_min Hj_mone].
                apply Int64.same_if_eq in Hi_min, Hj_mone.
                subst i; subst j.
                rewrite Hj_mone in *.
                simpl.
                destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.zero)) as [Heq | Heq].
                { inversion Heq. }
                simpl.
                destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [Heq_mone | Hneq].
                2:{ exfalso. apply Hneq; auto. }
                simpl.
                unfold LLONG_MIN.
                destruct (Val.eq (Vlong (Int64.repr Int64.min_signed))
                                 (Vlong (Int64.repr Int64.min_signed))) as [Heq_min | Hneq].
                2:{ exfalso. apply Hneq; auto. }
                simpl.
                rewrite <- Int64_mods_min_mone_zero.
                eapply tnum_smod_common_sound; eauto.
                discriminate.
          -- eapply tnum_smod_common_sound; eauto.
             intro Hj_eq.
             rewrite Hj_eq in Hmod.
             simpl in Hmod.
             discriminate.
  }
  {
    destruct (Int64.eq (fst b) Int64.zero) eqn:Hb_v.
    - unfold eval_mod_s64; simpl.
      destruct (Int64.eq j Int64.zero
                || Int64.eq i (Int64.repr Int64.min_signed)
                   && Int64.eq j Int64.mone) eqn:Hmod.
      + rewrite orb_true_iff in Hmod.
        destruct Hmod as [Hj_zero | Hover].
        * apply Int64.same_if_eq in Hj_zero.
          subst j.
          destruct (Val.eq (Vlong Int64.zero) (Vlong Int64.zero)) as [_ | Hneq].
          -- simpl. apply tnum_unknown_gamma_smod.
          -- exfalso. apply Hneq; auto.
        * rewrite andb_true_iff in Hover.
          destruct Hover as [Hi_min Hj_mone].
          apply Int64.same_if_eq in Hi_min, Hj_mone.
          subst i; subst j.
          simpl.
          destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.zero)) as [Heq | Heq].
          { inversion Heq. }
          simpl.
          destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [Heq_mone | Hneq].
          2:{ exfalso. apply Hneq; auto. }
          simpl.
          unfold LLONG_MIN.
          destruct (Val.eq (Vlong (Int64.repr Int64.min_signed))
                           (Vlong (Int64.repr Int64.min_signed))) as [Heq_min | Hneq].
          2:{ exfalso. apply Hneq; auto. }
          simpl. apply tnum_unknown_gamma_smod.
      + apply tnum_unknown_gamma_smod.
    - unfold eval_mod_s64; simpl.
      destruct (Int64.eq j Int64.zero
                || Int64.eq i (Int64.repr Int64.min_signed)
                   && Int64.eq j Int64.mone) eqn:Hmod.
      + rewrite orb_true_iff in Hmod.
        destruct Hmod as [Hj_zero | Hover].
        * apply Int64.same_if_eq in Hj_zero.
          exfalso.
          subst j.
          unfold mem_tnum in H_src_pair; simpl in H_src_pair.
          rewrite Int64.and_zero_l in H_src_pair.
          rewrite <- H_src_pair in Hb_v.
          rewrite Int64.eq_true in Hb_v.
          discriminate.
        * rewrite andb_true_iff in Hover.
          destruct Hover as [Hi_min Hj_mone].
          apply Int64.same_if_eq in Hi_min, Hj_mone.
          subst i; subst j.
          simpl.
          destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.zero)) as [Heq | Heq].
          { inversion Heq. }
          simpl.
          destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [Heq_mone | Hneq].
          2:{ exfalso. apply Hneq; auto. }
          simpl.
          unfold LLONG_MIN.
          destruct (Val.eq (Vlong (Int64.repr Int64.min_signed))
                           (Vlong (Int64.repr Int64.min_signed))) as [Heq_min | Hneq].
          2:{ exfalso. apply Hneq; auto. }
          simpl.
          rewrite <- Int64_mods_min_mone_zero.
          eapply tnum_smod_common_sound; eauto.
          discriminate.
      + eapply tnum_smod_common_sound; eauto.
        intro Hj_eq.
        rewrite Hj_eq in Hmod.
        simpl in Hmod.
        discriminate.
  }
Qed.

Theorem tnum_neg_mem_sound :
  forall a i
         (MEMA : mem_tnum i a),
    mem_tnum (Int64.neg i) (tnum_neg a).
Proof.
  intros.
  unfold tnum_neg.
  rewrite <- Int64.sub_zero_r.
  apply tnum_sub_mem_sound.
  - unfold mem_tnum. reflexivity.
  - apply MEMA.
Qed.

Theorem tnum_neg_sound :
  forall a dst,
    gamma_val dst a ->
    gamma_val (Val.negl dst) (tnum_neg a).
Proof.
  intros a dst Hdst.
  destruct dst; simpl in Hdst; try contradiction.
  simpl. apply tnum_neg_mem_sound. exact Hdst.
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

Lemma calc_neg_pos_sound: forall a b i j a_neg b_pos res,
  mem_tnum i a -> mem_tnum j b ->
  Int64.signed i < 0 -> Int64.signed j >= 0 ->
  tnum_get_negative a = Some a_neg ->
  tnum_get_positive b = Some b_pos ->
  calc_neg_pos_opt (Some a_neg) (Some b_pos) = Some res -> 
  mem_tnum (Int64.divs i j) res.
Proof.
  intros a b i j a_neg b_pos res Hmem_a Hmem_b Hsign_i Hsign_j Hneg_a Hpos_b Hcalc.
  
  Ltac msb_to_testbit H :=
    unfold Int64_msb in H;
    (rewrite Clt_Zlt_signed in H || rewrite Clt_Zlt_signed_false in H);
    change (Int64.signed Int64.zero) with 0 in H;
    (apply testbit_sign_neg in H || apply testbit_sign_pos in H).

  unfold calc_neg_pos_opt in Hcalc.
  destruct (Int64.ltu (get_signed_max b_pos) (Int64.neg (get_signed_max a_neg))) eqn:Hltu.
  - injection Hcalc as <-.
    unfold mem_tnum; simpl.
    apply Int64.same_bits_eq; intros n Hn.
    rewrite !Int64.bits_and by lia.
    rewrite !Int64.bits_not by lia.
    unfold Int64_ones, Int64_size.
    rewrite !Int64.testbit_repr by auto.
    
    match goal with
    | |- context [ Z.ones (Z_size_Z (Int64.unsigned ?X)) ] => set (min_val := X) in *
    end.
    
    assert (Hzsize: 0 <= Z_size_Z (Int64.unsigned min_val)).
    { apply Z_size_range_Int64. pose proof (Int64.unsigned_range min_val). unfold Int64.max_unsigned; lia. }
    
    destruct (Coqlib.zlt n (Z_size_Z (Int64.unsigned min_val))) as [Hlt | Hge].
    + rewrite !Z.ones_spec_low by lia.
      destruct (Int64.testbit (Int64.divs i j) n); reflexivity.
    + rewrite !Z.ones_spec_high by lia.
      exfalso.

      assert (H_a_neg_max_neg: Int64.signed (get_signed_max a_neg) < 0).
      {
        unfold get_signed_max, tnum_get_negative in *.
        destruct a as [v m]. destruct (Int64_msb v) eqn:Hv.
        - injection Hneg_a as <-. simpl. apply testbit_sign_neg.
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). msb_to_testbit Hv. rewrite Hv. auto.
        - destruct (Int64_msb m) eqn:Hm.
          + injection Hneg_a as <-. simpl. apply testbit_sign_neg.
            rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia).
            unfold Int64_min_signed.
            change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
            destruct (Int64.testbit v (Int64.zwordsize - 1)); auto.
          + discriminate.
      }

      assert (H_b_pos_max_pos: 0 <= Int64.signed (get_signed_max b_pos)).
      {
        unfold get_signed_max, tnum_get_positive in *.
        destruct b as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
        destruct (Int64_msb m) eqn:Hm.
        - injection Hpos_b as <-. simpl. apply testbit_sign_pos.
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia).
          rewrite !Int64.bits_and by (change Int64.zwordsize with 64; lia).
          unfold Int64_min_signed.
          change (Int64.testbit (Int64.not (Int64.repr Int64.min_signed)) (Int64.zwordsize - 1)) with false.
          rewrite andb_false_r. rewrite orb_false_r. msb_to_testbit Hv. exact Hv.
        - injection Hpos_b as <-. simpl. apply testbit_sign_pos.
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). msb_to_testbit Hv. msb_to_testbit Hm. rewrite Hv, Hm. auto.
      }

      assert (H_min_le_max_a: Int64.signed (get_signed_min a_neg) <= Int64.signed (get_signed_max a_neg)).
      {
        unfold get_signed_min, get_signed_max.
        assert (H_not_or: Int64.not (Int64.or (fst a_neg) (snd a_neg)) = Int64.and (Int64.not (fst a_neg)) (Int64.not (snd a_neg))).
        { apply Int64.same_bits_eq; intros n0 Hn0.
          rewrite Int64.bits_not, Int64.bits_and, !Int64.bits_not, !Int64.bits_or by auto.
          destruct (Int64.testbit (fst a_neg) n0), (Int64.testbit (snd a_neg) n0); auto. }
        pose proof (Int64.unsigned_not (fst a_neg)) as Hnot_f.
        pose proof (Int64.unsigned_not (Int64.or (fst a_neg) (snd a_neg))) as Hnot_or.
        rewrite H_not_or in Hnot_or. rewrite <- Zland_and in Hnot_or.
        
        assert (H_pos1: 0 <= Int64.unsigned (Int64.not (fst a_neg))) by (pose proof (Int64.unsigned_range (Int64.not (fst a_neg))); lia).
        assert (H_pos2: 0 <= Int64.unsigned (Int64.not (snd a_neg))) by (pose proof (Int64.unsigned_range (Int64.not (snd a_neg))); lia).
        pose proof (land_ub (Int64.unsigned (Int64.not (fst a_neg))) (Int64.unsigned (Int64.not (snd a_neg))) H_pos1 H_pos2).

        unfold Int64.signed.
        pose proof (Int64.unsigned_range (fst a_neg)).
        pose proof (Int64.unsigned_range (Int64.or (fst a_neg) (snd a_neg))).
        assert (H_sign_min: Int64.signed (fst a_neg) < 0).
        {
          unfold tnum_get_negative in Hneg_a.
          destruct a as [v m]. destruct (Int64_msb v) eqn:Hv.
          - injection Hneg_a as <-. simpl. apply testbit_sign_neg. msb_to_testbit Hv. exact Hv.
          - destruct (Int64_msb m) eqn:Hm.
            + injection Hneg_a as <-. simpl. apply testbit_sign_neg.
              rewrite !Int64.bits_or by lia. unfold Int64_min_signed.
              change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
              destruct (Int64.testbit v (Int64.zwordsize - 1)); auto.
            + discriminate.
        }
        apply testbit_sign_neg in H_sign_min.
        assert (H_msb_f: Int64.testbit (fst a_neg) (Int64.zwordsize - 1) = true) by exact H_sign_min.
        assert (H_msb_or: Int64.testbit (Int64.or (fst a_neg) (snd a_neg)) (Int64.zwordsize - 1) = true).
        { rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). rewrite H_msb_f. apply orb_true_l. }
        apply testbit_sign_neg in H_msb_f. apply testbit_sign_neg in H_msb_or.
        
        unfold Int64.signed in *.
        destruct (Coqlib.zlt (Int64.unsigned (fst a_neg)) Int64.half_modulus);
        destruct (Coqlib.zlt (Int64.unsigned (Int64.or (fst a_neg) (snd a_neg))) Int64.half_modulus);
        lia.
      }

      assert (H_min_le_max_b: Int64.signed (get_signed_min b_pos) <= Int64.signed (get_signed_max b_pos)).
      {
        unfold get_signed_min, get_signed_max.
        assert (H_not_or: Int64.not (Int64.or (fst b_pos) (snd b_pos)) = Int64.and (Int64.not (fst b_pos)) (Int64.not (snd b_pos))).
        { apply Int64.same_bits_eq; intros n0 Hn0.
          rewrite Int64.bits_not, Int64.bits_and, !Int64.bits_not, !Int64.bits_or by auto.
          destruct (Int64.testbit (fst b_pos) n0), (Int64.testbit (snd b_pos) n0); auto. }
        pose proof (Int64.unsigned_not (fst b_pos)) as Hnot_f.
        pose proof (Int64.unsigned_not (Int64.or (fst b_pos) (snd b_pos))) as Hnot_or.
        rewrite H_not_or in Hnot_or. rewrite <- Zland_and in Hnot_or.
        
        assert (H_pos1: 0 <= Int64.unsigned (Int64.not (fst b_pos))) by (pose proof (Int64.unsigned_range (Int64.not (fst b_pos))); lia).
        assert (H_pos2: 0 <= Int64.unsigned (Int64.not (snd b_pos))) by (pose proof (Int64.unsigned_range (Int64.not (snd b_pos))); lia).
        pose proof (land_ub (Int64.unsigned (Int64.not (fst b_pos))) (Int64.unsigned (Int64.not (snd b_pos))) H_pos1 H_pos2).

        unfold Int64.signed.
        pose proof (Int64.unsigned_range (fst b_pos)).
        pose proof (Int64.unsigned_range (Int64.or (fst b_pos) (snd b_pos))).
        
        assert (H_sign_min: 0 <= Int64.signed (fst b_pos)).
        {
          unfold tnum_get_positive in Hpos_b.
          destruct b as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
          destruct (Int64_msb m) eqn:Hm.
          - injection Hpos_b as <-. simpl. apply testbit_sign_pos. msb_to_testbit Hv. exact Hv.
          - injection Hpos_b as <-. simpl. apply testbit_sign_pos. msb_to_testbit Hv. exact Hv.
        }
        apply testbit_sign_pos in H_sign_min.
        assert (H_msb_f: Int64.testbit (fst b_pos) (Int64.zwordsize - 1) = false) by exact H_sign_min.
        
        assert (H_msb_or: Int64.testbit (Int64.or (fst b_pos) (snd b_pos)) (Int64.zwordsize - 1) = false).
        { 
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). rewrite H_msb_f. 
          unfold tnum_get_positive in Hpos_b.
          destruct b as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
          destruct (Int64_msb m) eqn:Hm.
          - injection Hpos_b as <-. cbv [snd]. rewrite !Int64.bits_and by (change Int64.zwordsize with 64; lia). unfold Int64_min_signed.
            change (Int64.testbit (Int64.not (Int64.repr Int64.min_signed)) (Int64.zwordsize - 1)) with false.
            rewrite andb_false_r. reflexivity.
          - injection Hpos_b as <-. cbv [snd]. msb_to_testbit Hm. rewrite Hm. reflexivity.
        }
        apply testbit_sign_pos in H_msb_f. apply testbit_sign_pos in H_msb_or.
        
        unfold Int64.signed in *.
        destruct (Coqlib.zlt (Int64.unsigned (fst b_pos)) Int64.half_modulus);
        destruct (Coqlib.zlt (Int64.unsigned (Int64.or (fst b_pos) (snd b_pos))) Int64.half_modulus);
        lia.
      }

      assert (H_ltu_math: Int64.signed (get_signed_max b_pos) < - Int64.signed (get_signed_max a_neg)).
      {
        unfold Int64.ltu in Hltu.
        destruct (Coqlib.zlt _ _) as [Hlt_ltu | Hge_ltu] in Hltu; [|discriminate].
        
        assert (H_uns_b: Int64.unsigned (get_signed_max b_pos) = Int64.signed (get_signed_max b_pos)).
        { unfold Int64.signed in *.
          pose proof (Int64.unsigned_range (get_signed_max b_pos)).
          destruct (Coqlib.zlt (Int64.unsigned (get_signed_max b_pos)) Int64.half_modulus); lia. }
          
        assert (H_uns_a: Int64.unsigned (Int64.neg (get_signed_max a_neg)) = - Int64.signed (get_signed_max a_neg)).
        { unfold Int64.neg. rewrite Int64.unsigned_repr_eq.
          assert (H_a_uns: Int64.unsigned (get_signed_max a_neg) = Int64.signed (get_signed_max a_neg) + Int64.modulus).
          { unfold Int64.signed in *.
            pose proof (Int64.unsigned_range (get_signed_max a_neg)).
            destruct (Coqlib.zlt (Int64.unsigned (get_signed_max a_neg)) Int64.half_modulus); lia. }
          rewrite H_a_uns.
          replace (- (Int64.signed (get_signed_max a_neg) + Int64.modulus)) with
                  (- Int64.signed (get_signed_max a_neg) + (-1) * Int64.modulus) by lia.
          rewrite Z.mod_add by (change Int64.modulus with 18446744073709551616; lia).
          rewrite Z.mod_small.
          - lia.
          - pose proof (Int64.signed_range (get_signed_max a_neg)).
            change Int64.min_signed with (-9223372036854775808) in *.
            change Int64.max_signed with 9223372036854775807 in *.
            change Int64.modulus with 18446744073709551616. lia. }
        rewrite H_uns_b, H_uns_a in Hlt_ltu. lia.
      }

      assert (H_a_neg_min_neg: Int64.signed (get_signed_min a_neg) < 0) by lia.

      assert (H_min_val_neg: Int64.signed min_val < 0).
      {
        unfold min_val.
        destruct (Int64.eq (get_signed_min b_pos) Int64.zero) eqn:E_b0.
        - lia.
        - assert (H_b0_neq: Int64.signed (get_signed_min b_pos) <> 0).
          { intro HF.
            assert (H_uns: Int64.unsigned (get_signed_min b_pos) = 0).
            { unfold Int64.signed in HF. 
              pose proof (Int64.unsigned_range (get_signed_min b_pos)). 
              destruct (Coqlib.zlt (Int64.unsigned (get_signed_min b_pos)) Int64.half_modulus); lia. }
            rewrite Int64_eq_unsigned in E_b0. change (Int64.unsigned Int64.zero) with 0 in E_b0.
            rewrite H_uns in E_b0. simpl in E_b0. discriminate.
          }
          assert (H_b_min_pos: 0 <= Int64.signed (get_signed_min b_pos)).
          {
            unfold get_signed_min, tnum_get_positive in *.
            destruct b as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
            destruct (Int64_msb m) eqn:Hm.
            - injection Hpos_b as <-. simpl. apply testbit_sign_pos. msb_to_testbit Hv. exact Hv.
            - injection Hpos_b as <-. simpl. apply testbit_sign_pos. msb_to_testbit Hv. exact Hv.
          }
          unfold Int64.divs.
          assert (H_bounds: Int64.min_signed <= Z.quot (Int64.signed (get_signed_min a_neg)) (Int64.signed (get_signed_min b_pos)) < 0).
          {
            split.
            - assert (H_Q_bound: Int64.signed (get_signed_min a_neg) <= Z.quot (Int64.signed (get_signed_min a_neg)) (Int64.signed (get_signed_min b_pos))).
              {
                 replace (Int64.signed (get_signed_min a_neg)) with (- (- Int64.signed (get_signed_min a_neg))) by lia.
                 rewrite Z.quot_opp_l by lia.
                 assert (Hle: Z.quot (- Int64.signed (get_signed_min a_neg)) (Int64.signed (get_signed_min b_pos)) <= - Int64.signed (get_signed_min a_neg)).
                 {
                    rewrite Z.quot_div_nonneg by lia.
                    destruct (Z.eq_dec (Int64.signed (get_signed_min b_pos)) 1).
                    - rewrite e. rewrite Z.div_1_r. lia.
                    - apply Z.div_le_upper_bound; try lia.
                      assert (H_c: Int64.signed (get_signed_min b_pos) >= 1) by lia.
                      assert (H_a: - Int64.signed (get_signed_min a_neg) >= 0) by lia.
                      assert (H_ac: - Int64.signed (get_signed_min a_neg) * 1 <= - Int64.signed (get_signed_min a_neg) * Int64.signed (get_signed_min b_pos)).
                      { apply Z.mul_le_mono_nonneg_l; lia. }
                      lia.
                 }
                 lia.
              }
              pose proof (Int64.signed_range (get_signed_min a_neg)). lia.
            - assert (H_neg_div: forall x y, x <= - y -> y > 0 -> Z.quot x y < 0).
              {
                intros x y Hxy Hy.
                replace x with (- (-x)) by lia.
                rewrite Z.quot_opp_l by lia.
                assert (Hpos: 0 < Z.quot (- x) y).
                { apply Z.quot_str_pos; lia. }
                lia.
              }
              apply H_neg_div; lia.
          }
          rewrite Int64.signed_repr.
          + lia.
          + pose proof (Int64.signed_range (get_signed_min a_neg)).
            change Int64.min_signed with (-9223372036854775808) in *.
            change Int64.max_signed with 9223372036854775807 in *.
            lia.
      }

      apply testbit_sign_neg in H_min_val_neg.
      assert (H_uns_ge: Int64.unsigned min_val >= 2^63).
      {
         unfold Int64.testbit in H_min_val_neg.
         assert (H_bit: Z.testbit (Int64.unsigned min_val) 63 = true) by (change (Int64.zwordsize - 1) with 63 in H_min_val_neg; exact H_min_val_neg).
         destruct (Z.lt_ge_cases (Int64.unsigned min_val) (2^63)) as [Hlt_bound | Hge_bound].
         - assert (H_false: Z.testbit (Int64.unsigned min_val) 63 = false).
           { apply Z.testbit_false; pose proof (Int64.unsigned_range min_val); lia. }
           rewrite H_false in H_bit. discriminate.
         - lia.
      }
      
      assert (H_size_64: Z_size_Z (Int64.unsigned min_val) = 64).
      {
         unfold Z_size_Z.
         destruct (Int64.unsigned min_val) eqn:Euns.
         - lia.
         - rewrite Z.abs_eq by lia.
           assert (Z.log2 (Z.pos p) = 63).
           { apply Z.log2_unique. 
             - lia.
             - pose proof (Int64.unsigned_range min_val) as H_range.
               rewrite Euns in H_range.
               change Int64.modulus with 18446744073709551616%Z in H_range.
               replace (2 ^ 63)%Z with 9223372036854775808%Z in H_uns_ge by reflexivity.
               replace (2 ^ 63)%Z with 9223372036854775808%Z by reflexivity.
               replace (2 ^ Z.succ 63)%Z with 18446744073709551616%Z by reflexivity.
               lia. }
           lia.
         - lia.
      }
      rewrite H_size_64 in Hge. change Int64.zwordsize with 64 in Hn. lia.

  - injection Hcalc as <-.
    apply tnum_unknown_gamma.
Qed.

Lemma calc_pos_neg_sound: forall a b i j a_pos b_neg res,
  mem_tnum i a -> mem_tnum j b ->
  Int64.signed i >= 0 -> Int64.signed j < 0 ->
  tnum_get_positive a = Some a_pos ->
  tnum_get_negative b = Some b_neg ->
  calc_pos_neg_opt (Some a_pos) (Some b_neg) = Some res -> 
  mem_tnum (Int64.divs i j) res.
Proof.
  intros a b i j a_pos b_neg res Hmem_a Hmem_b Hsign_i Hsign_j Hpos_a Hneg_b Hcalc.
  
  Ltac msb_to_testbit2 H :=
    unfold Int64_msb in H;
    (rewrite Clt_Zlt_signed in H || rewrite Clt_Zlt_signed_false in H);
    change (Int64.signed Int64.zero) with 0 in H;
    (apply testbit_sign_neg in H || apply testbit_sign_pos in H).

  unfold calc_pos_neg_opt in Hcalc.
  destruct (Int64.ltu (Int64.neg (get_signed_min b_neg)) (get_signed_min a_pos)) eqn:Hltu.
  - injection Hcalc as <-.
    unfold mem_tnum; simpl.
    apply Int64.same_bits_eq; intros n Hn.
    rewrite !Int64.bits_and by lia.
    rewrite !Int64.bits_not by lia.
    unfold Int64_ones, Int64_size.
    rewrite !Int64.testbit_repr by auto.
    
    match goal with
    | |- context [ Z.ones (Z_size_Z (Int64.unsigned ?X)) ] => set (min_val := X) in *
    end.
    
    assert (Hzsize: 0 <= Z_size_Z (Int64.unsigned min_val)).
    { apply Z_size_range_Int64. pose proof (Int64.unsigned_range min_val). unfold Int64.max_unsigned; lia. }

    destruct (Coqlib.zlt n (Z_size_Z (Int64.unsigned min_val))) as [Hlt | Hge].
    + rewrite !Z.ones_spec_low by lia.
      destruct (Int64.testbit (Int64.divs i j) n); reflexivity.
    + rewrite !Z.ones_spec_high by lia.
      exfalso.

      assert (H_a_pos_max_pos: 0 <= Int64.signed (get_signed_max a_pos)).
      {
        unfold get_signed_max, tnum_get_positive in *.
        destruct a as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
        destruct (Int64_msb m) eqn:Hm.
        - injection Hpos_a as <-. simpl. apply testbit_sign_pos.
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia).
          rewrite !Int64.bits_and by (change Int64.zwordsize with 64; lia).
          unfold Int64_min_signed.
          change (Int64.testbit (Int64.not (Int64.repr Int64.min_signed)) (Int64.zwordsize - 1)) with false.
          rewrite andb_false_r. rewrite orb_false_r. msb_to_testbit2 Hv. exact Hv.
        - injection Hpos_a as <-. simpl. apply testbit_sign_pos.
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). msb_to_testbit2 Hv. msb_to_testbit2 Hm. rewrite Hv, Hm. auto.
      }

      assert (H_b_neg_max_neg: Int64.signed (get_signed_max b_neg) < 0).
      {
        unfold get_signed_max, tnum_get_negative in *.
        destruct b as [v m]. destruct (Int64_msb v) eqn:Hv.
        - injection Hneg_b as <-. simpl. apply testbit_sign_neg.
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). msb_to_testbit2 Hv. rewrite Hv. auto.
        - destruct (Int64_msb m) eqn:Hm.
          + injection Hneg_b as <-. simpl. apply testbit_sign_neg.
            rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia).
            unfold Int64_min_signed.
            change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
            destruct (Int64.testbit v (Int64.zwordsize - 1)); auto.
          + discriminate.
      }

      assert (H_min_le_max_b: Int64.signed (get_signed_min b_neg) <= Int64.signed (get_signed_max b_neg)).
      {
        unfold get_signed_min, get_signed_max.
        assert (H_not_or: Int64.not (Int64.or (fst b_neg) (snd b_neg)) = Int64.and (Int64.not (fst b_neg)) (Int64.not (snd b_neg))).
        { apply Int64.same_bits_eq; intros n0 Hn0.
          rewrite Int64.bits_not, Int64.bits_and, !Int64.bits_not, !Int64.bits_or by auto.
          destruct (Int64.testbit (fst b_neg) n0), (Int64.testbit (snd b_neg) n0); auto. }
        pose proof (Int64.unsigned_not (fst b_neg)) as Hnot_f.
        pose proof (Int64.unsigned_not (Int64.or (fst b_neg) (snd b_neg))) as Hnot_or.
        rewrite H_not_or in Hnot_or. rewrite <- Zland_and in Hnot_or.
        
        assert (H_pos1: 0 <= Int64.unsigned (Int64.not (fst b_neg))) by (pose proof (Int64.unsigned_range (Int64.not (fst b_neg))); lia).
        assert (H_pos2: 0 <= Int64.unsigned (Int64.not (snd b_neg))) by (pose proof (Int64.unsigned_range (Int64.not (snd b_neg))); lia).
        pose proof (land_ub (Int64.unsigned (Int64.not (fst b_neg))) (Int64.unsigned (Int64.not (snd b_neg))) H_pos1 H_pos2).

        unfold Int64.signed.
        pose proof (Int64.unsigned_range (fst b_neg)).
        pose proof (Int64.unsigned_range (Int64.or (fst b_neg) (snd b_neg))).
        assert (H_sign_min: Int64.signed (fst b_neg) < 0).
        {
          unfold tnum_get_negative in Hneg_b.
          destruct b as [v m]. destruct (Int64_msb v) eqn:Hv.
          - injection Hneg_b as <-. simpl. apply testbit_sign_neg. msb_to_testbit2 Hv. exact Hv.
          - destruct (Int64_msb m) eqn:Hm.
            + injection Hneg_b as <-. simpl. apply testbit_sign_neg.
              rewrite !Int64.bits_or by lia. unfold Int64_min_signed.
              change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
              rewrite orb_true_r. auto.
            + discriminate.
        }
        apply testbit_sign_neg in H_sign_min.
        assert (H_msb_f: Int64.testbit (fst b_neg) (Int64.zwordsize - 1) = true) by exact H_sign_min.
        assert (H_msb_or: Int64.testbit (Int64.or (fst b_neg) (snd b_neg)) (Int64.zwordsize - 1) = true).
        { rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). rewrite H_msb_f. apply orb_true_l. }
        apply testbit_sign_neg in H_msb_f. apply testbit_sign_neg in H_msb_or.
        
        unfold Int64.signed in *.
        destruct (Coqlib.zlt (Int64.unsigned (fst b_neg)) Int64.half_modulus);
        destruct (Coqlib.zlt (Int64.unsigned (Int64.or (fst b_neg) (snd b_neg))) Int64.half_modulus);
        lia.
      }
      
      assert (H_min_le_max_a: Int64.signed (get_signed_min a_pos) <= Int64.signed (get_signed_max a_pos)).
      {
        unfold get_signed_min, get_signed_max.
        assert (H_not_or: Int64.not (Int64.or (fst a_pos) (snd a_pos)) = Int64.and (Int64.not (fst a_pos)) (Int64.not (snd a_pos))).
        { apply Int64.same_bits_eq; intros n0 Hn0.
          rewrite Int64.bits_not, Int64.bits_and, !Int64.bits_not, !Int64.bits_or by auto.
          destruct (Int64.testbit (fst a_pos) n0), (Int64.testbit (snd a_pos) n0); auto. }
        pose proof (Int64.unsigned_not (fst a_pos)) as Hnot_f.
        pose proof (Int64.unsigned_not (Int64.or (fst a_pos) (snd a_pos))) as Hnot_or.
        rewrite H_not_or in Hnot_or. rewrite <- Zland_and in Hnot_or.
        
        assert (H_pos1: 0 <= Int64.unsigned (Int64.not (fst a_pos))) by (pose proof (Int64.unsigned_range (Int64.not (fst a_pos))); lia).
        assert (H_pos2: 0 <= Int64.unsigned (Int64.not (snd a_pos))) by (pose proof (Int64.unsigned_range (Int64.not (snd a_pos))); lia).
        pose proof (land_ub (Int64.unsigned (Int64.not (fst a_pos))) (Int64.unsigned (Int64.not (snd a_pos))) H_pos1 H_pos2).

        unfold Int64.signed.
        pose proof (Int64.unsigned_range (fst a_pos)).
        pose proof (Int64.unsigned_range (Int64.or (fst a_pos) (snd a_pos))).
        
        assert (H_sign_min: 0 <= Int64.signed (fst a_pos)).
        {
          unfold tnum_get_positive in Hpos_a.
          destruct a as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
          destruct (Int64_msb m) eqn:Hm.
          - injection Hpos_a as <-. simpl. apply testbit_sign_pos. msb_to_testbit2 Hv. exact Hv.
          - injection Hpos_a as <-. simpl. apply testbit_sign_pos. msb_to_testbit2 Hv. exact Hv.
        }
        apply testbit_sign_pos in H_sign_min.
        assert (H_msb_f: Int64.testbit (fst a_pos) (Int64.zwordsize - 1) = false) by exact H_sign_min.
        
        assert (H_msb_or: Int64.testbit (Int64.or (fst a_pos) (snd a_pos)) (Int64.zwordsize - 1) = false).
        { 
          rewrite !Int64.bits_or by (change Int64.zwordsize with 64; lia). rewrite H_msb_f. 
          unfold tnum_get_positive in Hpos_a.
          destruct a as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
          destruct (Int64_msb m) eqn:Hm.
          - injection Hpos_a as <-. cbv [snd]. rewrite !Int64.bits_and by (change Int64.zwordsize with 64; lia). unfold Int64_min_signed.
            change (Int64.testbit (Int64.not (Int64.repr Int64.min_signed)) (Int64.zwordsize - 1)) with false.
            rewrite andb_false_r. reflexivity.
          - injection Hpos_a as <-. cbv [snd]. msb_to_testbit2 Hm. rewrite Hm. reflexivity.
        }
        apply testbit_sign_pos in H_msb_f. apply testbit_sign_pos in H_msb_or.
        
        unfold Int64.signed in *.
        destruct (Coqlib.zlt (Int64.unsigned (fst a_pos)) Int64.half_modulus);
        destruct (Coqlib.zlt (Int64.unsigned (Int64.or (fst a_pos) (snd a_pos))) Int64.half_modulus);
        lia.
      }
      
      assert (H_b_neg_min_neg: Int64.signed (get_signed_min b_neg) < 0) by lia.

      assert (H_a_pos_min_pos: 0 <= Int64.signed (get_signed_min a_pos)).
      {
        unfold get_signed_min, tnum_get_positive in *.
        destruct a as [v m]. destruct (Int64_msb v) eqn:Hv; try discriminate.
        destruct (Int64_msb m) eqn:Hm.
        - injection Hpos_a as <-. simpl. apply testbit_sign_pos. msb_to_testbit2 Hv. exact Hv.
        - injection Hpos_a as <-. simpl. apply testbit_sign_pos. msb_to_testbit2 Hv. exact Hv.
      }

      assert (H_ltu_math: - Int64.signed (get_signed_min b_neg) < Int64.signed (get_signed_min a_pos)).
      {
        unfold Int64.ltu in Hltu.
        destruct (Coqlib.zlt _ _) as [Hlt_ltu | Hge_ltu] in Hltu; [|discriminate].
        
        assert (H_uns_b: Int64.unsigned (Int64.neg (get_signed_min b_neg)) = - Int64.signed (get_signed_min b_neg)).
        { unfold Int64.neg. rewrite Int64.unsigned_repr_eq.
          assert (H_b_uns: Int64.unsigned (get_signed_min b_neg) = Int64.signed (get_signed_min b_neg) + Int64.modulus).
          { unfold Int64.signed in *. 
            pose proof (Int64.unsigned_range (get_signed_min b_neg)).
            destruct (Coqlib.zlt (Int64.unsigned (get_signed_min b_neg)) Int64.half_modulus); lia. }
          rewrite H_b_uns.
          replace (- (Int64.signed (get_signed_min b_neg) + Int64.modulus)) with
                  (- Int64.signed (get_signed_min b_neg) + -1 * Int64.modulus)%Z by lia.
          rewrite Z.mod_add by (change Int64.modulus with 18446744073709551616%Z; lia).
          rewrite Z.mod_small.
          - lia.
          - pose proof (Int64.signed_range (get_signed_min b_neg)).
            change Int64.min_signed with (-9223372036854775808%Z) in *.
            change Int64.max_signed with 9223372036854775807%Z in *.
            change Int64.modulus with 18446744073709551616%Z. lia. }
            
        assert (H_uns_a: Int64.unsigned (get_signed_min a_pos) = Int64.signed (get_signed_min a_pos)).
        { unfold Int64.signed in *.
          pose proof (Int64.unsigned_range (get_signed_min a_pos)).
          destruct (Coqlib.zlt (Int64.unsigned (get_signed_min a_pos)) Int64.half_modulus); lia. }
        rewrite H_uns_b, H_uns_a in Hlt_ltu. lia.
      }

      assert (H_min_val_neg: Int64.signed min_val < 0).
      {
        unfold min_val.
        unfold Int64.divs.
        assert (H_a_pos_strict: Int64.signed (get_signed_max a_pos) > 0) by lia.
        assert (H_b_max_neg1: Int64.signed (get_signed_max b_neg) <= -1) by lia.
        assert (H_bounds: Int64.min_signed <= Z.quot (Int64.signed (get_signed_max a_pos)) (Int64.signed (get_signed_max b_neg)) < 0).
        {
          split.
          - assert (H_Q_bound: - Int64.signed (get_signed_max a_pos) <= Z.quot (Int64.signed (get_signed_max a_pos)) (Int64.signed (get_signed_max b_neg))).
            {
               replace (Int64.signed (get_signed_max b_neg)) with (- (- Int64.signed (get_signed_max b_neg))) by lia.
               rewrite Z.quot_opp_r by lia.
               assert (Hle: Z.quot (Int64.signed (get_signed_max a_pos)) (- Int64.signed (get_signed_max b_neg)) <= Int64.signed (get_signed_max a_pos)).
               {
                  rewrite Z.quot_div_nonneg by lia.
                  destruct (Z.eq_dec (- Int64.signed (get_signed_max b_neg)) 1).
                  - lia.
                  - apply Z.div_le_upper_bound; try lia.
                    assert (H_c: - Int64.signed (get_signed_max b_neg) >= 2) by lia.
                    assert (H_ac: Int64.signed (get_signed_max a_pos) * 1 <= Int64.signed (get_signed_max a_pos) * (- Int64.signed (get_signed_max b_neg))).
                    { apply Z.mul_le_mono_nonneg_l; lia. }
                    lia.
               }
               lia.
            }
            pose proof (Int64.signed_range (get_signed_max a_pos)).
            change Int64.min_signed with (-9223372036854775808%Z) in *.
            change Int64.max_signed with 9223372036854775807%Z in *.
            lia.
          - assert (H_neg_div: forall x y, x >= - y -> y <= -1 -> Z.quot x y < 0).
            {
              intros x y Hxy Hy.
              replace y with (- (-y)) by lia.
              rewrite Z.quot_opp_r by lia.
              assert (Hpos: 0 < Z.quot x (- y)).
              { apply Z.quot_str_pos; lia. }
              lia.
            }
            apply H_neg_div; lia.
        }
        rewrite Int64.signed_repr.
        + lia.
        + pose proof (Int64.signed_range (get_signed_max a_pos)).
          change Int64.min_signed with (-9223372036854775808%Z) in *.
          change Int64.max_signed with 9223372036854775807%Z in *.
          lia.
      }

      apply testbit_sign_neg in H_min_val_neg.
      assert (H_uns_ge: Int64.unsigned min_val >= 2^63).
      {
         unfold Int64.testbit in H_min_val_neg.
         assert (H_bit: Z.testbit (Int64.unsigned min_val) 63 = true) by (change (Int64.zwordsize - 1) with 63 in H_min_val_neg; exact H_min_val_neg).
         destruct (Z.lt_ge_cases (Int64.unsigned min_val) (2^63)) as [Hlt_bound | Hge_bound].
         - assert (H_false: Z.testbit (Int64.unsigned min_val) 63 = false).
           { apply Z.testbit_false; pose proof (Int64.unsigned_range min_val); lia. }
           rewrite H_false in H_bit. discriminate.
         - lia.
      }
      
      assert (H_size_64: Z_size_Z (Int64.unsigned min_val) = 64).
      {
         unfold Z_size_Z.
         destruct (Int64.unsigned min_val) eqn:Euns.
         - lia.
         - rewrite Z.abs_eq by lia.
           assert (Z.log2 (Z.pos p) = 63).
           { apply Z.log2_unique. 
             - lia.
             - pose proof (Int64.unsigned_range min_val) as H_range.
               rewrite Euns in H_range.
               change Int64.modulus with 18446744073709551616%Z in H_range.
               replace (2 ^ 63)%Z with 9223372036854775808%Z by reflexivity.
               replace (2 ^ Z.succ 63)%Z with 18446744073709551616%Z by reflexivity.
               lia. }
           lia.
         - lia.
      }
      rewrite H_size_64 in Hge. change Int64.zwordsize with 64 in Hn. lia.

  - injection Hcalc as <-.
    apply tnum_unknown_gamma.
Qed.

Lemma tnum_sdiv_common_sound: forall a b i j,
  mem_tnum i a -> mem_tnum j b ->
  j <> Int64.zero ->
  ~ (i = Int64.repr Int64.min_signed /\ j = Int64.mone) ->
  mem_tnum (Int64.divs i j) (tnum_sdiv_common a b).
Proof.
  intros a b i j Hmem_a Hmem_b Hj_not0 H_not_overflow.
  unfold tnum_sdiv_common.
  
  Ltac kill_none x elem Hmem Hsign Hnone :=
    exfalso;
    (unfold tnum_get_negative in Hnone || unfold tnum_get_positive in Hnone);
    destruct x as [v m]; 
    destruct (Int64_msb v) eqn:Hv;
    destruct (Int64_msb m) eqn:Hm;
    try discriminate Hnone;
    unfold mem_tnum in Hmem; simpl in Hmem;
    assert (Hbit: Int64.testbit (Int64.and elem (Int64.not m)) 63 = Int64.testbit v 63) by (rewrite Hmem; reflexivity);
    rewrite Int64.bits_and in Hbit by (change Int64.zwordsize with 64; lia);
    rewrite Int64.bits_not in Hbit by (change Int64.zwordsize with 64; lia);
    destruct (Int64.testbit elem 63) eqn:Helem63;
    destruct (Int64.testbit v 63) eqn:Hv63;
    destruct (Int64.testbit m 63) eqn:Hm63;
    simpl in Hbit; try discriminate Hbit;
    change 63 with (Int64.zwordsize - 1) in Helem63, Hv63, Hm63;
    try (apply testbit_sign_neg in Helem63); try (apply testbit_sign_pos in Helem63);
    try (apply testbit_sign_neg in Hv63); try (apply testbit_sign_pos in Hv63);
    try (apply testbit_sign_neg in Hm63); try (apply testbit_sign_pos in Hm63);
    unfold Int64_msb in *;
    repeat match goal with 
    | H: Int64.lt _ _ = true |- _ => rewrite Clt_Zlt_signed in H 
    | H: Int64.lt _ _ = false |- _ => rewrite Clt_Zlt_signed_false in H 
    end;
    change (Int64.signed Int64.zero) with 0 in *;
    lia.

  Ltac solve_calc_none Hcalc Hmem_a Hmem_b Hi_sign Hj_sign elem_i elem_j orig_a orig_b :=
    unfold calc_pos_pos_opt, calc_neg_neg_opt, calc_neg_pos_opt, calc_pos_neg_opt in Hcalc;
    repeat match type of Hcalc with
    | context[Int64_msb ?x] => destruct (Int64_msb x) eqn:?
    | context[Int64.ltu ?x ?y] => destruct (Int64.ltu x y) eqn:?
    | context[?x && ?y] => destruct (x && y) eqn:?
    end;
    try discriminate Hcalc;
    exfalso;
    unfold mem_tnum in Hmem_a, Hmem_b; simpl in Hmem_a, Hmem_b;
    assert (Hba: Int64.testbit (Int64.and elem_i (Int64.not (snd orig_a))) 63 = Int64.testbit (fst orig_a) 63) by (rewrite Hmem_a; reflexivity);
    assert (Hbb: Int64.testbit (Int64.and elem_j (Int64.not (snd orig_b))) 63 = Int64.testbit (fst orig_b) 63) by (rewrite Hmem_b; reflexivity);
    rewrite Int64.bits_and in Hba by (change Int64.zwordsize with 64; lia);
    rewrite Int64.bits_not in Hba by (change Int64.zwordsize with 64; lia);
    rewrite Int64.bits_and in Hbb by (change Int64.zwordsize with 64; lia);
    rewrite Int64.bits_not in Hbb by (change Int64.zwordsize with 64; lia);
    destruct (Int64.testbit elem_i 63) eqn:Hei63;
    destruct (Int64.testbit elem_j 63) eqn:Hej63;
    destruct (Int64.testbit (fst orig_a) 63) eqn:Ha_v63;
    destruct (Int64.testbit (snd orig_a) 63) eqn:Ha_m63;
    destruct (Int64.testbit (fst orig_b) 63) eqn:Hb_v63;
    destruct (Int64.testbit (snd orig_b) 63) eqn:Hb_m63;
    simpl in Hba, Hbb; try discriminate Hba; try discriminate Hbb;
    change 63 with (Int64.zwordsize - 1) in Hei63, Hej63, Ha_v63, Ha_m63, Hb_v63, Hb_m63;
    try (apply testbit_sign_neg in Hei63); try (apply testbit_sign_pos in Hei63);
    try (apply testbit_sign_neg in Hej63); try (apply testbit_sign_pos in Hej63);
    try (apply testbit_sign_neg in Ha_v63); try (apply testbit_sign_pos in Ha_v63);
    try (apply testbit_sign_neg in Ha_m63); try (apply testbit_sign_pos in Ha_m63);
    try (apply testbit_sign_neg in Hb_v63); try (apply testbit_sign_pos in Hb_v63);
    try (apply testbit_sign_neg in Hb_m63); try (apply testbit_sign_pos in Hb_m63);
    unfold Int64_msb in *;
    repeat match goal with 
    | H: Int64.lt _ _ = true |- _ => rewrite Clt_Zlt_signed in H 
    | H: Int64.lt _ _ = false |- _ => rewrite Clt_Zlt_signed_false in H 
    end;
    change (Int64.signed Int64.zero) with 0 in *;
    lia.

  Ltac drill_union :=
    simpl;
    match goal with
    | |- mem_tnum _ tnum_unknown => apply tnum_unknown_gamma
    | |- mem_tnum _ (tnum_union _ _) => apply tnum_union_sound; (left; drill_union) + (right; drill_union)
    | |- mem_tnum _ ?res => assumption
    end. 

  destruct (Coqlib.zlt (Int64.signed i) 0) as [Hi_lt | Hi_ge];
  destruct (Coqlib.zlt (Int64.signed j) 0) as [Hj_lt | Hj_ge].
  
  -
    destruct (tnum_get_negative a) as [a_neg|] eqn:Ha_neg; [| kill_none a i Hmem_a Hi_lt Ha_neg].
    destruct (tnum_get_negative b) as [b_neg|] eqn:Hb_neg; [| kill_none b j Hmem_b Hj_lt Hb_neg].
    
    destruct (calc_neg_neg_opt (Some a_neg) (Some b_neg)) as [res|] eqn:Hcalc.
    + assert (H_sound: mem_tnum (Int64.divs i j) res) by (eapply calc_neg_neg_sound; eauto).
      destruct (calc_pos_pos_opt _ _); destruct (calc_neg_pos_opt _ _); destruct (calc_pos_neg_opt _ _).
      all: drill_union.
    + solve_calc_none Hcalc Hmem_a Hmem_b Hi_lt Hj_lt i j a b.

  -
    destruct (tnum_get_negative a) as [a_neg|] eqn:Ha_neg; [| kill_none a i Hmem_a Hi_lt Ha_neg].
    destruct (tnum_get_positive b) as [b_pos|] eqn:Hb_pos; [| kill_none b j Hmem_b Hj_ge Hb_pos].
    
    destruct (calc_neg_pos_opt (Some a_neg) (Some b_pos)) as [res|] eqn:Hcalc.
    + assert (H_sound: mem_tnum (Int64.divs i j) res) by (eapply calc_neg_pos_sound; eauto).
      destruct (calc_pos_pos_opt _ _); destruct (calc_neg_neg_opt _ _); destruct (calc_pos_neg_opt _ _).
      all: drill_union.
    + solve_calc_none Hcalc Hmem_a Hmem_b Hi_lt Hj_ge i j a b.

  -
    destruct (tnum_get_positive a) as [a_pos|] eqn:Ha_pos; [| kill_none a i Hmem_a Hi_ge Ha_pos].
    destruct (tnum_get_negative b) as [b_neg|] eqn:Hb_neg; [| kill_none b j Hmem_b Hj_lt Hb_neg].
    
    destruct (calc_pos_neg_opt (Some a_pos) (Some b_neg)) as [res|] eqn:Hcalc.
    + assert (H_sound: mem_tnum (Int64.divs i j) res) by (eapply calc_pos_neg_sound; eauto).
      destruct (calc_pos_pos_opt _ _); destruct (calc_neg_neg_opt _ _); destruct (calc_neg_pos_opt _ _).
      all: drill_union.
    + solve_calc_none Hcalc Hmem_a Hmem_b Hi_ge Hj_lt i j a b.

  -
    destruct (tnum_get_positive a) as [a_pos|] eqn:Ha_pos; [| kill_none a i Hmem_a Hi_ge Ha_pos].
    destruct (tnum_get_positive b) as [b_pos|] eqn:Hb_pos; [| kill_none b j Hmem_b Hj_ge Hb_pos].
    
    destruct (calc_pos_pos_opt (Some a_pos) (Some b_pos)) as [res|] eqn:Hcalc.
    + assert (H_sound: mem_tnum (Int64.divs i j) res) by (eapply calc_pos_pos_sound; eauto).
      destruct (calc_pos_neg_opt _ _); destruct (calc_neg_neg_opt _ _); destruct (calc_neg_pos_opt _ _).
      all: drill_union.
    + solve_calc_none Hcalc Hmem_a Hmem_b Hi_ge Hj_ge i j a b.
Qed.

Lemma tnum_msb_mone : forall a, mem_tnum Int64.mone a -> Int64_msb (fst a) = true \/ Int64_msb (snd a) = true.
Proof.
  intros.
  unfold Int64_msb.
  unfold mem_tnum in *.
  rewrite <- H.
  clear.
  
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
  - 
    change (Int64.testbit Int64.mone (Int64.zwordsize - 1)) with true.
    auto.
  - rewrite Int64.bits_not.
    2:{ change (Int64.zwordsize) with 64. lia. }
    rewrite Heq.
    auto.
Qed.

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
          assert (H_a_neg_min: get_signed_min (match tnum_get_negative (fst a, snd a) with Some x => x | None => (Int64.zero, Int64.zero) end) = Int64.repr Int64.min_signed).
          {
            unfold tnum_get_negative, get_signed_min; simpl.
            pose proof H_dst as Hmem. unfold mem_tnum in Hmem; simpl in Hmem.
            destruct (Int64_msb (fst a)) eqn:Hmsb_v.
            - rewrite <- Hmem. apply Int64.same_bits_eq; intros n Hn.
              simpl. 
              rewrite Int64.bits_and by auto.
              destruct (Coqlib.zlt n (Int64.zwordsize - 1)).
              + unfold Int64_min_signed. 
                rewrite Hm1.
                rewrite !Int64.testbit_repr by auto.
                change Int64.min_signed with (- two_p 63).
                rewrite !Zbits.Ztestbit_neg_two_p by (change Int64.zwordsize with 64 in Hn; lia); try lia.
                destruct (Coqlib.zlt n 63); try lia. simpl; auto.
              + assert (n = Int64.zwordsize - 1) by lia; subst n.
                unfold Int64_msb in Hmsb_v.
                rewrite Clt_Zlt_signed in Hmsb_v.
                change (Int64.signed Int64.zero) with 0 in Hmsb_v.
                apply testbit_sign_neg in Hmsb_v.
                rewrite <- Hmem in Hmsb_v. rewrite Int64.bits_and in Hmsb_v by lia.
                unfold Int64_min_signed.
                change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                rewrite Hmsb_v; auto.
            - rewrite Hm1 in H_dst.
              apply tnum_msb in H_dst as Hmsb_or. destruct Hmsb_or as [Hmsb_v' | Hmsb_m].
              { rewrite Hmsb_v in Hmsb_v'; discriminate. }
              rewrite Hmsb_m.
              rewrite <- Hmem. apply Int64.same_bits_eq; intros n Hn.
              simpl. 
              rewrite Int64.bits_or by auto. rewrite Int64.bits_and by auto.
              destruct (Coqlib.zlt n (Int64.zwordsize - 1)).
              + unfold Int64_min_signed. 
                rewrite Hm1. 
                rewrite !Int64.testbit_repr by auto. 
                change Int64.min_signed with (- two_p 63). 
                rewrite !Zbits.Ztestbit_neg_two_p by (change Int64.zwordsize with 64 in Hn; lia); try lia.
                destruct (Coqlib.zlt n 63); try lia.
              + assert (n = Int64.zwordsize - 1) by lia; subst n.
                unfold Int64_min_signed.
                change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                rewrite orb_true_r; auto.
          }
          unfold tnum_sdiv_common.
          change (tnum_get_positive (Int64.mone, Int64.zero)) with (@None tnum).
          change (tnum_get_negative (Int64.mone, Int64.zero)) with (Some (Int64.mone, Int64.zero)).
          
          destruct (tnum_get_negative (fst a, snd a)) as [a_neg|] eqn:Ha_neg.
          2:{
            unfold get_signed_min in H_a_neg_min. simpl in H_a_neg_min.
            apply (f_equal Int64.signed) in H_a_neg_min.
            change (Int64.signed Int64.zero) with 0 in H_a_neg_min.
            change (Int64.signed (Int64.repr Int64.min_signed)) with (-9223372036854775808) in H_a_neg_min.
            lia.
          }
          unfold calc_neg_neg_opt.
        
          assert (H_calc : Int64.eq (get_signed_min a_neg) Int64_min_signed && Int64.eq (get_signed_max (Int64.mone, Int64.zero)) Int64.mone = true).
          { rewrite H_a_neg_min. reflexivity. }
          rewrite H_calc.
          simpl.

          Opaque tnum_union.
          destruct (Int64_msb (fst a)); destruct (Int64_msb (snd a)); simpl.
          all: repeat match goal with 
                 | |- context [if ?cond then _ else _] => destruct cond; simpl
               end.
          Transparent tnum_union.
          all: repeat apply tnum_union_sound.
          all: repeat ( (left; apply tnum_unknown_gamma) || right ).
          all: try apply tnum_unknown_gamma.

        * rewrite orb_false_iff in Hm.
          destruct Hm as (Hm1 & Hm2).
          apply tnum_sdiv_common_sound; auto.
          --
             intro Hj_eq; subst j.
             rewrite Hj_eq in Hm1.
             rewrite Int64.eq_true in Hm1; discriminate.
          --
             intro H_over; destruct H_over as [Hi Hj].
             rewrite Hi, Hj in Hm2.
             rewrite !Int64.eq_true in Hm2.
             simpl in Hm2; discriminate.
  }
  -
    destruct (Int64.eq (fst b) Int64.zero) eqn:Hb_v0.
          +
            unfold eval_div_s64, LLONG_MIN; simpl.
            destruct (Val.eq (Vlong j) (Vlong Int64.zero)) as [Hj0 | Hj0].
            {
              inversion Hj0; subst j.
              rewrite Int64.eq_true. simpl. apply tnum_unknown_gamma. }
              
            destruct (Val.eq (Vlong j) (Vlong Int64.mone)) as [Hj1 | Hj1]; simpl.
            { destruct (Val.eq (Vlong i) (Vlong (Int64.repr Int64.min_signed))) as [Hi_min | Hi_min]; simpl.
              -
                inversion Hj1; subst j. inversion Hi_min; subst i.
                rewrite !Int64.eq_true. simpl. apply tnum_unknown_gamma.
              -
                inversion Hj1; subst j.
                destruct (Int64.eq i (Int64.repr Int64.min_signed)) eqn:E_i.
                { apply Int64.same_if_eq in E_i. exfalso. apply Hi_min. f_equal. auto. }
                simpl. apply tnum_unknown_gamma.
            }
            {
              destruct (Int64.eq j Int64.zero) eqn:E_j0.
              { apply Int64.same_if_eq in E_j0. exfalso. apply Hj0. f_equal. auto. }
              destruct (Int64.eq j Int64.mone) eqn:E_j1.
              { apply Int64.same_if_eq in E_j1. exfalso. apply Hj1. f_equal. auto. }
              destruct (Int64.eq i (Int64.repr Int64.min_signed)).
              all: simpl; apply tnum_unknown_gamma.
            }
    + simpl.
      unfold eval_div_s64; simpl.
      destruct (Int64.eq j Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone) eqn: Hm.
      *
                destruct (Val.eq (Vlong j) (Vlong Int64.zero)) as [Hj | Hj].
                {
                  exfalso. inversion Hj. subst j.
                  unfold mem_tnum in H_src. rewrite Int64.and_zero_l in H_src.
                  rewrite <- H_src in Hb_v0. rewrite Int64.eq_true in Hb_v0. discriminate.
                }
                
                rewrite orb_true_iff in Hm.
                destruct Hm as [Hm_zero | Hm_over].
                { exfalso. apply Hj. f_equal. apply Int64.same_if_eq in Hm_zero. auto. }
                rewrite andb_true_iff in Hm_over. destruct Hm_over as (Hm1 & Hm2).
                apply Int64.same_if_eq in Hm1, Hm2.
                
                unfold tnum_sdiv_common.
                destruct (tnum_get_negative (fst a, snd a)) as [a_neg|] eqn:Ha_neg.
                2:{
                  rewrite Hm1 in H_dst. apply tnum_msb in H_dst.
                  unfold tnum_get_negative in Ha_neg. destruct a as [a_v a_m]; simpl in *.
                  destruct H_dst as [H_v | H_m].
                  - rewrite H_v in Ha_neg; discriminate.
                  - destruct (Int64_msb a_v); [discriminate | rewrite H_m in Ha_neg; discriminate].
                }
                
                destruct (tnum_get_negative (fst b, snd b)) as [b_neg|] eqn:Hb_neg.
                2:{
                  rewrite Hm2 in H_src. apply tnum_msb_mone in H_src.
                  unfold tnum_get_negative in Hb_neg. destruct b as [b_v b_m]; simpl in *.
                  destruct H_src as [H_v | H_m].
                  - rewrite H_v in Hb_neg; discriminate.
                  - destruct (Int64_msb b_v); [discriminate | rewrite H_m in Hb_neg; discriminate].
                }

                assert (H_a_neg_min: get_signed_min a_neg = Int64.repr Int64.min_signed).
                {
                  unfold tnum_get_negative in Ha_neg. unfold get_signed_min.
                  destruct a as [a_v a_m]. simpl in *.
                  pose proof H_dst as Hmem. unfold mem_tnum in Hmem. simpl in Hmem.
                  destruct (Int64_msb a_v) eqn:Hmsb_v.
                  - injection Ha_neg as <-. simpl.
                    rewrite <- Hmem. apply Int64.same_bits_eq; intros n Hn.
                    simpl. rewrite Int64.bits_and by auto.
                    destruct (Coqlib.zlt n (Int64.zwordsize - 1)).
                    + unfold Int64_min_signed. rewrite Hm1. rewrite !Int64.testbit_repr by auto.
                      change Int64.min_signed with (- two_p 63).
                      rewrite !Zbits.Ztestbit_neg_two_p by (change Int64.zwordsize with 64 in Hn; lia); try lia.
                      destruct (Coqlib.zlt n 63); try lia. simpl; auto.
                    + assert (n = Int64.zwordsize - 1) by lia; subst n.
                      unfold Int64_msb in Hmsb_v. rewrite Clt_Zlt_signed in Hmsb_v.
                      change (Int64.signed Int64.zero) with 0 in Hmsb_v.
                      apply testbit_sign_neg in Hmsb_v.
                      rewrite <- Hmem in Hmsb_v. rewrite Int64.bits_and in Hmsb_v by lia.
                      unfold Int64_min_signed. change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                      rewrite Hmsb_v; auto.
                  - rewrite Hm1 in H_dst. apply tnum_msb in H_dst as Hmsb_or.
                    destruct Hmsb_or as [Hmsb_v' | Hmsb_m_true].
                    { simpl in Hmsb_v'. rewrite Hmsb_v in Hmsb_v'; discriminate. }
                    simpl in Hmsb_m_true. rewrite Hmsb_m_true in Ha_neg. injection Ha_neg as <-.
                    rewrite <- Hmem. apply Int64.same_bits_eq; intros n Hn.
                    simpl. rewrite Int64.bits_or by auto. rewrite Int64.bits_and by auto.
                    destruct (Coqlib.zlt n (Int64.zwordsize - 1)).
                    + unfold Int64_min_signed. rewrite Hm1. rewrite !Int64.testbit_repr by auto.
                      change Int64.min_signed with (- two_p 63).
                      rewrite !Zbits.Ztestbit_neg_two_p by (change Int64.zwordsize with 64 in Hn; lia); try lia.
                      destruct (Coqlib.zlt n 63); try lia.
                    + assert (n = Int64.zwordsize - 1) by lia; subst n.
                      unfold Int64_min_signed. change (Int64.testbit (Int64.repr Int64.min_signed) (Int64.zwordsize - 1)) with true.
                      rewrite orb_true_r; auto.
                }

                assert (H_b_neg_max: get_signed_max b_neg = Int64.mone).
                {
                  assert (Hmem_b_neg: mem_tnum Int64.mone b_neg).
                  { rewrite Hm2 in H_src. 
                    apply tnum_get_negative_sound with (a := b) (i := Int64.mone) (a_neg := b_neg).
                    - exact H_src.
                    - change (Int64.signed Int64.mone) with (-1). lia.
                    - destruct b. exact Hb_neg.
                  }
                  unfold mem_tnum in Hmem_b_neg. rewrite Int64.and_mone_l in Hmem_b_neg.
                  unfold get_signed_max. rewrite <- Hmem_b_neg.
                  apply Int64.same_bits_eq; intros n Hn.
                  rewrite Int64.bits_or by auto. rewrite Int64.bits_not by auto.
                  destruct b_neg as [b_neg_v b_neg_m]. simpl in *.
                  rewrite Int64.bits_mone by auto.
                  destruct (Int64.testbit b_neg_m n); reflexivity.
                }

                subst i j. unfold LLONG_MIN.
                assert (H_if : Coqlib.proj_sumbool (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) && Coqlib.proj_sumbool (Val.eq (Vlong (Int64.repr Int64.min_signed)) (Vlong (Int64.repr Int64.min_signed))) = true).
                {
                  unfold Coqlib.proj_sumbool.
                  destruct (Val.eq (Vlong Int64.mone) (Vlong Int64.mone)) as [_ | Hneq1]; [|exfalso; apply Hneq1; auto].
                  destruct (Val.eq (Vlong (Int64.repr Int64.min_signed)) (Vlong (Int64.repr Int64.min_signed))) as [_ | Hneq2]; [|exfalso; apply Hneq2; auto].
                  reflexivity.
                }
                rewrite H_if. simpl.
                unfold tnum_union_opt. unfold calc_neg_neg_opt.
                assert (H_calc : Int64.eq (get_signed_min a_neg) Int64_min_signed && Int64.eq (get_signed_max b_neg) Int64.mone = true).
                { rewrite H_a_neg_min, H_b_neg_max. reflexivity. }
                rewrite H_calc.
                
                Opaque tnum_union.
                repeat match goal with
                | |- context [if ?cond then _ else _] => destruct cond; simpl
                end.
                Transparent tnum_union.
                
               Ltac find_unknown :=
            match goal with
            | |- mem_tnum _ tnum_unknown => apply tnum_unknown_gamma
            | |- _ \/ _ => (left; find_unknown) + (right; find_unknown)
            | |- mem_tnum _ (tnum_union _ _) => apply tnum_union_sound; find_unknown
            end.
          
          all: find_unknown.

      *
            rewrite orb_false_iff in Hm.
            destruct Hm as (Hm1 & Hm2).
            apply tnum_sdiv_common_sound; auto.
            -- intro Hj_eq; subst j.
               rewrite Int64.eq_true in Hm1; discriminate.
            -- intro H_over; destruct H_over as [Hi Hj].
               rewrite Hi, Hj in Hm2.
               rewrite !Int64.eq_true in Hm2.
               simpl in Hm2; discriminate.
Qed.
