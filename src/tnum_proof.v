From Coq Require Import List ZArith Lia.
From compcert.lib Require Import Integers.
(*From bpf.src Require Import tnum. *)
Require Import tnumZ tnumZ_add_sound.
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
