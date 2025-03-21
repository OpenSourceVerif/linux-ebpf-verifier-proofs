(**
Formalisation of the Tristate abstract domain from the paper

[1] Harishankar Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte. 2022.
Sound, precise, and fast abstract interpretation with tristate numbers. CGO'22

*)


From Coq Require Import ZArith Bool Lia Btauto.
Open Scope Z_scope.
Add Search  Blacklist "POrderedType".

From bpf.src Require Import Zmore.

Ltac dand :=
  repeat match goal with
  | H : ?A /\ ?B |- _ =>
      let f1 := fresh H  in
      let f2 := fresh H in
      destruct H as (f1,f2)
    end.

Ltac elim_testbit :=
  repeat
  match goal with
  | H : context[Z.testbit ?A ?B] |- _ => destruct (Z.testbit A B)
  | |- context[Z.testbit ?A ?B]  => destruct (Z.testbit A B)
  end.

Definition tnum := (Z * Z)%type.

Definition gamma  (a: tnum) (x: Z) : Prop :=
   (Z.land x (Z.lnot (snd a))) = (fst a).

Lemma add_lor_excl : forall x y,
    Z.land x y = 0%Z ->
  (x + y)%Z = Z.lor x y.
Proof.
  intros.
  rewrite <- Z.add_lor_land.
  rewrite H.
  ring.
Qed.

Lemma gamma_add_lor : forall a i,
    gamma a i ->
    (fst a + snd a = Z.lor (fst a) (snd a))%Z.
Proof.
  intros.
  apply add_lor_excl.
  unfold gamma in H.
  rewrite <- H.
  rewrite <- Z.land_assoc.
  rewrite (Z.land_comm (Z.lnot (snd a))).
  rewrite Z.land_lnot_diag.
  rewrite Z.land_0_r.
  reflexivity.
Qed.


(** [add_carry_bit x y c n] computes the nth carry bit
    of the addition of x + y + c *)
Fixpoint add_carry_bit (x y : Z) (c:bool) (n:nat) :=
  match n with
  | O => c
  | S n' =>
      let pc := add_carry_bit x y c n' in
      let n := Z.of_nat n' in
                  (orb (andb (Z.testbit x n)
                          (Z.testbit y  n))
                     (andb pc (xorb (Z.testbit x n) (Z.testbit y n))))
  end.

Lemma carry_bit_rew : forall  (x y : Z) (c:bool) (n:nat),
    add_carry_bit x y c n =
  match n with
  | O => c
  | S n' =>
      let pc := add_carry_bit x y c n' in
      let n := Z.of_nat n' in
      (orb (andb (Z.testbit x n)
              (Z.testbit y  n))
         (andb pc (xorb (Z.testbit x n) (Z.testbit y n))))
  end.
Proof.
  destruct n; try reflexivity.
Qed.


Lemma xtestbit_add_sound : forall n x y c0,
    Z.testbit (x + y + Z.b2z c0) (Z.of_nat n) =
      xorb (xorb (Z.testbit x (Z.of_nat n))
              (Z.testbit y (Z.of_nat n))) (add_carry_bit x y c0 n).
Proof.
  induction n.
  - simpl.
    intros.
    rewrite! Z.odd_add.
    rewrite Zodd_b2z.
    reflexivity.
  -
    intros.
    rewrite (decomp (x + y + Z.b2z c0)) at 1.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) at 1 by lia.
    rewrite Z.testbit_succ_r by lia.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
    rewrite carry_bit_rew.
    cbv zeta.
    rewrite (decomp x) at 2.
    rewrite (decomp y) at 2.
    rewrite! Z.testbit_succ_r by lia.
    rewrite add_shift.
    rewrite add_shift.
    rewrite b2z_div2.
    rewrite Z.odd_add.
    rewrite! Zodd_b2z.
    assert (CR: (exists cr, Z.b2z (Z.odd x && Z.odd y) + 0 +
     Z.b2z (xorb (Z.odd x) (Z.odd y) && c0) = Z.b2z cr)%Z).
    {
      destruct (Z.odd x),(Z.odd y),c0; simpl;
        try (exists true;  reflexivity);
        try (exists false;  reflexivity).
    }
    destruct CR as (cr& CR).
    replace ((x / 2 + y / 2 + Z.b2z (Z.odd x && Z.odd y) + 0 +
                Z.b2z (xorb (Z.odd x) (Z.odd y) && c0)))%Z
      with  (x / 2 + y / 2 + Z.b2z cr)%Z by lia.
    rewrite IHn.
    f_equal.
    clear IHn.
    revert x y cr c0 CR.
    induction n.
    {
      simpl.
      intros.
      destruct cr,(Z.odd x),(Z.odd y),c0; simpl in *; try reflexivity;
        try congruence.
    }
    {
      intros.
      rewrite carry_bit_rew.
      cbv zeta.
      apply IHn in CR.
      rewrite CR.
      replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
      replace (Z.testbit x (Z.succ (Z.of_nat n))) with (Z.testbit (x/2) (Z.of_nat n)).
      replace (Z.testbit y (Z.succ (Z.of_nat n))) with (Z.testbit (y/2) (Z.of_nat n)).
      reflexivity.
      rewrite (decomp y) at 2.
      rewrite Z.testbit_succ_r. reflexivity. lia.
      rewrite (decomp x) at 2.
      rewrite Z.testbit_succ_r. reflexivity. lia.
    }
Qed.

Lemma testbit_add_sound : forall n x y,
    Z.testbit (x + y) (Z.of_nat n) =
      xorb (xorb (Z.testbit x (Z.of_nat n))
              (Z.testbit y (Z.of_nat n))) (add_carry_bit x y false n).
Proof.
  intros.
  rewrite <- xtestbit_add_sound.
  f_equal. simpl; ring.
Qed.

Lemma Ztestbit_add_sound : forall n x y,
    n >= 0 ->
    Z.testbit (x + y) n =
      xorb (xorb (Z.testbit x n)
              (Z.testbit y n)) (add_carry_bit x y false (Z.to_nat n)).
Proof.
  intros.
  assert (n = Z.of_nat (Z.to_nat n)) by lia.
  rewrite H0.
  rewrite testbit_add_sound.
  rewrite <- H0.
  reflexivity.
Qed.


(** [minimum_carries] i.e. Lemma 2 of [1] *)

Lemma minimum_carries : forall a i b j,
    gamma a i ->
    gamma b j ->
    forall n c, add_carry_bit (fst a) (fst b) c n  = true -> add_carry_bit i j c n = true.
Proof.
  unfold gamma. intros.
  destruct a as (va,ma).
  destruct b as (vb,mb). simpl in *.
  subst.
  revert H1.
  revert i ma j mb c.
  induction n.
  - simpl. auto.
  - intros.
    rewrite carry_bit_rew with (n:=S n).
    rewrite carry_bit_rew in H1.
    cbv zeta in *.
    rewrite! orb_true_iff in H1.
    rewrite! Z.land_spec in H1.
    rewrite! Z.lnot_spec in H1 by lia.
    rewrite! andb_true_iff in H1.
    destruct H1 as [H1 | H1].
    + dand.
      rewrite H2,H1.  reflexivity.
    + destruct H1 as (CB & XORB).
      apply IHn in CB.
      rewrite CB.
      destruct (Z.testbit i (Z.of_nat n));
        destruct (Z.testbit j (Z.of_nat n)); try reflexivity.
      discriminate.
Qed.


(** [tnum_add a b] performs the abstract addition *)
Definition tnum_add (a b: Z * Z): Z * Z :=
  let sv    := (fst a) + (fst b) in
  let sm    := (snd a) + (snd b) in
  let sigma := sm + sv in
  let chi   := Z.lxor sigma sv in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land sv (Z.lnot mu), mu).

(* In the definition of [tnum_add], we remark that
   the definition of [sigma] i.e  (fst a) + (fst b) + (snd a) + (snd b)
   can computed as [(fst a) || (snd a) + (fst b) || (snd b) *)

Definition sigma (a b:tnum) := (fst a) + (fst b) + (snd a) + (snd b).

Definition sigma_lor (a b:tnum) := (Z.lor (fst a) (snd a) , Z.lor (fst b) (snd b)).

Lemma sigma_lor_sigma : forall a b i j,
    gamma a i ->
    gamma b j ->
    (sigma a b = fst (sigma_lor a b) + snd (sigma_lor a b))%Z.
Proof.
  intros.
  unfold sigma_lor.
  rewrite <- gamma_add_lor with (1:= H).
  rewrite <- gamma_add_lor with (1:= H0).
  unfold sigma; simpl.
  ring.
Qed.

(** As a result, we get [tnum_add'] an equivalent definition of [tnum] *)

Definition tnum_add' (a b: Z * Z): Z * Z :=
  let sv    := (fst a) + (fst b) in
  let sm    := (snd a) + (snd b) in
  let sigma := (Z.lor (fst a) (snd a))  + (Z.lor (fst b) (snd b)) in
  let chi   := Z.lxor sigma sv in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land sv (Z.lnot mu), mu).

Lemma tnum_add_eq : forall a b i j,
    gamma a i ->
    gamma b j ->
    tnum_add a b = tnum_add' a b.
Proof.
  intros.
  cbv beta delta [tnum_add tnum_add'].
  rewrite <- gamma_add_lor with (1:= H).
  rewrite <- gamma_add_lor with (1:= H0).
  cbv zeta.
  f_equal.
  f_equal. f_equal.
  f_equal. f_equal. ring.
  f_equal. f_equal. ring.
Qed.


(** [maximum_carries] is Lemma 3 *)
Lemma maximum_carries : forall a i b j,
    gamma a i ->
    gamma b j ->
    forall n,
      add_carry_bit i j false n = true ->
      add_carry_bit (fst (sigma_lor a b)) (snd (sigma_lor a b)) false n = true.
Proof.
  intros.
  unfold sigma_lor.
  destruct a as (va,ma).
  destruct b as (vb,mb).
  unfold gamma in *. simpl in *.
  subst.
  induction n.
  - simpl in *. congruence.
  - simpl in H1.
    simpl.
    rewrite! Z.lor_spec.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    destruct (add_carry_bit i j false n).
    + rewrite IHn by reflexivity.
      clear IHn.
      elim_testbit; try reflexivity.
      discriminate.
    + clear IHn.
      elim_testbit; try reflexivity; try discriminate.
Qed.


(** [tnum_add_sound] proves the soundness of the abstract addition *)
Lemma tnum_add_sound : forall a b i j,
    gamma a i ->
    gamma b j ->
    gamma (tnum_add a b) (i+j).
Proof.
  destruct a as (va,ma).
  destruct b as (vb,mb).
  intros.
  rewrite tnum_add_eq with (i:=i) (j:=j) by assumption.
  unfold gamma.
  apply Z.bits_inj.
  unfold Z.eqf.
  simpl.  intros.
  rewrite! Z.land_spec.
  assert (N : n < 0 \/ n >= 0) by lia.
  destruct N.
  - destruct n; try lia; simpl.
    reflexivity.
 - rewrite! Ztestbit_add_sound by lia.
   rewrite! Z.lnot_spec by lia.
   rewrite! Z.lor_spec.
   rewrite Z.lxor_spec.
   destruct (add_carry_bit i j false (Z.to_nat n)) eqn:CB.
   + apply maximum_carries with (1:=H) (2:=H0) in CB.
     unfold sigma_lor in CB.
     simpl in CB.
     rewrite! Ztestbit_add_sound by lia.
     rewrite CB.
     rewrite! Z.lor_spec.
     unfold gamma in *.
     simpl in *.
     subst.
     rewrite! Z.land_spec.
     rewrite! Z.lnot_spec by lia.
     btauto.
   + rewrite! Ztestbit_add_sound by lia.
     rewrite! Z.lor_spec.
     destruct (add_carry_bit va vb false (Z.to_nat n)) eqn:CB'.
     * change va with (fst (va,ma)) in CB'.
       change vb with (fst (vb,mb)) in CB'.
       exfalso.
       specialize (minimum_carries _ _ _ _ H H0 _ _ CB').
       congruence.
     * unfold gamma in *.
       simpl in *.
       subst.
       rewrite! Z.land_spec.
       rewrite! Z.lnot_spec by lia.
       btauto.
Qed.
