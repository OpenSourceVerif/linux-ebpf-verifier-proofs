(**
Formalisation of the Tristate abstract domain from the paper

[1] Harishankar Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte. 2022.
Sound, precise, and fast abstract interpretation with tristate numbers. CGO'22

*)


Require Import ZArith Bool Lia.
Require Import Btauto.
(*Require Import Cdcl.Itauto.*)
Open Scope Z_scope.
Add Search  Blacklist "POrderedType".

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


Module Preliminary.
  Lemma Zodd_b2z : forall b, Z.odd (Z.b2z b) = b.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma decomp : forall x,
      (x = 2 * (x / 2) + Z.b2z (Z.odd x))%Z.
  Proof.
    intros.
    rewrite <- Z.bit0_odd.
    rewrite Z.bit0_mod.
    apply Z_div_mod_eq_full.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma add_shift : forall a b,
      ((a + b) / 2 =
         (a / 2 + (b / 2) + (Z.b2z (Z.odd a && Z.odd b))))%Z.
  Proof.
    intros.
    rewrite! Zodd_mod.
    destruct (Zeq_bool (a mod 2) 1 && Zeq_bool (b mod 2) 1) eqn:LB.
    - simpl.
      rewrite andb_true_iff in LB.
      destruct LB as (LB1 & LB2).
      apply Zeq_bool_eq in LB1.
      apply Zeq_bool_eq in LB2.
      lia.
    - simpl.
      rewrite andb_false_iff  in LB.
      destruct LB.
      apply Zeq_bool_neq in H.
      lia.
      apply Zeq_bool_neq in H.
      lia.
  Qed.


  Lemma sub_shift : forall a b,
      ((a - b) / 2 =
         (a / 2 - (b / 2) - (Z.b2z (negb (Z.odd a) && Z.odd b))))%Z.
  Proof.
    intros.
    rewrite! Zodd_mod.
    destruct (negb (Zeq_bool (a mod 2) 1) && Zeq_bool (b mod 2) 1) eqn:LB.
    - simpl.
      rewrite andb_true_iff in LB.
      destruct LB as (LB1 & LB2).
      rewrite negb_true_iff in LB1.
      apply Zeq_bool_neq in LB1.
      apply Zeq_bool_eq in LB2.
      lia.
    - simpl.
      rewrite andb_false_iff  in LB.
      destruct LB.
      rewrite negb_false_iff in H.
      apply Zeq_bool_eq in H.
      lia.
      apply Zeq_bool_neq in H.
      lia.
  Qed.



  Lemma b2z_div2 : forall b,
      (Z.b2z b / 2 = 0)%Z.
  Proof.
    destruct b; reflexivity.
  Qed.

End Preliminary.
Import Preliminary.


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
                  (orb
                    (andb (Z.testbit x n) (Z.testbit y  n)) (**r x[n] = y[n] = 1 *)
                    (andb pc (xorb (Z.testbit x n) (Z.testbit y n)))) (**r x[n] = 1 /\ y[n] = 0 or x[n] = 0 /\ y[n] = 1 *)
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

(** [sub_borrow_bit x y c n] computes the nth borrow bit
    of the substraction of x - y - c *)
Fixpoint sub_borrow_bit (x y : Z) (c:bool) (n:nat) :=
  match n with
  | O => c
  | S n' =>
      let pc := sub_borrow_bit x y c n' in
      let n := Z.of_nat n' in
                  (orb
                    (andb (negb (Z.testbit x n))
                          (Z.testbit y  n)) (**r x[n] = 0 /\ y[n] = 1*)
                     (andb pc (negb (xorb (Z.testbit x n) (Z.testbit y n)))))  (**r x[n] = y[n] *)
  end.

Lemma borrow_bit_rew : forall  (x y : Z) (c:bool) (n:nat),
    sub_borrow_bit x y c n =
  match n with
  | O => c
  | S n' =>
      let pc := sub_borrow_bit x y c n' in
      let n := Z.of_nat n' in
                  (orb (andb (negb (Z.testbit x n))
                          (Z.testbit y  n))
                     (andb pc (negb (xorb (Z.testbit x n) (Z.testbit y n)))))
  end.
Proof.
  destruct n; try reflexivity.
Qed.

Lemma xtestbit_sub_sound : forall n x y c0,
    Z.testbit (x - y - Z.b2z c0) (Z.of_nat n) =
      xorb (xorb (Z.testbit x (Z.of_nat n))
              (Z.testbit y (Z.of_nat n))) (sub_borrow_bit x y c0 n).
Proof.
  induction n.
  - simpl.
    intros.
    rewrite! Z.odd_sub.
    rewrite Zodd_b2z.
    reflexivity.
  -
    intros.
    rewrite (decomp (x - y - Z.b2z c0)) at 1.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) at 1 by lia.
    rewrite Z.testbit_succ_r by lia.
    replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
    rewrite borrow_bit_rew.
    cbv zeta.
    rewrite (decomp x) at 2.
    rewrite (decomp y) at 2.
    rewrite! Z.testbit_succ_r by lia.
    rewrite sub_shift.
    rewrite sub_shift.
    rewrite b2z_div2.
    rewrite Z.odd_sub.
    rewrite! Zodd_b2z.
    assert (CR: (exists cr, Z.b2z (negb (Z.odd x) && Z.odd y) +
     Z.b2z (negb (xorb (Z.odd x) (Z.odd y)) && c0) = Z.b2z cr)).
    {
      destruct (Z.odd x),(Z.odd y),c0; simpl;
        try (exists true;  reflexivity);
        try (exists false;  reflexivity).
    }
    destruct CR as (cr& CR).
    replace ((x / 2 - y / 2 - Z.b2z (negb (Z.odd x) && Z.odd y) - 0 -
     Z.b2z (negb (xorb (Z.odd x) (Z.odd y)) && c0)))
      with  (x / 2 - y / 2 - Z.b2z cr)%Z by lia.
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
      rewrite borrow_bit_rew.
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

Lemma testbit_sub_sound : forall n x y,
    Z.testbit (x - y) (Z.of_nat n) =
      xorb (xorb (Z.testbit x (Z.of_nat n))
              (Z.testbit y (Z.of_nat n))) (sub_borrow_bit x y false n).
Proof.
  intros.
  rewrite <- xtestbit_sub_sound.
  f_equal. simpl; ring.
Qed.

Lemma Ztestbit_sub_sound : forall n x y,
    n >= 0 ->
    Z.testbit (x - y) n =
      xorb (xorb (Z.testbit x n)
              (Z.testbit y n)) (sub_borrow_bit x y false (Z.to_nat n)).
Proof.
  intros.
  assert (n = Z.of_nat (Z.to_nat n)) by lia.
  rewrite H0.
  rewrite testbit_sub_sound.
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

Definition tnum_sub (a b: tnum): tnum :=
  let dv    :=  (fst a) - (fst b) in
  let alpha :=  dv + (snd a) in
  let beta  := dv - (snd b) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land alpha (Z.lnot mu), mu).




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
   (**r we get the equal because of gamma_add_lor: + is or *)
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
      rewrite andb_true_l in H1.
      rewrite orb_true_iff in H1.
      rewrite andb_true_iff in H1.
      destruct H1.
      * destruct H. rewrite H. rewrite H0.
        btauto.
      *  elim_testbit; try reflexivity.
         discriminate.
    + clear IHn.
      rewrite andb_false_l in H1.
      rewrite orb_false_r in H1.
      rewrite andb_true_iff in H1.
      destruct H1. rewrite H. rewrite H0.
      btauto.
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
     remember (add_carry_bit (Z.land i (Z.lnot ma)) (Z.land j (Z.lnot mb)) false (Z.to_nat n)) as KKK eqn: Hk.
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

(** substraction *)


Definition tnum_sub' (a b: tnum): tnum :=
  let dv    :=  (fst a) - (fst b) in
  let alpha :=  (Z.lor (fst a) (snd a)) - fst b in
  let beta  :=  (fst a) - (Z.lor (fst b) (snd b)) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land alpha (Z.lnot mu), mu).

Lemma tnum_sub_eq : forall a b i j,
    gamma a i ->
    gamma b j ->
    tnum_sub a b = tnum_sub' a b.
Proof.
  intros.
  cbv beta delta [tnum_sub tnum_sub'].
  rewrite <- gamma_add_lor with (1:= H).
  rewrite <- gamma_add_lor with (1:= H0).
  cbv zeta.
  replace (fst a - fst b + snd a) with (fst a + snd a - fst b) by lia.
  replace (fst a - fst b - snd b) with (fst a - (fst b + snd b)) by lia.
  reflexivity.
Qed.

Lemma lor_land_not : forall x y, Z.lor (Z.land x (Z.lnot y)) y = Z.lor x y.
Proof.
  intros.
  rewrite Z.lor_land_distr_l.
  rewrite (Z.lor_comm (Z.lnot _)).
  rewrite Z.lor_lnot_diag.
  rewrite Z.land_m1_r.
  reflexivity.
Qed.

Lemma Zland_lb : forall x1 b1 x2 b2,
    Z.land (2 * x1 + Z.b2z b1) (2* x2 + Z.b2z b2) =
      2 * Z.land x1 x2 + Z.b2z (b1 && b2).
Proof.
  intros.
  apply Z.bits_inj.
  repeat intro.
  rewrite Z.land_spec.
  assert (n = 0 \/ n < 0 \/ n > 0) by lia.
  destruct H as [H | [H | H]].
  - subst. rewrite! Z.testbit_0_r.
    reflexivity.
  - destruct n; try lia.
    simpl. reflexivity.
  - assert (n = Z.succ (n - 1)) by lia.
    rewrite H0.
    rewrite ! Z.testbit_succ_r by lia.
    rewrite Z.land_spec.
    reflexivity.
Qed.


Lemma Zodd_land : forall z1 z2,
    Z.odd (Z.land z1 z2) = Z.odd z1 && Z.odd z2.
Proof.
  intros.
  rewrite (decomp z1).
  rewrite (decomp z2).
  rewrite Zland_lb.
  rewrite! Z.odd_add.
  rewrite! Z.odd_mul.
  rewrite! Z.odd_2.
  rewrite! Zodd_b2z.
  reflexivity.
Qed.

Lemma Zlor_lb : forall x1 b1 x2 b2,
    Z.lor (2 * x1 + Z.b2z b1) (2* x2 + Z.b2z b2) =
      2 * Z.lor x1 x2 + Z.b2z (b1 || b2).
Proof.
  intros.
  apply Z.bits_inj.
  repeat intro.
  rewrite Z.lor_spec.
  assert (n = 0 \/ n < 0 \/ n > 0) by lia.
  destruct H as [H | [H | H]].
  - subst. rewrite! Z.testbit_0_r.
    reflexivity.
  - destruct n; try lia.
    simpl. reflexivity.
  - assert (n = Z.succ (n - 1)) by lia.
    rewrite H0.
    rewrite ! Z.testbit_succ_r by lia.
    rewrite Z.lor_spec.
    reflexivity.
Qed.


Lemma Zodd_lor : forall z1 z2,
    Z.odd (Z.lor z1 z2) = Z.odd z1 || Z.odd z2.
Proof.
  intros.
  rewrite (decomp z1).
  rewrite (decomp z2).
  rewrite Zlor_lb.
  rewrite! Z.odd_add.
  rewrite! Z.odd_mul.
  rewrite! Z.odd_2.
  rewrite! Zodd_b2z.
  reflexivity.
Qed.


Lemma Zlnot_lb : forall x1 b1,
    Z.lnot (2 * x1 + Z.b2z b1)  =
      2 * Z.lnot x1 + Z.b2z (negb b1).
Proof.
  intros.
  unfold Z.lnot.
  unfold Z.b2z,negb;destruct b1;lia.
Qed.


Lemma Zodd_lnot : forall z,
    Z.odd (Z.lnot z) = negb (Z.odd z).
Proof.
  intros.
  rewrite (decomp z).
  rewrite Zlnot_lb.
  rewrite! Z.odd_add.
  rewrite! Z.odd_mul.
  rewrite! Z.odd_2.
  rewrite! Zodd_b2z.
  reflexivity.
Qed.


Lemma Zlxor_lb : forall x1 b1 x2 b2,
    Z.lxor (2 * x1 + Z.b2z b1) (2* x2 + Z.b2z b2) =
      2 * Z.lxor x1 x2 + Z.b2z (xorb b1  b2).
Proof.
  intros.
  apply Z.bits_inj.
  repeat intro.
  rewrite Z.lxor_spec.
  assert (n = 0 \/ n < 0 \/ n > 0) by lia.
  destruct H as [H | [H | H]].
  - subst. rewrite! Z.testbit_0_r.
    reflexivity.
  - destruct n; try lia.
    simpl. reflexivity.
  - assert (n = Z.succ (n - 1)) by lia.
    rewrite H0.
    rewrite ! Z.testbit_succ_r by lia.
    rewrite Z.lxor_spec.
    reflexivity.
Qed.

Lemma Zodd_lxor : forall z1 z2,
    Z.odd (Z.lxor z1 z2) = xorb (Z.odd z1) (Z.odd z2).
Proof.
  intros.
  rewrite (decomp z1).
  rewrite (decomp z2).
  rewrite Zlxor_lb.
  rewrite! Z.odd_add.
  rewrite! Z.odd_mul.
  rewrite! Z.odd_2.
  rewrite! Zodd_b2z.
  reflexivity.
Qed.

Lemma xorb_false_iff :
  forall  x y, xorb x y = false <-> x = y.
Proof.
  split; intros.
  - apply xorb_eq; auto.
  - subst.
    apply xorb_nilpotent.
Qed.

Lemma minimum_borrows : forall va ma i vb mb j,
    gamma (va,ma) i ->
    gamma (vb,mb) j ->
    forall n c,
      sub_borrow_bit (Z.lor va ma) vb c n  = true ->
      sub_borrow_bit i j c n = true.
Proof.
  intros va ma i vb mb j Hgi Hgj n c Hsub.
  unfold gamma in *. simpl in *.
  induction n.
  - simpl in *. congruence.
  - simpl in *.
    rewrite! Z.lor_spec in *.
    rewrite! orb_true_iff in *.
    rewrite! andb_true_iff in *.
    rewrite! negb_true_iff in *.
    rewrite! orb_false_iff in *.
    destruct Hsub as [Hsub | Hsub].
    + destruct Hsub as ((Hva & Hma) & Hvb).
      subst.
      rewrite! Z.land_spec in *.
      rewrite! Z.lnot_spec in * by lia.
      rewrite! andb_true_iff in *.
      rewrite Hma in Hva.
      unfold negb in Hva.
      rewrite! andb_false_iff in *.
      destruct Hvb as (Hj & Hmb).
      rewrite Hj.
      destruct Hva as [Hva | Hva].
      * rewrite Hva.
        intuition.
      * inversion Hva. 
    + destruct Hsub as (Hsub & Hxor).
      specialize (IHn Hsub).
      rewrite IHn.
      rewrite xorb_false_iff in Hxor.
      destruct (Z.testbit vb (Z.of_nat n)) eqn: Hvb.
      * subst.
        rewrite! Z.land_spec in *.
        rewrite! Z.lnot_spec in * by lia.
        rewrite! andb_true_iff in *.
        destruct Hvb as (Hj & Hmb).
        rewrite Hj.
        destruct (Z.testbit i (Z.of_nat n)) eqn: Hi.
        {
          intuition idtac.
        }
        intuition idtac.
      * rewrite orb_false_iff in Hxor.
        destruct Hxor as (Hva & Hma).
        subst.
        rewrite! Z.land_spec in *.
        rewrite! Z.lnot_spec in * by lia.
        rewrite! andb_false_iff in *.
        rewrite Hma in Hva.
        unfold negb in Hva.
        destruct Hva as [Hi | HF]; [| inversion HF].
        rewrite Hi.
        destruct Hvb as [Hj | Hmb].
        {
          rewrite Hj. unfold xorb.
          auto.
        }
        rewrite negb_false_iff in Hmb.
        destruct (Z.testbit j (Z.of_nat n)) eqn: Hj.
        { auto. }
        unfold xorb.
        auto.
Qed.

Lemma maximum_borrows : forall va ma  i vb mb j,
    gamma (va,ma) i ->
    gamma (vb,mb) j ->
    forall n,
      sub_borrow_bit i j false n = true ->
      sub_borrow_bit va (Z.lor vb mb) false n = true.
Proof.
  intros va ma  i vb mb j Hgi Hgj n Hsub.
  unfold gamma in *; simpl in *.
  induction n.
  - simpl in *.
    auto.
  - simpl in *.
    rewrite! Z.lor_spec in *.
    rewrite! orb_true_iff in *.
    rewrite! andb_true_iff in *.
    rewrite! negb_true_iff in *.
    destruct Hsub as [Hsub | Hsub].
    + destruct Hsub as (Hi & Hj).
      subst.
      rewrite! Z.land_spec in *.
      rewrite! Z.lnot_spec in * by lia.
      rewrite Hi, Hj.
      rewrite andb_false_l.
      rewrite andb_true_l.
      left.
      destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; auto.
    + destruct Hsub as (Hsub & Hxor).
      specialize (IHn Hsub).
      rewrite IHn.
      rewrite xorb_false_iff in Hxor.
      subst.
      rewrite! Z.land_spec in *.
      rewrite! Z.lnot_spec in * by lia.
      rewrite Hxor.
      destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb.
      * rewrite orb_true_r.
        destruct (Z.testbit j (Z.of_nat n)) eqn: Hj.
        { rewrite andb_true_l.
          destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; auto.
        }
        destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; auto.
      * destruct (Z.testbit j (Z.of_nat n)) eqn: Hj.
        {
          destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; auto.
        }
        destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; auto.
Qed.  

(*
Lemma minimum_borrows : forall va ma  i vb mb j,
    gamma (va,ma) i ->
    gamma (vb,mb) j ->
    forall n,
      sub_borrow_bit i j false n = true ->
      sub_borrow_bit (Z.lor va ma) vb false n = true ->
      sub_borrow_bit va (Z.lor vb mb) false n = true ->
      sub_borrow_bit va vb false n = true.
Proof.
  intros.
  unfold gamma in *. simpl in *.
  induction n.
  - simpl in *. congruence.
  - simpl in *.
    simpl.
    rewrite! Z.lor_spec in *.
    rewrite! orb_true_iff in *.
    rewrite! andb_true_iff in *.
    rewrite! negb_true_iff in *.
    rewrite! orb_true_iff in *.
    rewrite! orb_false_iff in *.
    intuition idtac.
    + rewrite H3 in *.
      rewrite orb_false_l in H6.
      simpl.
      destruct (Z.testbit vb (Z.of_nat n)) eqn:VB.
      tauto.
      right.
      split;auto.
      rewrite <- H in H3.
      rewrite! Z.land_spec in *.
      rewrite! Z.lnot_spec in * by lia.
      rewrite andb_false_iff  in H3.
      destruct H3.
      rewrite xorb_false_r in H6.
      rewrite H2 in *.
      clear H2.
      subst.
      rewrite lor_land_not in *.
      * induction n.
        {
          simpl in *.
          rewrite Zodd_land in VB.
          rewrite H5 in  VB.
          rewrite Zodd_lnot in VB.
          rewrite H4 in VB. simpl in VB.


      destruct VB. congruence.
      rewrite xorb_false_r in H6.
      rewrite H1 in *.
      rewrite H6 in *.
      simpl in *. rewrite H4 in *. simpl in *.
      rewrite lor_land_not in *.


    destruct (sub_borrow_bit (Z.lor va ma) vb false n) eqn:CB1;
      destruct (sub_borrow_bit va (Z.lor vb mb) false n) eqn:CB2.
    + rewrite IHn by reflexivity.
      subst.
      rewrite Z.land_spec in *.
      rewrite Z.lnot_spec in * by lia.
      elim_testbit;try reflexivity ; try discriminate.
      simpl. simpl in *.
      rewrite! H in *.
      exfalso.
      specialize (IHn eq_refl eq_refl).
      revert CB1 CB2 IHn.
      clear. { induction n.
               - simpl. discriminate.
               - simpl.
                 rewrite! Z.lor_spec.
                 rewrite! Z.land_spec.
                 rewrite! Z.lnot_spec by lia.
                 destruct (sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false n).
                 destruct (sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false n).
                 destruct (sub_borrow_bit i j false n); simpl.
                 intros.
                 elim_testbit;try discriminate.
                 simpl in *.




      unfold negb in H1 at 1.
      rewrite andb_false_l in H1.
      rewrite orb_false_l in H1.
      destruct (Z.testbit vb (Z.of_nat n)) eqn:VB.
      *  simpl in H1. rewrite andb_true_r in H1.
         rewrite IHn by assumption.
         rewrite andb_true_l. clear IHn.
         btauto.




    destruct (sub_borrow_bit (Z.lor (Z.land i (Z.lnot ma)) ma) (Z.land j (Z.lnot mb)) false n).
    +
      rewrite (IHn eq_refl).
      rewrite! Z.lor_spec in H1.
      rewrite! Z.land_spec in H1.
      rewrite! Z.lnot_spec in H1 by lia.
      rewrite andb_true_l in H1.
      elim_testbit;try discriminate;try reflexivity.
    + elim_testbit;try discriminate;try reflexivity.
    destruct (sub_borrow_bit i j false n).
    + rewrite IHn by reflexivity.
      clear IHn.
      rewrite andb_true_l in H1.
      rewrite orb_true_iff in H1.
      rewrite andb_true_iff in H1.
      destruct H1.
      * destruct H.
        rewrite negb_true_iff in H.
        rewrite H. rewrite H0.
        btauto.
      *  elim_testbit; try reflexivity; try discriminate.
         discriminate. discriminate. simpl. simpl in H.
    + clear IHn.
      rewrite andb_false_l in H1.
      rewrite orb_false_r in H1.
      rewrite andb_true_iff in H1.
      destruct H1. rewrite H. rewrite H0.
      btauto.
Qed.
*)

Ltac elim_testbit_eqn :=
  (repeat
  match goal with
  | |- context[Z.testbit ?A ?B]  =>
      let f:= fresh "TB" in
      destruct (Z.testbit A B) eqn:f
  end); try reflexivity;
  repeat match goal with
  | H : Z.testbit ?A ?B = true |- _ => rewrite H in *; revert H
  end; try discriminate;
  match goal with
  | H : context[Z.testbit ?A ?B] |- _ =>
      let f := fresh "TB" in
      destruct (Z.testbit A B) eqn:f;
      revert f
  end.

Lemma sub_eq : forall x,  - x = Z.lnot (x + -1).
Proof.
  intros.
  replace (x + (-1)) with (x -1) by lia.
  rewrite Z.lnot_pred. reflexivity.
Qed.

Definition tnum_pred (a : tnum) :=
  let sv    := (fst a) + -1 in
  let sigma := (snd a) + sv in
  let chi   := Z.lxor sigma sv in
  let mu    := Z.lor chi (snd a) in
    (Z.land sv (Z.lnot mu), mu).

Lemma tnum_pred_eq : forall a,
    tnum_add a (-1,0) = tnum_pred a.
Proof.
  unfold tnum_pred,tnum_add.
  intros.
  simpl.
  rewrite Z.lor_0_r.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Definition tnum_not (a:tnum) :=
  (Z.lnot (Z.lor (fst a)  (snd a)) , snd a).


Lemma fst_tnum_not : forall a,
    fst (tnum_not a) = Z.lnot (Z.lor (fst a)  (snd a)).
Proof.
  unfold tnum_not.
  reflexivity.
Qed.

Lemma fst_tnum_pred : forall a,
    fst (tnum_pred a) =
  let sv    := (fst a) + -1 in
  let sigma := (snd a) + sv in
  let chi   := Z.lxor sigma sv in
  let mu    := Z.lor chi (snd a) in
    Z.land sv (Z.lnot mu).
Proof.
  reflexivity.
Qed.

(* x - y = x + ( - y) = x + not (x + -1) *)
Definition tnum_sub_by_add_not_pred (a b:tnum) :=
  tnum_add a (tnum_not (tnum_pred b)).

(* x - y = not (not x + y) *)
Definition tnum_sub_by_not_not_add (a b:tnum) :=
  tnum_not (tnum_add (tnum_not a) b).

Lemma sub_not_not_add : forall x y, x - y = Z.lnot ((Z.lnot x) + y).
Proof.
  intros.
  rewrite <- (Z.lnot_involutive (x - y)).
  rewrite Z.lnot_sub.
  f_equal.
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

Lemma gamma_const : forall c,
  gamma (c, 0) c.
Proof.
  unfold gamma.
  simpl. intros.
  rewrite Z.lnot_0.
  rewrite Z.land_m1_r.
  reflexivity.
Qed.

Lemma tnum_sub_by_add_sound : forall a i b j,
    gamma a i ->
    gamma b j ->
    gamma (tnum_sub_by_add_not_pred a b) (i - j).
Proof.
  intros.
  unfold tnum_sub_by_add_not_pred.
  apply tnum_add_sound; auto.
  rewrite sub_eq.
  apply tnum_not_sound; auto.
  rewrite <- tnum_pred_eq.
  apply tnum_add_sound; auto.
  apply gamma_const.
Qed.


Lemma tnum_sub_by_not_not_add_sound : forall a i b j,
    gamma a i ->
    gamma b j ->
    gamma (tnum_sub_by_not_not_add a b) (i - j).
Proof.
  intros.
  unfold tnum_sub_by_not_not_add.
  rewrite sub_not_not_add.
  apply tnum_not_sound; auto.
  apply tnum_add_sound; auto.
  apply tnum_not_sound; auto.
Qed.


Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof.
  destruct b; simpl;lia.
Qed.


Lemma Zlor_div2 : forall x y, (Z.lor x y)/ 2 = Z.lor (x / 2) (y / 2).
Proof.
  intros.
  rewrite (decomp x) at 1.
  rewrite (decomp y) at 1.
  rewrite Zlor_lb.
  generalize (b2z_range (Z.odd x || Z.odd y)).
  lia.
Qed.


Lemma Zland_div2 : forall x y, (Z.land x y)/ 2 = Z.land (x / 2) (y / 2).
Proof.
  intros.
  rewrite (decomp x) at 1.
  rewrite (decomp y) at 1.
  rewrite Zland_lb.
  generalize (b2z_range (Z.odd x && Z.odd y)).
  lia.
Qed.

Lemma Zlnot_div2 : forall x, (Z.lnot x)/ 2 = Z.lnot (x / 2).
Proof.
  intros.
  rewrite (decomp x) at 1.
  rewrite Zlnot_lb.
  generalize (b2z_range (negb (Z.odd x))).
  lia.
Qed.



Lemma Zlxor_div2 : forall x y, (Z.lxor x y)/ 2 = Z.lxor (x / 2) (y / 2).
Proof.
  intros.
  rewrite (decomp x) at 1.
  rewrite (decomp y) at 1.
  rewrite Zlxor_lb.
  generalize (b2z_range (xorb (Z.odd x)  (Z.odd y))).
  lia.
Qed.


Ltac bits :=
  repeat match goal with
    | |- context[Z.testbit (Z.land _ _) _] => rewrite Z.land_spec
    | |- context[Z.testbit (Z.lor _ _) _] => rewrite Z.lor_spec
    | |- context[Z.testbit (Z.lnot _) _] => rewrite Z.lnot_spec
    | |- context[Z.testbit (Z.lxor _ _) _] => rewrite Z.lxor_spec
    | |- context[Z.testbit (Z.add _ _) _] => rewrite add_shift
    | |- context[Z.testbit (Z.sub _ _) _] => rewrite sub_shift
    | |-  context[(Z.land ?A ?B) / 2] => rewrite Zland_div2
    | |-  context[(Z.lor ?A ?B) / 2] => rewrite Zlor_div2
    | |-  context[(Z.lxor ?A ?B) / 2] => rewrite Zlxor_div2
    | |-  context[(Z.lnot  ?A ) / 2] => rewrite Zlnot_div2

    | |-  context[(Z.sub ?A ?B) / 2] => rewrite sub_shift

    | |-  context[(Z.odd (Z.land ?A ?B))] => rewrite Zodd_land
    | |-  context[(Z.odd (Z.add ?A ?B))] => rewrite Z.odd_add
    | |-  context[(Z.odd (Z.add ?A ?B))] => rewrite Z.odd_add
    | |-  context[(Z.odd (Z.sub ?A ?B))] => rewrite Z.odd_sub
    | |-  context[(Z.odd (Z.lor ?A ?B))] => rewrite Zodd_lor
    | |-  context[(Z.odd (Z.lxor ?A ?B))] => rewrite Zodd_lxor
    | |-  context[(Z.odd (Z.lnot ?B))] => rewrite Zodd_lnot
    | |-  context[Z.odd (Z.b2z ?B)] => rewrite Zodd_b2z
    | |-  context[Z.b2z ?X / 2] => rewrite Z.b2z_div2
    | |-  context[Z.odd 0]      => rewrite Z.odd_0
    | |-  context[Z.testbit 0 _] => rewrite Z.bits_0
    | |-  context[Z.testbit _ 0] => rewrite Z.bit0_odd
    end.

Lemma arrow_implb : forall b1 b2 b3 b4,
    orb (negb (eqb b1 b2)) (eqb b3 b4) = true <->
    (b1 = b2 -> b3 = b4).
Proof.
  intros.
  rewrite orb_true_iff.
  rewrite negb_true_iff.
  rewrite eqb_false_iff.
  rewrite eqb_true_iff.
  destruct b1,b2; intuition congruence.
Qed.

Lemma eqb_implb : forall b1 b2,
    eqb b1 b2 = andb (implb b1 b2) (implb b2 b1).
Proof.
  destruct b1,b2;reflexivity.
Qed.

Lemma implb_andb_orb : forall b1 b2,
    (implb b1 b2) = orb (negb b1) b2.
Proof.
  destruct b1,b2;reflexivity.
Qed.

Ltac btauto_ext :=
  repeat
    (match goal with
     | |- context[(@eq bool ?A1 ?A2) -> (@eq bool ?B1 ?B2)] =>
         rewrite <- arrow_implb
     end) ;
  repeat rewrite eqb_implb;
  repeat rewrite implb_andb_orb; btauto.


Lemma minimal_borrows : forall n va ma vb mb i j,
    gamma (va, ma) i ->
    gamma (vb, mb) j ->
    sub_borrow_bit (Z.lor va ma) vb false n = true ->
    sub_borrow_bit i j false n = true.
Proof.
  induction n.
  - simpl. auto.
  - intros. simpl in H1.
    destruct (sub_borrow_bit (Z.lor va ma) vb false) eqn:SB.
    +
    simpl.
    eapply IHn in SB; eauto.
    rewrite SB.
    revert H1.
    apply arrow_implb.
    rewrite! eqb_implb.
    rewrite! implb_andb_orb.
    unfold gamma in *. simpl in *.
    subst. bits;try lia.
    btauto.
    + simpl.
    revert H1.
    apply arrow_implb.
    rewrite! eqb_implb.
    rewrite! implb_andb_orb.
    unfold gamma in *. simpl in *.
    subst. bits;try lia.
    btauto.
Qed.




Lemma maximal_borrows : forall n va ma vb mb i j,
    gamma (va, ma) i ->
    gamma (vb, mb) j ->
    sub_borrow_bit i j false n = true ->
    sub_borrow_bit va (Z.lor vb mb) false n = true
.
Proof.
  induction n.
  - simpl. auto.
  - intros. simpl in H1.
    destruct (sub_borrow_bit i j  false) eqn:SB.
    +
    simpl.
    eapply IHn in SB; eauto.
    rewrite SB.
    revert H1.
    apply arrow_implb.
    rewrite! eqb_implb.
    rewrite! implb_andb_orb.
    unfold gamma in *. simpl in *.
    subst. bits;try lia.
    btauto.
    + simpl.
    revert H1.
    apply arrow_implb.
    rewrite! eqb_implb.
    rewrite! implb_andb_orb.
    unfold gamma in *. simpl in *.
    subst. bits;try lia.
    btauto.
Qed.



Lemma Ztestbit_1 : forall n,
    Z.testbit 1 n = if Z.eq_dec n 0 then true else false.
Proof.
  intros.
  destruct (Z.eq_dec n 0).
  subst;reflexivity.
  destruct n; try reflexivity.
  lia.
Qed.

Lemma gamma_div2 : forall va ma i,
    gamma (va,ma) i ->
    gamma (va / 2 , ma /2 ) (i/2).
Proof.
  unfold gamma in *. simpl in *.
  intros. subst.
  rewrite Zland_div2.
  rewrite Zlnot_div2.
  reflexivity.
Qed.

Ltac elim_testbit_one_eqn :=
  match goal with
  | |- context[Z.testbit ?A ?B]  =>
      let f:= fresh "TB" in
      destruct (Z.testbit A B) eqn:f
  end.

Lemma sub_borrow_bit_0 : forall x y z,
    sub_borrow_bit x y z 0 = z.
Proof.
  reflexivity.
Qed.

Lemma Zsub_borrow_bit_0 : forall x y z,
    sub_borrow_bit x y z 0 = z.
Proof.
  reflexivity.
Qed.


(*
Lemma sub_uncertain : forall n va ma vb mb i j,
    gamma (va,ma) i ->
    gamma (vb,mb) j ->
    Z.testbit (Z.lor (Z.lxor (Z.lor va ma - vb)
                        (va - Z.lor vb mb)) (Z.lor ma mb)) (Z.of_nat n) =
   orb (xorb (sub_borrow_bit (Z.lor va ma) vb false n)
          (sub_borrow_bit va (Z.lor vb mb) false n)) (Z.testbit (Z.lor ma mb) (Z.of_nat n)).
Proof.
  destruct n.
  { (*n = 0*)
    simpl. intros.
    rewrite! Zodd_lor.
    rewrite Zodd_lxor.
    rewrite! Z.odd_sub.
    unfold gamma in *; simpl in *; subst.
    rewrite! Zodd_lor.
    rewrite! Zodd_land.
    rewrite! Zodd_lnot.
    btauto.
  }
  intros.
  rewrite borrow_bit_rew.
  cbv zeta.
  replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
  rewrite <- !Z.div2_bits by lia.
  destruct n.
  { (* n = 1 *)
    simpl.
    bits.
    btauto.
  }
  rewrite borrow_bit_rew.
  cbv zeta.
  replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
  rewrite <- !Z.div2_bits by lia.
  bits.
  destruct n.
  {
    change (Z.of_nat 0) with 0.
    rewrite ! sub_borrow_bit_0.
    bits.
    rewrite! Zdiv_Zdiv by lia.
    replace (2 * 2) with 4 by reflexivity.
    rewrite! borrow_bit_rew.
    cbv zeta.
    change (Z.of_nat 0) with 0.
    bits.
    replace (Z.of_nat 1) with (Z.succ 0) by lia.
    rewrite <- !Z.div2_bits by lia.
    bits.
    btauto.





      rewrite! Zodd_land.
    rewrite! Zodd_lnot.
    rewrite! Zland_div2.
    rewrite! sub_shift.
    rewrite! Zland_div2.
    rewrite! Zlor_div2.
    rewrite! Zodd_land.
    rewrite! Z.odd_sub.
    rewrite! Zodd_b2z.
    rewrite! Zodd_lor.
    bits; try lia.
    rewrite! Zodd_land.
    btauto.
    bits; try lia.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      btauto_ext.
      btauto_ext.
      btauto_ext.
      btauto_ext.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      btauto_ext.
      btauto_ext.
      simpl.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_one_eqn.
      elim_testbit_eqn.
      btauto_ext.
      simpl.
      elim_testbit_one_eqn.



      rewrite! andb_true_iff in ODD.
      rewrite! negb_true_iff in ODD.
      destruct ODD as ((O1 & O2) & O3).
      unfold Z.b2z.
      assert (gamma (va / 2 , ma /2 ) (i/2)).
      {
        unfold gamma in *. simpl in *.
        subst.
        rewrite Zland_div2.
        rewrite Zlnot_div2.
        reflexivity.
      }
      assert (gamma (vb / 2 , mb /2 ) (j/2)).
      {
        unfold gamma in *. simpl in *.
        subst.
        rewrite Zland_div2.
        rewrite Zlnot_div2.
        reflexivity.
      }
      specialize (IHn _ _ _ _ _ _ H1 H2).
      revert IHn.
      bits.
      rewrite! Ztestbit_sub_sound.
      bits.
      rewrite Ztestbit_1.
      destruct (Z.eq_dec (Z.of_nat n) 0).
      * rewrite e.
        simpl.
        assert (n = 0%nat) by lia.
        subst.
        simpl.
        unfold gamma in *. simpl in *. subst.
        rewrite! Zodd_land.
        rewrite! Zodd_lnot.
        admit.
      *
*)

Lemma sub_borrow_bit_zero : forall n x,
sub_borrow_bit x 0 false n = false.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. intros.  rewrite IHn.
    bits. btauto.
Qed.

(*
Ltac xorb_def :=
  match goal with
  | |- context [xorb ?A ?B] =>
      let a := fresh in
      let ea := fresh in
      let b := fresh in
      let eb := fresh in
      remember A as a eqn:ea;
      remember B as b eqn:eb;
      rewrite (xorb_def a b);
      revert ea; revert eb
  end. *)

Goal forall x y,
    (if Z.odd x then false else Z.odd y) =
      negb (Z.odd x) && Z.odd y.
Proof.
  intros.
  destruct (Z.odd x);
    destruct (Z.odd y); try reflexivity.
Qed.

Lemma sub_div2 : forall x y,
    (x - y) / 2 =  (x / 2 - y /2 - Z.b2z (negb (Z.odd x) && Z.odd y)).
Proof.
  intros.
  rewrite (decomp x) at 1.
  rewrite (decomp y) at 1.
  destruct (Z.odd x); destruct (Z.odd y);
    unfold negb,andb,Z.b2z; lia.
Qed.


Definition tnum_sub_ext (a b: tnum) (z1:Z) (z2:Z) (z3:Z): tnum :=
  let dv    :=  (fst a) - (fst b) -  z1 in
  let alpha :=  (Z.lor (fst a) (snd a)) - fst b - z2 in
  let beta  :=  (fst a) - (Z.lor (fst b) (snd b) - z3) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land dv (Z.lnot mu), mu).

Ltac bsimpl :=
  match goal with
  | |- context [xorb true true] => change (xorb true true) with false
  | |- context [xorb true false] => change (xorb true false) with true
  | |- context [xorb false true] => change (xorb false true) with true
  | |- context [negb false] => change (negb false) with true
  | |- context [negb true] => change (negb true) with false
  | |- context [xorb false ?X] => rewrite xorb_false_l
  | |- context [xorb ?X false] => rewrite xorb_false_r
  | |- context [andb ?X false] => rewrite andb_false_r
  | |- context [andb false ?X] => rewrite andb_false_l
  | |- context [andb ?X true] => rewrite andb_true_r
  | |- context [andb true ?X] => rewrite andb_true_l
  | |- context [orb false ?X] => rewrite orb_false_l
  | |- context [orb ?X false] => rewrite orb_false_r
  end.


Lemma bool_case : forall b, b = false \/ b = true.
Proof.
  destruct b; intuition congruence.
Qed.

Definition pgoal i j va vb ma mb (a b c: Z) n :=
  Z.testbit
    (Z.land (i - j + a)
       (Z.lnot
          (Z.lor (Z.lxor (va - vb + ma + b) (va  - vb - mb + c))
             (Z.lor ma mb)))) (Z.of_nat n) =
  Z.testbit
    (Z.land (va - vb + a )
       (Z.lnot
          (Z.lor (Z.lxor (va - vb + ma + b) (va - vb - mb + c))
             (Z.lor ma mb)))) (Z.of_nat n).





Ltac ground t :=
  match t with
  | true => constr:(true)
  | false => constr:(true)
  | andb ?A ?B  => ground2 A B
  | orb ?A ?B   => ground2 A B
  | xorb ?A ?B  => ground2 A B
  | negb ?A     => ground A
  | xorb ?A ?B  => ground2 A B
  end
    with ground2 A B :=
      let t1 := ground A in
      let t2 := ground B in
      match constr:((t1 , t2)) with
      | (true , true) => constr:(true)
      |    _          => constr:(false)
      end.

Ltac evalt :=
  match goal with
  | |- context[Z.b2z ?T] =>
      let t := ground T in
      match t with
      | true => let t := (eval simpl in T) in
                change T with t ;
                change (Z.b2z true) with 1;
                change (Z.b2z false) with 0
      |   _  => fail
      end
  end.

Lemma gamma_testbit_mask_false:
  forall va ma i n0
  (Hg: gamma (va, ma) i)
  (Hor_ma : Z.testbit ma (Z.of_nat n0) = false),
  (Z.testbit va (Z.of_nat n0) = Z.testbit i (Z.of_nat n0)).
Proof.
  intros.
  unfold gamma in *; simpl in *; subst.
  rewrite ! Z.land_spec.
  rewrite ! Z.lnot_spec by lia.
  rewrite Hor_ma.
  btauto.
Qed.

Lemma tnum_sub_sound : forall a b i j
  ,
    gamma a i ->
    gamma b j ->
    gamma (tnum_sub a b) (i-j).
Proof.
  destruct a as (va,ma).
  destruct b as (vb,mb).
  intros i j Hgi Hgj.
  rewrite tnum_sub_eq with (i:=i) (j:=j) by assumption.
  unfold gamma.
  apply Z.bits_inj.
  unfold Z.eqf.
  simpl.  intros n.
  rewrite! Z.land_spec.
  replace (va - vb + ma) with ((va + ma) - vb) by lia.
  replace (va - vb - mb) with (va - (vb + mb)) by lia.
  assert (N : n < 0 \/ n >= 0) by lia.
  destruct N eqn: HN.
  - destruct n; try lia; simpl.
    reflexivity.
  - (**because here is `(va - vb)` n while we should have `(va - Z.lor vb mb)` *)
    rewrite! Ztestbit_sub_sound by lia.
    rewrite! Z.lnot_spec by lia.
    rewrite! Z.lor_spec.
    rewrite Z.lxor_spec.
    destruct (sub_borrow_bit i j false (Z.to_nat n)) eqn:CB.
   + apply maximum_borrows with (1:=Hgi) (2:=Hgj) in CB.
     rewrite! Ztestbit_sub_sound by lia.
     rewrite CB.
     rewrite! Z.lor_spec.
     unfold gamma in *.
     simpl in *.
     subst.
     rewrite! Z.land_spec.
     rewrite! Z.lnot_spec by lia.
     remember (sub_borrow_bit (Z.lor (Z.land i (Z.lnot ma)) ma) (Z.land j (Z.lnot mb)) false
     (Z.to_nat n)) as KKK eqn: HK.
     btauto.
   + rewrite! Ztestbit_sub_sound by lia.
     rewrite! Z.lor_spec.
     destruct (sub_borrow_bit (Z.lor va ma) vb false (Z.to_nat n)) eqn:CB'.
     * exfalso.
       specialize (minimum_borrows _ _ _ _ _ _ Hgi Hgj _ _ CB').
       congruence.
     * unfold gamma in *.
       simpl in *.
       subst.
       rewrite! Z.land_spec.
       rewrite! Z.lnot_spec by lia.
       btauto.
Qed.

Definition tnum_lshift (a: tnum) (shift: Z): tnum :=
  ( Z.shiftl (fst a) shift, Z.shiftl (snd a) shift).

Definition tnum_rshift (a: tnum) (shift: Z): tnum :=
  ( Z.shiftr (fst a) shift, Z.shiftr (snd a) shift).

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