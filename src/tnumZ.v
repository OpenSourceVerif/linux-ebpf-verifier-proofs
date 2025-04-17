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



Definition wf_tnum (a: tnum): Prop := (Z.land (fst a) (snd a)) = 0.

(** gamma definition implies wf *)
Lemma gamma_imply_wf: forall va ma i,
  gamma (va, ma) i ->
  wf_tnum (va, ma).
Proof.
  unfold gamma, wf_tnum; simpl.
  intros va ma i Hg.
  subst.
  rewrite <- Z.land_assoc.
  rewrite Z.land_comm with (b := ma).
  rewrite Z.land_lnot_diag.
  apply Z.land_0_r.
Qed.   


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

Definition tnum_sub_easy (a b: tnum): tnum :=
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

(** substraction: tnum_sub' is better than tnum_sub_easy, w.r.t. proof *)
Definition tnum_sub' (a b: tnum): tnum :=
  let dv    :=  (fst a) - (fst b) in
  let alpha :=  (Z.lor (fst a) (snd a)) - fst b in
  let beta  :=  (fst a) - (Z.lor (fst b) (snd b)) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land alpha (Z.lnot mu), mu).

Lemma tnum_sub_easy_eq : forall a b i j,
    gamma a i ->
    gamma b j ->
    tnum_sub_easy a b = tnum_sub' a b.
Proof.
  intros.
  cbv beta delta [tnum_sub_easy tnum_sub'].
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

Lemma sub_borrow_bit_zero : forall n x,
sub_borrow_bit x 0 false n = false.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. intros.  rewrite IHn.
    bits. btauto.
Qed.

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

(**prove the tnum_sub_eq firstly *)


Definition tnum_sub (a b: tnum): tnum :=
  let dv    :=  (fst a) - (fst b) in
  let alpha :=  dv + (snd a) in
  let beta  := dv - (snd b) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land dv (Z.lnot mu), mu).


Lemma add_carry_bit_and_not_false: forall n mb j,
    add_carry_bit (Z.land j (Z.lnot mb)) mb false n = false.
Proof.
  induction n; intros.
  - simpl; auto.
  - simpl.
    rewrite IHn.
    rewrite andb_false_l.
    rewrite orb_false_r.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite <- andb_assoc.
    rewrite andb_negb_l.
    rewrite andb_false_r.
    auto.
Qed.

Lemma Ztestbit_and_not_false: forall mb n j
  (HN: n >= 0)
  (Hmb : Z.testbit mb n = false),
    Z.testbit (Z.land j (Z.lnot mb) + mb) n = Z.testbit j n.
Proof.
  intros.
  replace n with (Z.of_nat (Z.to_nat n)) in *.
  2:{ apply Z2Nat.id; lia. }
  rewrite testbit_add_sound.
  rewrite! Z.land_spec.
  rewrite! Z.lnot_spec by lia.
  rewrite Hmb.
  simpl.
  rewrite add_carry_bit_and_not_false.
  destruct (Z.testbit j (Z.of_nat (Z.to_nat n))); auto.
Qed.

Lemma Ztestbit_and_not_true: forall mb n j
  (HN: n >= 0)
  (Hmb : Z.testbit mb n = true),
    Z.testbit (Z.land j (Z.lnot mb) + mb) n = true.
Proof.
  intros.
  replace n with (Z.of_nat (Z.to_nat n)) in *.
  2:{ apply Z2Nat.id; lia. }
  rewrite testbit_add_sound.
  rewrite! Z.land_spec.
  rewrite! Z.lnot_spec by lia.
  rewrite Hmb.
  simpl.
  rewrite add_carry_bit_and_not_false.
  destruct (Z.testbit j (Z.of_nat (Z.to_nat n))); auto.
Qed.

Lemma Zand_not_or: forall a b,
  (Z.land a (Z.lnot b)) + b = Z.lor a b.
Proof.
  intros.
  apply Z.bits_inj.
  unfold Z.eqf.
  intro n.
  assert (N : n < 0 \/ n >= 0) by lia.
  destruct N as [HN | HN].
  - destruct n; try lia; simpl.
    reflexivity.
  - rewrite! Z.lor_spec.
    destruct (Z.testbit b n) eqn: Hb.
    + rewrite Ztestbit_and_not_true; try assumption.
      rewrite orb_true_r.
      auto.
    + rewrite Ztestbit_and_not_false; try assumption.
      rewrite orb_false_r.
      auto.
Qed.

Lemma sub_borrow_bit_and_not_true: forall n i ma j mb,  
sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false n = true ->
sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.land j (Z.lnot mb)) false n = true.
Proof.
  induction n; simpl; intros.
  - inversion H.
  - rewrite! Z.lor_spec in *.
    rewrite! Z.land_spec in *.
    rewrite! Z.lnot_spec in * by lia.
    destruct (Z.testbit i (Z.of_nat n)) eqn: Hi; simpl in *.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          2:{ auto. }
          rewrite andb_false_r in *.
          inversion H.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - rewrite andb_false_r in *.
            inversion H.
          - rewrite andb_true_r in *.
            apply IHn; auto.
        }
      * rewrite andb_false_r in *.
        inversion H.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          2:{ auto. }
          rewrite andb_false_r in *.
          inversion H.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - rewrite andb_true_r in *.
            apply IHn; auto.
          - auto.
        }
      * rewrite andb_false_r in *. 
        destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        { rewrite andb_false_r in *.
          inversion H.
        }
        { rewrite andb_true_r in *.
          apply IHn; auto.
        }
Qed.

Lemma sub_borrow_bit_true: forall n ma mb i j
  (Hma : Z.testbit ma (Z.of_nat n) = false)
  (Hmb : Z.testbit mb (Z.of_nat n) = false)
  (Hkma : sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false n = true)
  (Hkmb : sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false n = true),
    sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.land j (Z.lnot mb)) false n = true.
Proof.
  induction n; intros.
  - simpl in *.
    inversion Hkma.
  - clear Hma Hmb.
    simpl in *.
    rewrite! Z.land_spec in *.
    rewrite! Z.lnot_spec in * by lia.
    rewrite! Z.lor_spec in *.
    destruct (Z.testbit i (Z.of_nat n)) eqn: Hi; simpl in *.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          2:{ auto. }
          rewrite andb_false_r in *.
          inversion Hkma.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - rewrite andb_false_r in *.
            inversion Hkma.
          - rewrite andb_true_r in *.
            apply IHn; auto.
        }
      * rewrite andb_false_r in *.
        inversion Hkma.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          2:{ auto. }
          rewrite andb_false_r in *.
          inversion Hkma.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          2:{ auto. }
          rewrite andb_true_r in *.
          clear Hkmb IHn.
          apply sub_borrow_bit_and_not_true; auto.
        }
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          rewrite andb_false_r in *.
          inversion Hkma.
        }
        { rewrite andb_true_r in *.
          apply sub_borrow_bit_and_not_true; auto. 
        }
Qed.


Lemma sub_borrow_bit_and_not_false: forall n i ma j mb,  
sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false n = false ->
sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.land j (Z.lnot mb)) false n = false.
Proof.
  induction n; simpl; intros.
  - auto.
  - rewrite! Z.lor_spec in *.
    rewrite! Z.land_spec in *.
    rewrite! Z.lnot_spec in * by lia.
    destruct (Z.testbit i (Z.of_nat n)) eqn: Hi; simpl in *.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        { inversion H. }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - rewrite andb_false_r in *.
            auto.
          - rewrite andb_true_r in *.
            apply IHn; auto.
        }
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        { destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - inversion H.
          - rewrite andb_true_r in *.
            apply IHn; auto.
        }
        rewrite andb_false_r in *.
        auto.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * inversion H.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - inversion H.
          - rewrite andb_true_r in *.
            apply IHn; auto.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - inversion H.
          - rewrite andb_true_r in *.
            apply IHn; auto.
        }
Qed.

Lemma sub_borrow_bit_false: forall n ma mb i j
  (Hma : Z.testbit ma (Z.of_nat n) = false)
  (Hmb : Z.testbit mb (Z.of_nat n) = false)
  (Hkma : sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false n = false)
  (Hkmb : sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false n = false),
    sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.land j (Z.lnot mb)) false n = false.
Proof.
  induction n; intros.
  - simpl in *.
    auto.
  - clear Hma Hmb.
    simpl in *.
    rewrite! Z.land_spec in *.
    rewrite! Z.lnot_spec in * by lia.
    rewrite! Z.lor_spec in *.
    destruct (Z.testbit i (Z.of_nat n)) eqn: Hi; simpl in *.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          inversion Hkmb.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - rewrite andb_false_r in *.
            auto.
          - rewrite andb_true_r in *.
            apply sub_borrow_bit_and_not_false; auto.
        }
      * rewrite andb_false_r in *.
        destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - inversion Hkmb.
          - rewrite andb_true_r in *.
            apply sub_borrow_bit_and_not_false; auto.
        }
        rewrite andb_false_r in *.
        auto.
    + destruct (Z.testbit j (Z.of_nat n)) eqn: Hj; simpl in *.
      * inversion Hkmb.
      * destruct (Z.testbit ma (Z.of_nat n)) eqn: Hma; simpl in *.
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - inversion Hkmb.
          - rewrite andb_true_r in *.
            apply sub_borrow_bit_and_not_false; auto.
        }
        {
          destruct (Z.testbit mb (Z.of_nat n)) eqn: Hmb; simpl in *.
          - inversion Hkmb.
          - rewrite andb_true_r in *.
            apply sub_borrow_bit_and_not_false; auto.
        }
Qed.  


Lemma tnum_sub_eq: forall va ma vb mb i j,
  gamma (va, ma) i ->
  gamma (vb, mb) j ->
  tnum_sub_easy (va, ma) (vb, mb) = tnum_sub (va, ma) (vb, mb).
Proof.
  intros va ma vb mb i j Hgi Hgj.
  cbv beta delta [tnum_sub_easy tnum_sub].
  cbv zeta.
  f_equal.
  apply Z.bits_inj.
  unfold Z.eqf.
  intro n.
  rewrite! Z.land_spec.
  assert (Hgi1 := Hgi).
  assert (Hgj1 := Hgj).
  unfold gamma in Hgi, Hgj.
  simpl in *.
  assert (N : n < 0 \/ n >= 0) by lia.
  destruct N as [HN | HN].
  - destruct n; try lia; simpl.
    reflexivity.
  - rewrite! Z.lnot_spec by lia.
    rewrite! Z.lor_spec.
    rewrite! Z.lxor_spec.
    simpl.
    remember (va - vb) as K eqn: HK.
    destruct (Z.testbit ma n) eqn: Hma.
    + rewrite orb_true_r.
      unfold negb.
      rewrite ! andb_false_r.
      auto.
    + rewrite ! orb_false_l.
      destruct (Z.testbit mb n) eqn: Hmb; simpl.
      * rewrite ! orb_true_r.
        unfold negb.
        rewrite ! andb_false_r.
        auto.
      * rewrite ! orb_false_r.
        destruct (Z.testbit (K + ma) n) eqn: Hkma; simpl.
        {
          destruct (Z.testbit (K - mb) n) eqn: Hkmb; simpl.
          2:{ rewrite andb_false_r. auto. }
          symmetry.
          rewrite andb_true_r.
          rewrite HK in *.
          replace (va - vb + ma) with ((va + ma) - vb) in * by lia.
          replace (va - vb - mb) with (va - (vb + mb)) in * by lia.
          rewrite Ztestbit_sub_sound in * by lia.
          rewrite <- Hgi in HK, Hkma, Hkmb.
          rewrite <- Hgj in HK, Hkma, Hkmb.
          rewrite <- Hgi.
          rewrite <- Hgj.
          rewrite! Z.land_spec in *.
          rewrite! Z.lnot_spec in * by lia.
          rewrite Hma, Hmb in *.
          simpl in *.
          rewrite ! andb_true_r in *.
          destruct (Z.testbit i n) eqn: Hi; simpl in *.
          - rewrite Ztestbit_and_not_false in *; try assumption.
            rewrite Hi in *.
            simpl in *.
            rewrite ! Zand_not_or in *.
            destruct (Z.testbit j n) eqn: Hj; simpl in *.
            + apply sub_borrow_bit_true; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
            + destruct (sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false (Z.to_nat n)) eqn: Hsub1; [inversion Hkma| clear Hkma; rename Hsub1 into Hkma].
              destruct (sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false (Z.to_nat n)) eqn: Hsub1; [inversion Hkmb| clear Hkmb; rename Hsub1 into Hkmb].
              rewrite sub_borrow_bit_false; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
          - rewrite Ztestbit_and_not_false in *; try assumption.
            rewrite Hi in *.
            simpl in *.
            rewrite ! Zand_not_or in *.
            destruct (Z.testbit j n) eqn: Hj; simpl in *.
            + destruct (sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false (Z.to_nat n)) eqn: Hsub1; [inversion Hkma| clear Hkma; rename Hsub1 into Hkma].
              destruct (sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false (Z.to_nat n)) eqn: Hsub1; [inversion Hkmb| clear Hkmb; rename Hsub1 into Hkmb].
              rewrite sub_borrow_bit_false; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
            + apply sub_borrow_bit_true; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
        }
        
        {
          destruct (Z.testbit (K - mb) n) eqn: Hkmb; simpl.
          { rewrite andb_false_r. auto. }
          symmetry.
          rewrite andb_true_r.
          rewrite HK in *.
          replace (va - vb + ma) with ((va + ma) - vb) in * by lia.
          replace (va - vb - mb) with (va - (vb + mb)) in * by lia.
          rewrite Ztestbit_sub_sound in * by lia.
          rewrite <- Hgi in HK, Hkma, Hkmb.
          rewrite <- Hgj in HK, Hkma, Hkmb.
          rewrite <- Hgi.
          rewrite <- Hgj.
          rewrite! Z.land_spec in *.
          rewrite! Z.lnot_spec in * by lia.
          rewrite Hma, Hmb in *.
          simpl in *.
          rewrite ! andb_true_r in *.
          destruct (Z.testbit i n) eqn: Hi; simpl in *.
          - rewrite Ztestbit_and_not_false in *; try assumption.
            rewrite Hi in *.
            simpl in *.
            rewrite ! Zand_not_or in *.
            destruct (Z.testbit j n) eqn: Hj; simpl in *.
            + apply sub_borrow_bit_false; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
            + destruct (sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false (Z.to_nat n)) eqn: Hsub1; [clear Hkma; rename Hsub1 into Hkma | inversion Hkma].
              destruct (sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false (Z.to_nat n)) eqn: Hsub1; [clear Hkmb; rename Hsub1 into Hkmb | inversion Hkmb].
              rewrite sub_borrow_bit_true; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
          - rewrite Ztestbit_and_not_false in *; try assumption.
            rewrite Hi in *.
            simpl in *.
            rewrite ! Zand_not_or in *.
            destruct (Z.testbit j n) eqn: Hj; simpl in *.
            + destruct (sub_borrow_bit (Z.lor i ma) (Z.land j (Z.lnot mb)) false (Z.to_nat n)) eqn: Hsub1; [clear Hkma; rename Hsub1 into Hkma | inversion Hkma].
              destruct (sub_borrow_bit (Z.land i (Z.lnot ma)) (Z.lor j mb) false (Z.to_nat n)) eqn: Hsub1; [clear Hkmb; rename Hsub1 into Hkmb | inversion Hkmb].
              rewrite sub_borrow_bit_true; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
            + apply sub_borrow_bit_false; auto.
              all: rewrite Z2Nat.id; try lia; try auto.
        }
Qed.

(**r now prove the tnum_sub_sound *)

Lemma tnum_sub_sound : forall a b i j,
    gamma a i ->
    gamma b j ->
    gamma (tnum_sub a b) (i-j).
Proof.
  destruct a as (va,ma).
  destruct b as (vb,mb).
  intros i j Hgi Hgj.
  rewrite <- tnum_sub_eq with (i:=i) (j:=j) by assumption.
  rewrite tnum_sub_easy_eq with (i:=i) (j:=j) by assumption.
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

Definition Z_size (x: Z) : nat :=
  match x with
  | Zpos p => Pos.to_nat (Pos.size p)
  | _ => 0
  end.

Definition tnum_num_bits (a: tnum): nat :=
  Nat.max (Z_size (fst a)) (Z_size (snd a)).

Fixpoint tnum_mul_rec (fuel: nat) (a b: tnum): tnum :=
  match fuel with
  | O => (0, 0)
  | S n =>
    let c1 := Z.eqb (Z.land (fst a) 1) 1 in
    let c2 := Z.eqb (Z.land (snd a) 1) 1 in
    let acc_m := tnum_mul_rec n (tnum_rshift a 1) (tnum_lshift b 1) in
      if c1 then tnum_add acc_m (0, snd b) else
      if c2 then tnum_add acc_m (0, Z.lor (fst b) (snd b)) else acc_m
  end.

Definition tnum_mul (a b: tnum): tnum :=
  let n := tnum_num_bits a in
  let acc_v := (Z.mul (fst a) (fst b), 0) in
  let acc_m := tnum_mul_rec n a b in
    tnum_add acc_v acc_m.

Fixpoint tnum_mul_simple_rec (fuel: nat) (a b: tnum): tnum * tnum :=
  match fuel with
  | O => ((0, 0), (0, 0))
  | S n =>
    let c1 := Z.eqb (Z.land (fst a) 1) 1 in
    let c2 := Z.eqb (Z.land (snd a) 1) 1 in
    let (acc_v, acc_m) :=
      tnum_mul_simple_rec n (tnum_rshift a 1) (tnum_lshift b 1) in
      if c1 then
      (tnum_add acc_v (fst b, 0), tnum_add acc_m (0, snd b))
      else
        (acc_v, if c2 then
            tnum_add acc_m (0, Z.lor (fst b) (snd b))
          else
            acc_m)
  end.

Definition tnum_mul_simple (a b: tnum): tnum :=
  let n := tnum_num_bits a in
  let (acc_v, acc_m) := tnum_mul_simple_rec n a b in
    tnum_add acc_v acc_m.

(*
Lemma tnum_mul_simple_rec_eq: forall n a b,
  tnum_add (fst a * fst b, 0) (tnum_mul_rec n a b) =
    (let (acc_v, acc_m) := tnum_mul_simple_rec n a b in tnum_add acc_v acc_m).
Proof.
  induction n; simpl; intros.
  - unfold tnum_add; simpl.
    rewrite ! Z.add_0_r.
    rewrite Z.lor_0_r.
    rewrite Z.lxor_nilpotent.
    rewrite Z.lnot_0.
    generalize (fst a * fst b) as n.
    intros.
    unfold Z.land.
    destruct n; try lia; try auto.
    simpl.
    Search (Z.land (-1) _).

Lemma tnum_mul_simple_eq: forall a b,
  tnum_mul a b = tnum_mul_simple a b.
Proof.
  unfold tnum_mul, tnum_mul_simple; intros.
  generalize (tnum_num_bits a) as n.
  revert a b.
  induction n.
Qed. *)
(*    

Compute (tnum_mul (1, 4) (2, 4)).
Compute (tnum_mul (2, 4) (1, 4)).
Compute (tnum_mul_simple (1, 4) (2, 4)).
Compute (tnum_mul_simple (2, 4) (1, 4)).

Fixpoint tnum_mul_rec (fuel: nat) (a b acc_v acc_m: tnum): tnum * tnum :=
  match fuel with
  | O => (acc_v, acc_m)
  | S n =>
    let c1 := Z.eqb (Z.land (fst a) 1) 1 in
    let c2 := Z.eqb (Z.land (snd a) 1) 1 in
      tnum_mul_rec n
        (tnum_rshift a 1)
        (tnum_lshift b 1)
        (if c1 then tnum_add acc_v (fst b, 0) else acc_v)
        (if c1 then tnum_add acc_m (0, snd b) else
         if c2 then tnum_add acc_m (0, Z.lor (fst b) (snd b)) else acc_m)
  end.

Definition tnum_mul (a b: tnum): tnum :=
  let n := Nat.max (tnum_num_bits a) (tnum_num_bits b) in
  let (acc_v, acc_m) := tnum_mul_rec n a b (0, 0) (0, 0) in
    tnum_add acc_v acc_m.*)

Fixpoint zmul_bits_pos (a b: Z) (n: nat): Z :=
  match n with
  | O => 0
  | S k => let p := Z.mul (Z.land a 1) b in
    p + (zmul_bits_pos (Z.shiftr a 1) (b*2) k) (* Z.shiftl b 1 *)
  end.

Definition zmul_bits (a b: Z): Z :=
  match a with
  | Zpos p => zmul_bits_pos (Zpos p) b (Z_size (Zpos p))
  | Zneg n => Z.opp (zmul_bits_pos (Zpos n) b (Z_size (Zpos n)))
  | Z0 => Z0
  end.

Lemma zmul_bits_pos_0: forall n b,
  zmul_bits_pos 0 b n = 0.
Proof.
  induction n; simpl; intros.
  - auto.
  - rewrite Z.shiftr_0_l.
    rewrite IHn.
    auto.
Qed.

Lemma pos_size_shiftr_ge: forall m n p p1
  (HN : (Pos.to_nat (Pos.size p) <= m + n)%nat)
  (HC : Z.shiftr (Z.pos p) (Z.of_nat m) = Z.pos p1),
    (Pos.to_nat (Pos.size p1) <= n)%nat.
Proof.
  unfold Z.shiftr.
  induction m; simpl; intros.
  - injection HC as Heq.
    subst p.
    auto.
  - destruct p as [px | po | ]; simpl in *.
    + eapply IHm with (p := px); eauto.
      lia.
      unfold Z.shiftl.
      destruct m; try auto; try lia.
      simpl.
      replace (Pos.of_succ_nat (S m)) with (Pos.succ (Pos.of_succ_nat m)) in HC by lia.
      rewrite Pos.iter_succ_r in HC.
      simpl in HC.
      auto.
    + eapply IHm with (p := po); eauto.
      lia.
      unfold Z.shiftl.
      destruct m; try auto; try lia.
      simpl.
      replace (Pos.of_succ_nat (S m)) with (Pos.succ (Pos.of_succ_nat m)) in HC by lia.
      rewrite Pos.iter_succ_r in HC.
      simpl in HC.
      auto.
    + destruct m; simpl in *; try auto; try lia. 
      rewrite Pos.iter_succ_r in HC.
      replace (Z.div2 1) with 0 in HC by lia.
      assert (Heq: forall k, Pos.iter Z.div2 0 k = 0).
      {
        clear.
        induction k; simpl in *; intros; try auto.
        - rewrite ! IHk.
          lia.
        - rewrite ! IHk.
          lia.
      }
      rewrite Heq in HC.
      inversion HC.
Qed.

Lemma Zmul_bits_pos_eq: forall n a b p
  (HP: a = Zpos p)
  (HN: (Z_size a <= n)%nat),
    a * b = zmul_bits_pos a b n.
Proof.
  induction n; unfold Z_size; simpl; intros; subst.
  - pose proof (Pos2Nat.is_pos p) as HP.
    lia.
  - remember (Z.shiftr (Z.pos p) 1) as hp1 eqn: HP1.
    pose proof (Z.shiftr_nonneg (Z.pos p) 1) as Ht.
    assert (HG: 0 <= hp1) by lia.
    clear Ht.
    assert (HC: hp1 = 0 \/ exists p1, hp1 = Zpos p1).
    { destruct hp1.
      - auto.
      - right.
        exists p0.
        auto.
      - lia.
    }
    destruct HC as [HC | HC].
    {
      rewrite HC.
      rewrite zmul_bits_pos_0.
      rewrite Z.add_0_r.
      assert (HB: b <> 0 \/ b = 0) by lia.
      destruct HB as [HB | HB].
      - rewrite Z.mul_cancel_r by lia.
        subst hp1.
        rewrite <- Z.div2_spec in HC.
        destruct p; try auto; try lia.
      - lia.
    }
    destruct HC as (p1 & HC).
    rewrite <- IHn with (p := p1); auto.
    2:{
      unfold Z_size.
      subst.
      rewrite HC.
      clear - HN HC.
      eapply pos_size_shiftr_ge with (p := p) (m := 1%nat); eauto.
    }
    assert (HB: b <> 0 \/ b = 0) by lia.
    destruct HB as [HB | HB]. 2:{ subst b. lia. }
    assert (Heq: Z.pos p = Z.land (Z.pos p) 1 + hp1*2).
    { 
      clear IHn.
      subst hp1.
      replace 2 with (2^1) by lia.
      rewrite <- Z.shiftl_mul_pow2 by lia.
      destruct p; try auto; try lia.
    }
    rewrite Heq at 1.
    rewrite Z.mul_add_distr_r.
    lia.
Qed.

Lemma Zmul_bits_eq: forall a b,
    a * b = zmul_bits a b.
Proof.
  unfold zmul_bits.
  intros.
  destruct a as [| ap | an].
  - auto.
  - eapply Zmul_bits_pos_eq; eauto.
  - erewrite <- Zmul_bits_pos_eq; eauto.
    lia.
Qed.

(*
Lemma gamma_size_eq: forall va ma i
  (Hgi : gamma (va, ma) i),
  tnum_num_bits (va, ma) = Z_size i.
Proof.
  unfold gamma, tnum_num_bits, Z_size; simpl; intros.
  subst.
  destruct i.
  - rewrite Z.land_0_l.
  
  Search (Z.land 0 _).
  unfold Nat.max.
Qed.  *)


(**r Lemma 8 *)
Lemma tnum_set_union_with_zero: forall va ma i
  (Hgi: gamma (va, ma) i),
  gamma (0, Z.lor va ma) i /\ gamma (0, Z.lor va ma) 0.
Proof.
  unfold gamma; simpl; intros.
  split; [| auto].
  subst.
  apply Z.bits_inj.
  unfold Z.eqf.
  intros n.
  rewrite! Z.land_spec.
  assert (N : n < 0 \/ n >= 0) by lia.
  destruct N as [HN | HN].
  - destruct n; try lia; simpl.
    reflexivity.
  - rewrite! Z.lnot_spec by lia.
    rewrite! Z.lor_spec.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite Z.bits_0.
    destruct (Z.testbit i n); try auto.
    simpl.
    destruct (Z.testbit ma n); try auto.
Qed.

(**r Lemma 9 *)
../..

Lemma value_mask_decompose_tnum_sum: forall n va ma vb mb i j acc_v acc_m
  (Hgi: gamma (va, ma) i)
  (Hgj: gamma (vb, mb) j)
  (Hacc: tnum_mul_simple_rec n (va, ma) (vb, mb) = (acc_v, acc_m)),
    gamma (tnum_add acc_v acc_m) (zmul_bits_pos i j n).
(*
Lemma tnum_mul_simple_rec_0: forall n ma vb mb v m
  (HM: tnum_mul_simple_rec n (0, ma) (vb, mb) = (v, m)),
    fst (tnum_add v m) = 0.
Proof.
  induction n; intros.
  - simpl in HM. inversion HM.
    clear; simpl.
    auto.
  - simpl in HM.
    unfold tnum_rshift, tnum_lshift in HM.
    unfold fst, snd in HM.
    replace (Z.shiftr 0 1) with 0 in HM.
    2:{ rewrite Z.shiftr_0_l. auto. }
    remember (tnum_mul_simple_rec n (0, Z.shiftr ma 1) (Z.shiftl vb 1, Z.shiftl mb 1)) as a eqn: HA.
    destruct a as (acc_v, acc_m).
    symmetry in HA.
    specialize (IHn _ _ _ _ _ HA).
    destruct (Z.land ma 1 =? 1) eqn: Hma1;
      injection HM as HV HM;subst v m; [| auto].
    unfold tnum_add in *; simpl in IHn; simpl.
    rewrite ! Z.add_0_r. *)

Lemma tnum_mul_simple_sound : forall a b i j,
  gamma a i ->
  gamma b j ->
    gamma (tnum_mul_simple a b) (i*j).
Proof.
  destruct a as (va,ma).
  destruct b as (vb,mb).
  intros i j Hgi Hgj.
  unfold gamma, tnum_mul_simple; simpl.
  remember (tnum_num_bits (va, ma)) as k eqn: HK.
  remember (tnum_mul_simple_rec k (va, ma) (vb, mb)) as acc eqn: HM.
  destruct acc as (acc_v, acc_m).
  rewrite ! Zmul_bits_eq.
  unfold zmul_bits.
  destruct i.
  - unfold gamma in Hgi.
    rewrite Z.land_0_l in *.
    simpl in Hgi.
    subst va.

  apply Z.bits_inj.
  unfold Z.eqf.
  intros n.
  rewrite! Z.land_spec.
  assert (N : n < 0 \/ n >= 0) by lia.
  destruct N as [HN | HN].
  - destruct n; try lia; simpl.
    reflexivity.
  - remember (tnum_num_bits (va, ma)) as k eqn: HK.
    remember (tnum_mul_rec k (va, ma) (vb, mb)) as acc_m eqn: HM.
    unfold tnum_num_bits in HK.
    simpl in *.
    rewrite! Z.lnot_spec by lia.
    rewrite! Z.lor_spec.
    rewrite! Z.lxor_spec.
    replace (snd acc_m + (va * vb + fst acc_m)) with
    ((va * vb) + (snd acc_m + fst acc_m)) by lia.
    rewrite! Ztestbit_add_sound by lia.
(*
Definition tnum_is_const (a: tnum): bool := Z.eqb (snd a) 0.
  
Fixpoint tnum_karatsuba_mul_aux (fuel n: nat) (x y: tnum): tnum :=
  match fuel with
  | O => ((fst x) * (fst y), 0)
  | S fuel' =>
    if (tnum_is_const x) && (tnum_is_const y) then
      ((fst x) * (fst y), 0)
    else
    let m := Z.of_nat (Nat.div n 2) in

    (*decompose: x = a * 2^m + b, y = c * 2^m + d *)
    let a := tnum_rshift x m in
    let b := tnum_sub x (tnum_lshift a m) in
    let c := tnum_rshift y m in
    let d := tnum_sub y (tnum_lshift c m) in

    (*compute: 3 sub karatsuba_mul *)
    let ac := tnum_karatsuba_mul_aux fuel' (Nat.div n 2) a c in
    let bd := tnum_karatsuba_mul_aux fuel' (Nat.div n 2) b d in
    let ab_cd := tnum_karatsuba_mul_aux fuel' ((Nat.div n 2)+1) (tnum_add a b) (tnum_add c d) in

    (*compute: ad + bc = (a+b)(c+d) - ac - bd *)
    let ad_plus_bc := tnum_sub (tnum_sub ab_cd ac) bd in

    (*merge result: ac * 2^{2m} + (ad+bc) * 2^m + bd *)
      tnum_add (tnum_add (tnum_lshift ac (2 * m)) (tnum_lshift ad_plus_bc m)) bd
  end.

Definition tnum_karatsuba_mul (x y: tnum): tnum := 
  let n := Nat.max (tnum_num_bits x) (tnum_num_bits y) in
    tnum_karatsuba_mul_aux n n x y.

Compute (tnum_karatsuba_mul (2, 4) (1,4)).
Compute (Nat.max (tnum_num_bits (2, 4)) (tnum_num_bits (1,4))).
Compute (Nat.div 3 2).*)