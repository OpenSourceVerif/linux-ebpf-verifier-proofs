From Coq Require Import ZArith Bool Lia Btauto.
From bpf.src Require Import Zmore tnumZ tnumZ_add_sound tnumZ_not_sound.

Definition tnum_sub_easy (a b: tnum): tnum :=
  let dv    :=  (fst a) - (fst b) in
  let alpha :=  dv + (snd a) in
  let beta  := dv - (snd b) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land alpha (Z.lnot mu), mu).


(** substraction: tnum_sub' is better than tnum_sub_easy, w.r.t. proof *)
Definition tnum_sub' (a b: tnum): tnum :=
  let dv    :=  (fst a) - (fst b) in
  let alpha :=  (Z.lor (fst a) (snd a)) - fst b in
  let beta  :=  (fst a) - (Z.lor (fst b) (snd b)) in
  let chi   := Z.lxor alpha beta in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land alpha (Z.lnot mu), mu).

(* x - y = x + ( - y) = x + not (x + -1) *)
Definition tnum_sub_by_add_not_pred (a b:tnum) :=
  tnum_add a (tnum_not (tnum_pred b)).

(* x - y = not (not x + y) *)
Definition tnum_sub_by_not_not_add (a b:tnum) :=
  tnum_not (tnum_add (tnum_not a) b).

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

Lemma gamma_testbit_mask_false_Z:
  forall va ma i x
  (Hg: gamma (va, ma) i)
  (Hor_ma : Z.testbit ma x = false),
  0 <= x -> Z.testbit va x = Z.testbit i x.
Proof.
  intros.
  unfold gamma in *; simpl in *; subst.
  rewrite ! Z.land_spec.
  rewrite ! Z.lnot_spec by lia.
  rewrite Hor_ma.
  btauto.
Qed.

(**prove the tnum_sub_eq firstly *)

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



Lemma sub_borrow_bit_and_not_false_false: forall n i am,
    sub_borrow_bit i (Z.land i (Z.lnot am)) false n = false.
Proof.
  induction n; intros; simpl; auto.
  rewrite IHn; try lia.
  rewrite! Z.land_spec.
  rewrite! Z.lnot_spec by lia.
  destruct (Z.testbit i _); simpl; try lia.
Qed.