From Coq Require Import ZArith Bool Lia Btauto.
Open Scope Z_scope.

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

  
Lemma add_lor_excl : forall x y,
  Z.land x y = 0%Z ->
  (x + y)%Z = Z.lor x y.
Proof.
  intros.
  rewrite <- Z.add_lor_land.
  rewrite H.
  ring.
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

Lemma Z_lor_recompose : forall x y,
  x = Z.lor (Z.land x (Z.lnot y)) (Z.land x y).
Proof.
  intros.
  rewrite <- Z.land_lor_distr_r.
  rewrite Z.lor_comm.
  rewrite Z.lor_lnot_diag.
  symmetry; apply Z.land_m1_r.
Qed.

Lemma Z_land_disjoint : forall x y,
  Z.land (Z.land x (Z.lnot y)) (Z.land x y) = 0.
Proof.
  intros.
  rewrite (Z.land_comm x y).
  rewrite (Z.land_assoc (Z.land x (Z.lnot y)) y x).
  rewrite <- (Z.land_assoc x (Z.lnot y) y).
  rewrite (Z.land_comm (Z.lnot y) y).
  rewrite Z.land_lnot_diag.
  rewrite Z.land_0_r; apply Z.land_0_l.
Qed.

Lemma Z_ldiff_ones n x : 
  0 <= n -> Z.ldiff x (Z.ones n) = 0 <-> (0 <= x <= Z.ones n).
Proof.
  intros. split.
  - apply Z.ldiff_le; rewrite Z.ones_equiv.
    apply Z.lt_le_pred, Z.pow_pos_nonneg. lia. apply H.
  - intros; destruct H0. destruct (Z.eqb_spec x 0).
    + rewrite e. reflexivity.
    + apply Z.ldiff_ones_r_low. lia.
      rewrite Z.ones_equiv in H1; apply Z.lt_le_pred in H1.
      apply Z.log2_lt_pow2. lia. apply H1.
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

Lemma sub_eq : forall x,  - x = Z.lnot (x + -1).
Proof.
  intros.
  replace (x + (-1)) with (x -1) by lia.
  rewrite Z.lnot_pred. reflexivity.
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


Lemma sub_not_not_add : forall x y, x - y = Z.lnot ((Z.lnot x) + y).
  Proof.
    intros.
    rewrite <- (Z.lnot_involutive (x - y)).
    rewrite Z.lnot_sub.
    f_equal.
  Qed.

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

Lemma pos_land_le: forall p p0,
  Z.of_N (Pos.land p p0) <= Z.pos p.
Proof.
  induction p; simpl; intros; try lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
Qed.

Lemma pos_pred_n_diff_le: forall p p0,
    Z.of_N (Pos.ldiff p p0) <= Z.pos p.
Proof.
  induction p; simpl; intros; try lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
Qed.

Lemma Z_land_leb: forall i j,
  0 <= i ->
  Z.land i j <= i.
Proof.
  unfold Z.land.
  destruct i; simpl; intros; try lia.
  destruct j; try lia.
  - apply pos_land_le.
  - destruct (Pos.pred_N p0) eqn: Hp0; try lia.
    apply pos_pred_n_diff_le.
Qed.

Lemma Z_land_leb_r: forall i j,
  0 <= j ->
  Z.land i j <= j.
Proof.
  intros.
  rewrite Z.land_comm.
  apply (Z_land_leb _ _ H).
Qed.

Lemma Z_land_1_eq: forall i,
  Z.land i 1 = 0 \/ Z.land i 1 = 1.
Proof.
  intros.
  assert (Heq: 0 <= 1) by lia.
  eapply Z_land_leb with (j := i) in Heq as Hg; eauto.

  assert (Hor: 0 <= 1 \/ 0 <= i) by lia.
  rewrite <- Z.land_nonneg in Hor.
  rewrite Z.land_comm.
  lia.
Qed.

Lemma Z_bits_decomp : forall x k,
  0 <= x -> 0 <= k -> x = Z.land x (Z.ones k) + Z.shiftl (Z.shiftr x k) k.
Proof.
  intros.
  rewrite Z.land_ones; try lia.
  rewrite Z.shiftl_mul_pow2; try lia.
  rewrite Z.shiftr_div_pow2; try lia.
Qed.

Lemma Z_shiftr_ones : forall x y,
  0 <= x -> 0 <= y -> Z.shiftr (Z.ones (x + y)) y = Z.ones x.
Proof.
  intros. rewrite Z.shiftr_div_pow2; try lia.
  rewrite !Z.ones_equiv. rewrite <- !Z.sub_1_r.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.mul_comm.
  rewrite <- (Z.div_unique (2 ^ y * 2 ^ x - 1) (2 ^ y) (2 ^ x - 1) (2 ^ y - 1)); try lia.
Qed.