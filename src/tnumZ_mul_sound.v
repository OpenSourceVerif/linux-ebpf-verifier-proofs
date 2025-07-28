From Coq Require Import List ZArith Lia.
From bpf.src Require Import Zmore tnumZ tnumZ_inv tnumZ_add_sound tnumZ_sub_sound tnumZ_shift_sound.
Import ListNotations.

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

Fixpoint partial_product (n: nat) (x y: Z): list Z :=
  match n with
  | O => []
  | S n1 =>
    ((Z.land x 1) * y) ::
  partial_product n1 (Z.shiftr x 1) (Z.shiftl y 1)
end.

Lemma partial_product_Sn: forall n x y,
  partial_product (S n) x y =
  ((Z.land x 1) * y) ::
  partial_product n (Z.shiftr x 1) (Z.shiftl y 1).
Proof.
  simpl; auto.
Qed.

Lemma partial_product_0: forall n k y,
  fold_left (fun a b : Z => a + b) (partial_product n 0 k) y = y.
Proof.
  induction n; intros.
  auto.

  assert (Heq: partial_product (S n) 0 k = [0]  ++ partial_product n 0 (Z.shiftl k 1)). {
      simpl.
      auto.
    }
  rewrite Heq.
  rewrite fold_left_app.
  rewrite IHn.
  simpl. lia.
Qed.

Lemma partial_product_mul_eq: forall n d x y p
  (HP: x = Zpos p)
  (HN: (Z_size x <= n)%nat),
  (x * y) + d = (List.fold_left (fun a b => a + b) (partial_product n x y) d).
Proof.
  induction n; unfold Z_size; intros; subst.
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
    assert (Heq: partial_product (S n) (Z.pos p) y = [(Z.land (Z.pos p) 1) * y]  ++ partial_product n (Z.shiftr (Z.pos p) 1) (Z.shiftl y 1)). {
      simpl.
      auto.
    }
    remember (Z.pos p) as k eqn: HK.
    rewrite Heq; clear Heq.
    rewrite fold_left_app.
    subst k.
    destruct HC as [HC | HC].
    { subst hp1.
      assert (Heq: Z.pos p = 1). {
        clear - HC.
        unfold Z.shiftr, Z.shiftl in HC.
        simpl in HC.
        destruct p; try lia.
      }
      rewrite Heq; clear Heq.
      assert (Heq: Z.shiftr 1 1 = 0). {
        unfold Z.shiftr, Z.shiftl; simpl.
        auto.
      }
      rewrite Heq; clear Heq.
      replace (Z.land 1 1) with 1. 2:{
        unfold Z.land; simpl. auto.
      }
      remember (Z.shiftl y 1) as k eqn: HK.
      rewrite Z.mul_1_l.
      simpl.
      rewrite Z.add_comm.
      rewrite partial_product_0.
      auto.
    }
    destruct HC as (p1 & HC).
    rewrite <- IHn with (p := p1); auto.
    2:{ subst. lia. }
    2:{
      unfold Z_size.
      subst.
      rewrite HC.
      clear - HN HC.
      eapply pos_size_shiftr_ge with (p := p) (m := 1%nat); eauto.
    }
    assert (HB: y <> 0 \/ y = 0) by lia.
    destruct HB as [HB | HB]. 2:{ subst y. rewrite ! Z.shiftl_0_l. simpl. lia. }
    assert (Heq: Z.pos p * y = Z.shiftr (Z.pos p) 1 * Z.shiftl y 1 +
      Z.land (Z.pos p) 1 * y).
    { 
      subst.
      clear. unfold Z.shiftr, Z.shiftl. simpl.
      destruct p; destruct y; simpl; auto; lia.
    }
    rewrite Heq at 1.
    simpl; lia.
Qed.

Definition Zpartial_product (a b: Z): Z :=
  match a with
  | Zpos p => let l := partial_product (Z_size (Zpos p)) (Zpos p) b in
      List.fold_left (fun a b => a + b) l 0
  | Zneg n => let l := partial_product (Z_size (Zpos n)) (Zpos n) b in
      Z.opp (List.fold_left (fun a b => a + b) l 0)
  | Z0 => Z0
  end.

(* Observation 7. *)
Lemma partial_product_eq: forall a b,
    a * b = (Zpartial_product a b).
Proof.
  unfold Zpartial_product.
  intros.
  rewrite <- Z.add_0_r with (n := a * b).
  destruct a as [| ap | an].
  - auto.
  - eapply partial_product_mul_eq; eauto.
  - erewrite <- partial_product_mul_eq; eauto.
    lia.
Qed.

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

Definition tnum_add_sum (l: list tnum) (d: tnum): tnum := (**default = (0, 0) *)
  List.fold_left (fun a b => tnum_add a b) l d.

Lemma tnum_add_sum_cons: forall l a d,
  tnum_add_sum (a :: l) d = (tnum_add_sum l (tnum_add a d)).
Proof.
  unfold tnum_add_sum; induction l; simpl; intros.
  - apply tnum_add_comm.
  - rewrite <- IHl.
    simpl.
    rewrite tnum_add_comm.
    rewrite tnum_add_comm with (a := a0).
    auto.
Qed.

Lemma tnum_add_sum_tail: forall l a d,
  tnum_add_sum (l++[a]) d = tnum_add a (tnum_add_sum l d).
Proof.
  unfold tnum_add_sum; induction l as [| t tl]; simpl; intros.
  - apply tnum_add_comm.
  - rewrite <- IHtl.
    auto.
Qed.

Lemma tnum_add_decompose: forall a i
  (Hd : gamma a i),
    gamma (tnum_add (fst a, 0) (0, snd a)) i.
Proof.
  unfold tnum_add, gamma; destruct a as (av, am); simpl; intros.
  rewrite Z.add_0_r.
  subst av.
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
    rewrite! Z.lxor_spec.
    destruct (Z.testbit i n); simpl; try auto.
    destruct (Z.testbit am n); simpl;  try auto.
    unfold negb, xorb, orb.
    destruct (Z.testbit (am + Z.land i (Z.lnot am)) n); simpl; try auto.
    + destruct (Z.testbit (Z.land i (Z.lnot am)) n); simpl; try auto.
    + destruct (Z.testbit (Z.land i (Z.lnot am)) n); simpl; try auto.
Qed.

(**r Eqn.16  T.v is the smallest element in gamma T i *)
Lemma smallest_concrete: forall a i
  (Hi: 0 <= i)
  (Hd: gamma a i),
    (fst a) <= i.
Proof.
  unfold gamma; destruct a as (av, am); simpl; intros.
  rewrite <- Hd.
  apply Z_land_leb; auto.
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

(**r Property P0 (value-mask decomposition of a single tnum). *)
Lemma value_mask_decompose_a_tnum: forall a i
  (Hi: tnum_ge_inv a)
  (Hd: gamma a i),
    exists i1 i2, i = i1+i2 /\
      gamma (fst a, 0) i1 /\
      gamma (0, snd a) i2.
Proof.    
  destruct a as (av, am); simpl; intros.
  exists av, (i-av).
  repeat split.
  - eapply tnum_ge_inv_gamma in Hi; eauto.
    pose proof (smallest_concrete (av, am) i Hi Hd) as Hge.
    lia.
  - unfold gamma in *; simpl in *; subst.
    apply Z.bits_inj.
    unfold Z.eqf.
    intro n.
    assert (N : n < 0 \/ n >= 0) by lia.
    destruct N as [HN | HN]; [destruct n; try lia; simpl; reflexivity | ].
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    destruct (Z.testbit i n); simpl; try lia.
    destruct (Z.testbit am n); simpl; try lia.
    rewrite Z.bits_0; lia.

  - unfold gamma in *; simpl in *; subst.
    apply Z.bits_inj.
    unfold Z.eqf.
    intro n.
    assert (N : n < 0 \/ n >= 0) by lia.
    destruct N as [HN | HN]; [destruct n; try lia; simpl; reflexivity | ].
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite Z.bits_0.
    destruct (Z.testbit am n) eqn: Ham; simpl; try lia.
    rewrite Bool.andb_true_r.
    rewrite Ztestbit_sub_sound; try lia.
    unfold xorb.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite Ham.
    rewrite sub_borrow_bit_and_not_false_false.
    destruct (Z.testbit i n) eqn: Hi1; simpl; try lia.
Qed.

Fixpoint list_eq_z_three (l l1 l2: list Z): bool :=
  match l, l1, l2 with
  | [], [], [] => true
  | a::tl, a1::tl1, a2 :: tl2 =>
    if Z.eqb a (a1 + a2) then
      list_eq_z_three tl tl1 tl2
    else
      false
  | _, _, _ => false
  end.

Lemma list_eq_z_three_tail_if: forall l l1 l2 a a1 a2,
  list_eq_z_three l l1 l2 = true /\ a = a1 + a2 ->
  list_eq_z_three (l++[a]) (l1++[a1]) (l2++[a2]) = true.
Proof.
  induction l; simpl; intros.
  {
    destruct l1; simpl; inversion H.
    - subst.
      destruct l2; simpl; inversion H.
      + rewrite Z.eqb_refl; auto.
      + inversion H0.
    - subst.
      inversion H0.
  }

  destruct l1; simpl; inversion H.
  - subst.
    inversion H0.
  - subst.
    destruct l2; simpl; inversion H.
    + inversion H0.
    + destruct (a =? z + z0); inversion H0.
    rewrite IHl; auto.
Qed.

Lemma list_eq_z_three_tail_only_if: forall l l1 l2 a a1 a2,
  list_eq_z_three (l++[a]) (l1++[a1]) (l2++[a2]) = true ->
    list_eq_z_three l l1 l2 = true /\ a = a1 + a2.
Proof.
  induction l; simpl; intros.
  {
    destruct l1; simpl in *; inversion H.
    - destruct l2; simpl in *; inversion H.
      + destruct (a =? a1 + a2) eqn: Ha; inversion H.
        rewrite Z.eqb_eq in Ha.
        auto.
      + destruct (a =? a1 + z) eqn: Ha; inversion H.
        destruct l2; simpl in *; inversion H.
    - destruct l2; simpl in *; inversion H.
      + destruct (a =? z + a2) eqn: Ha; inversion H.
        destruct l1; simpl in *; inversion H.
      + destruct (a =? z + z0) eqn: Ha; inversion H.
        destruct l1; simpl in *; inversion H.
  }

  destruct l1; simpl in *; inversion H.
  - destruct l2; simpl in *; inversion H.
    + destruct (a =? a1 + a2) eqn: Ha; inversion H.
      destruct l; simpl in *; inversion H.
    + destruct (a =? a1 + z) eqn: Ha; inversion H.
      destruct l; simpl in *; inversion H.
  - destruct l2; simpl in *; inversion H.
    + destruct (a =? z + a2) eqn: Ha; inversion H.
      destruct l; simpl in *; inversion H.
      * destruct l1; simpl in *; inversion H.
      * destruct l1; simpl in *; inversion H.
    + destruct (a =? z + z0) eqn: Ha; inversion H.
      rewrite H.
      apply IHl in H.
      destruct H as (H & Ha0).
      subst.
      split; auto.
Qed.

Lemma list_eq_z_three_tail_iff: forall l l1 l2 a a1 a2,
  list_eq_z_three (l++[a]) (l1++[a1]) (l2++[a2]) = true <->
    list_eq_z_three l l1 l2 = true /\ a = a1 + a2.
Proof.
  split.
  apply list_eq_z_three_tail_only_if.
  apply list_eq_z_three_tail_if.
Qed.

Lemma list_eq_z_three_tail_exist: forall l l1 l2 a,
  list_eq_z_three (l++[a]) l1 l2 = true ->
  exists a1 a2 l3 l4,
    l1 = l3++[a1] /\ l2 = l4++[a2] /\ a = a1+a2.
Proof.
  induction l; simpl; intros.
  {
    destruct l1; simpl; inversion H.
    destruct l2; simpl; inversion H.
    destruct (a =? z + z0) eqn: Ha; inversion H1.
    destruct l1; simpl; inversion H.
    destruct l2; simpl; inversion H.
    rewrite Z.eqb_eq in Ha.
    exists z, z0, [], [].
    simpl; auto.
  }

  destruct l1; simpl; inversion H.
  destruct l2; simpl; inversion H.
  destruct (a =? z + z0) eqn: Ha; inversion H.
  rewrite Z.eqb_eq in Ha.
  apply IHl in H.
  destruct H as (a1 & a2 & l3 & l4 & Heq1 & Heq2 & Heq3).
  exists a1, a2, (z::l3), (z0::l4).
  subst.
  repeat split; auto.
Qed.

Lemma sum_add_split_eq: forall ls l1 l2 di d1 d2
  (Heq: list_eq_z_three ls l1 l2 = true)
  (Hd: di = d1 + d2),
    (List.fold_left (fun a b => a + b) ls di) = 
    (List.fold_left (fun a b => a + b) l1 d1) +
    (List.fold_left (fun a b => a + b) l2 d2).
Proof.
  induction ls; simpl; intros.
  - destruct l1; [| inversion Heq].
    destruct l2; [| inversion Heq].
    simpl.
    lia.
  - destruct l1 as [| a1 tl1]; [inversion Heq|].
    destruct l2 as [| a2 tl2]; [inversion Heq|].
    destruct (a =? a1 + a2) eqn: Ha; [| inversion Heq].
    rewrite Z.eqb_eq in Ha.
    assert (HE: di + a = d1 + a1 + (d2 + a2)) by lia.
    specialize (IHls tl1 tl2 (di + a) (d1+a1) (d2+a2) Heq HE).
    rewrite IHls.
    simpl.
    lia.
Qed.

Lemma list_split_exists: forall l,
  exists l1 l2,
    list_eq_z_three l l1 l2 = true.
Proof.
  induction l; simpl; intros.
  - exists [], [].
    auto.
  - destruct IHl as (tl1 & tl2 & Heq).
    exists (0::tl1), (a:: tl2).
    simpl.
    rewrite Z.eqb_refl.
    auto.
Qed.  

Lemma list_fold_left_z_add_eq: forall l a b,
  fold_left (fun a b : Z => a + b) l (a + b) = a + fold_left (fun a b : Z => a + b) l b.
Proof.
  induction l; simpl; intros.
  auto.
  specialize (IHl a0 (b+a)).
  rewrite Z.add_assoc in IHl.
  auto.
Qed.

Lemma list_Sn_tail: forall {A:Type} (l: list A) n,
  length l = S n ->
    exists ln an1 n1, length ln = n1 /\ l = ln ++ [an1].
Proof.
  induction l; simpl; intros.
  inversion H.

  inversion H.
  destruct n.
  - destruct l; inversion H1.
    exists [], a, 0%nat.
    simpl; auto.
  - apply IHl in H1.
    destruct H1 as (ln1 & a2 & n2 & Hn2_eq & Hl_eq).
    exists (a::ln1), a2, (S n2).
    subst.
    simpl; auto.
Qed.

Lemma fold_left_tail_eq: forall l a b,
  fold_left (fun a b : Z => a + b) (l ++ [a]) (b - a) =
  fold_left (fun a b : Z => a + b) l b.
Proof.
  induction l; simpl; intros.
  lia.
  erewrite <- IHl with (a := a0).
  rewrite Z.add_sub_swap.
  auto.
Qed.


Fixpoint gamma_list (v: list Z) (l: list tnum): Prop :=
  match v, l with
  | [], [] => True
  | va::vtl, a::tl => gamma a va /\ tnum_ge_inv a /\ gamma_list vtl tl
  | _, _ => False
  end.

Lemma gamma_list_imply: forall l
  (Hg: forall a i, List.In (a,i) l -> gamma a i /\ tnum_ge_inv a),
    gamma_list (List.map snd l) (List.map fst l).
Proof.
  induction l; simpl; intros.
  auto.

  assert (Heq: a = (fst a, snd a) \/ In (fst a, snd a) l).
  { left.
    destruct a; auto.
  }
  specialize (Hg (fst a) (snd a) Heq) as HK; clear Heq.
  destruct HK as (HK & Hs).
  unfold tnum_ge_inv in Hs.
  repeat split; auto; lia.
Qed.

Lemma gamma_list_app: forall l1 l2 l3 l4,
  gamma_list l1 l2 ->
  gamma_list l3 l4 ->
    gamma_list (l1 ++ l3) (l2 ++ l4).
Proof.
  induction l1; simpl; intros.
  - destruct l2; inversion H.
    simpl.
    auto.
  - destruct l2 as [| a2 tl2]; [ inversion H|].
    destruct H as (Ha2 & Hc & Htl2).
    simpl.
    split; auto. 
Qed.

Lemma gamma_list_tail_if: forall l1 l2 a b,
  gamma_list l1 l2 /\ gamma b a /\ tnum_ge_inv b ->
    gamma_list (l1 ++ [a]) (l2 ++ [b]).
Proof.
  induction l1; simpl; unfold tnum_ge_inv; intros.
  - destruct l2; simpl; inversion H.
    + intuition.
    + destruct H as (H & _); inversion H.
  - destruct l2 as [| a2 tl2]; simpl in *; [ inversion H|].
    + destruct H as (H & _); inversion H.
    + destruct H as ((Ha2 & Hc & H) & Ha0).
      repeat split; auto; lia.
Qed.

Lemma gamma_list_tail_only_if: forall l1 l2 a b,
  gamma_list (l1 ++ [a]) (l2 ++ [b]) ->
    gamma_list l1 l2 /\ gamma b a /\ tnum_ge_inv b.
Proof.
  induction l1; simpl; unfold tnum_ge_inv in *; intros.
  - destruct l2; simpl; inversion H.
    + intuition.
    + exfalso.
      destruct l2; simpl in *; inversion H1; auto.
  - destruct l2 as [| a2 tl2]; simpl in *; [ inversion H|].
    + exfalso.
      destruct l1; simpl in *; inversion H1; auto.
    + destruct H as (Ha2 & Hc & H).
      apply IHl1 in H.
      destruct H as (Hl1 & Ha0).
      intuition.
Qed.

Lemma gamma_list_tail_iff: forall l1 l2 a b,
  gamma_list l1 l2 /\ gamma b a /\ tnum_ge_inv b <->
    gamma_list (l1 ++ [a]) (l2 ++ [b]).
Proof.
  split.
  apply gamma_list_tail_if.
  apply gamma_list_tail_only_if.
Qed.

Lemma value_mask_decompose_tnum_sum2: forall n l lv lm ls d di ls_l1 ls_l2
  (Hn: length l = n)
  (Hge: tnum_ge_inv d)
  (Hd : gamma d di)
  (Hg : gamma_list ls l)
  (Hv : lv = map (fun a : Z * Z => (fst a, 0)) l)
  (Hm : lm = map (fun a : Z * Z => (0, snd a)) l)
  (Hls_eq : list_eq_z_three ls ls_l1 ls_l2 = true),
    exists d1 d2,
      di = d1 + d2 /\
      gamma (tnum_add_sum lv (fst d, 0)) (fold_left (fun a b : Z => a + b) ls_l1 d1) /\
      gamma (tnum_add_sum lm (0, snd d)) (fold_left (fun a b : Z => a + b) ls_l2 d2).
Proof.
  induction n as [| n1].
  { 
    simpl; intros; subst.
    destruct l; [| inversion Hn].
    destruct ls; [| inversion Hg].
    simpl in *.
    destruct ls_l1.
    2: { destruct ls_l2; inversion Hls_eq. }
    destruct ls_l2; [| inversion Hls_eq].
    unfold tnum_add_sum; simpl.
    apply value_mask_decompose_a_tnum; auto.
  }
  simpl; intros; subst.

  pose proof (list_Sn_tail _ _ Hn) as Hln.
  destruct Hln as (ln & a & n2 & Hn2_len & Hl_eq).

  rewrite Hl_eq in *.
  rewrite ! map_app in *. simpl. simpl in Hls_eq.
  rewrite ! tnum_add_sum_tail.

  destruct a as (av & am).

  (**change ls to ls ++ [sa] *)
  assert (Heq: exists lm m, ls = lm ++ [m]). {
    clear - Hg.
    destruct ls as [| a l] eqn: Hls.
    { destruct ln; simpl in Hg; inversion Hg. }

    assert (Heq: length ls = S (length l)).
    { subst ls. simpl; auto. }
    apply  list_Sn_tail in Heq.
    destruct Heq as (la & an & n1 & Hlen & Heq).
    exists la, an.
    rewrite Hls in *.
    auto.
  }
  destruct Heq as (lm & m & Hlm_eq).
  rewrite Hlm_eq in *.

  apply list_eq_z_three_tail_exist in Hls_eq as He.
  destruct He as (a1 & a2 & l3 & l4 & Hls_l1_eq & Hls_l2_eq & Hls_12_eq).
  subst ls_l1 ls_l2.

  simpl in *.
  
  apply list_eq_z_three_tail_iff in Hls_eq.
  destruct Hls_eq as (Hls_eq & Ha12_eq).

  rewrite last_length in Hn.
  rewrite Nat.succ_inj_wd in Hn.
  
  apply gamma_list_tail_iff in Hg.
  destruct Hg as (Hg & Hgm & Hgm_inv).

  eapply IHn1 with (l := ln)
    (lv := map (fun a : Z * Z => (fst a, 0)) ln)
    (lm := map (fun a : Z * Z => (0, snd a)) ln)
    (d := d) (di := di) in Hls_eq; eauto.

  destruct Hls_eq as (td1 & td2 & Hdi_eq & Hls_eq1 & Hls_eq2).

  pose proof (value_mask_decompose_a_tnum _ _ Hgm_inv Hgm) as Hi_eq.
  destruct Hi_eq as (i1 & i2 & Hi_eq & Hgi1_eq& Hgi2_eq).
  exists (i1 + td1 - a1), (i2 + td2 - a2).
  split; [lia | ].
  split.
  - pose proof (list_fold_left_z_add_eq (l3 ++ [a1]) i1 (td1 - a1)) as Heq.
    rewrite Z.add_sub_assoc in Heq.
    rewrite Heq; clear Heq.
    rewrite fold_left_tail_eq.
    apply tnum_add_sound; auto.
  - pose proof (list_fold_left_z_add_eq (l4 ++ [a2]) i2 (td2 - a2)) as Heq.
    rewrite Z.add_sub_assoc in Heq.
    rewrite Heq; clear Heq.
    rewrite fold_left_tail_eq.
    apply tnum_add_sound; auto.
Qed.

(**r [Lemma 9] Value-mask-decomposed tnum summations*)
Lemma value_mask_decompose_tnum_sum: forall l lv lm ls d di
  (Hge: tnum_ge_inv d)
  (Hd: gamma d di)
  (Hg: gamma_list ls l)
  (Hv: lv = map (fun a : Z * Z => (fst a, 0)) l) (**r sum_0_n-1 (Tj.v, 0) *)
  (Hm: lm = List.map (fun a => (0, snd a)) l) (**r sum_0_n-1 (0, Tj.m) *)
  ,
    gamma (
      tnum_add (tnum_add_sum lv (fst d, 0)) (tnum_add_sum lm (0, snd d)))
      (List.fold_left (fun a b => a + b) ls di). (**r sum_0_n-1 S *)
Proof.
  intros.
  pose proof (list_split_exists ls) as Hls_eq.
  destruct Hls_eq as (ls_l1 & ls_l2 & Hls_eq).

  assert (Heq: length l = length l) by auto.
  pose proof (value_mask_decompose_tnum_sum2 (length l) l lv lm ls d di ls_l1 ls_l2
    Heq Hge Hd Hg Hv Hm Hls_eq) as Hi_eq.
  destruct Hi_eq as (i1 & i2 & Hi_eq & Hgi1_eq& Hgi2_eq).

  pose proof (sum_add_split_eq _ _ _ di _ _ Hls_eq Hi_eq) as Hls_sum.
  rewrite Hls_sum.
  
  apply tnum_add_sound; auto.
Qed.

(*
Fixpoint calc_acc_v (n: nat) (a b d: tnum): tnum :=
  match n with
  | O => d
  | S n1 =>
    let acc_v := tnum_add d (
      if (Z.eqb (Z.land (fst a) 1) 1) then (fst b, 0) else (0, 0)) in
      calc_acc_v n1 (tnum_rshift a 1) (tnum_lshift b 1) acc_v
  end.

Fixpoint calc_acc_m (n: nat) (a b f: tnum): tnum :=
  match n with
  | O => f
  | S n1 =>
    let acc_m := tnum_add f (
      if Z.eqb (Z.land (fst a) 1) 1 then (0, snd b)
      else if Z.eqb (Z.land (snd a) 1) 1 then (0, Z.lor (fst b) (snd b))
      else (0, 0)) in
      calc_acc_m n1 (tnum_rshift a 1) (tnum_lshift b 1) acc_m
  end. *)

(**r [Property P2.] ACCV and ACCM are value-mask-decomposed summations of partial products. *)
Lemma value_mask_decompose_sum: forall n a b x y acc_v acc_m d di f fi
  (Hd_inv: tnum_ge_inv d)
  (Hd: gamma d di)
  (Hf_inv: tnum_ge_inv f)
  (Hf: gamma f fi)
  (Hgx: gamma a x)
  (Ha_inv: tnum_ge_inv a)
  (Hgy: gamma b y)
  (Hb_inv: tnum_ge_inv b)
  (Hacc: tnum_mul_simple_rec n a b d f = (acc_v, acc_m))
  ,
  exists l,
    gamma_list (partial_product n x y) l /\
    acc_v = (tnum_add_sum
              (List.map (fun a => (fst a, 0)) l) (**r sum_0_n-1 (Tj.v, 0) *)
              d) /\
    acc_m = (tnum_add_sum
              (List.map (fun a => (0, snd a)) l) (**r sum_0_n-1 (0, Tj.m) *)
              f).
Proof.
  induction n; intros.
  {
    simpl in *.
    inversion Hacc.
    exists [].
    split; auto.
  }

  assert (Ha1: gamma (tnum_rshift a 1) (Z.shiftr x 1)). {
    apply tnum_rshift_sound; auto.
  }

  assert (Hb1: gamma (tnum_lshift b 1) (Z.shiftl y 1)). {
    apply tnum_lshift_sound; auto.
  }

  destruct b as (ba, bm).
  simpl in Hacc.
  rewrite partial_product_Sn.
  remember (Z.land x 1 * y) as h1 eqn: Hh1.
  remember (partial_product n (Z.shiftr x 1) (Z.shiftl y 1)) as t1 eqn: Ht1.
  apply value_mask_decompose_a_tnum in Hgy as Hgy_eq; auto.
  simpl in Hgy_eq.
  destruct Hgy_eq as (y1 & y2 & Hy_eq & Hgy1 & Hgy2).

  assert (Hor_y: gamma (0, Z.lor ba bm) y). {
    clear - Hgy. 
    unfold gamma in *; simpl in *.
    subst ba.
    
    apply Z.bits_inj.
    unfold Z.eqf.
    intro n.
    assert (N : n < 0 \/ n >= 0) by lia.
    destruct N as [HN | HN]; [destruct n; try lia; simpl; reflexivity | ].
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite! Z.lor_spec.
    rewrite! Z.land_spec.
    rewrite! Z.lnot_spec by lia.
    rewrite Z.bits_0.
    destruct (Z.testbit y n); simpl; try lia.
    destruct (Z.testbit bm n); simpl; try lia.
  }

  
  assert (Hgdb: gamma
    (tnum_add d (if Z.land (fst a) 1 =? 1 then (ba, 0) else (0, 0)))
    (di + (if Z.land (fst a) 1 =? 1 then y1 else 0))). {
      destruct (Z.land (fst a) 1 =? 1).
      - apply tnum_add_sound; auto.
      - rewrite tnum_add_comm.
        erewrite tnum_add_0; eauto.
        rewrite Z.add_0_r.
        auto.
  }

  assert (Hgdf: gamma
    (tnum_add f
      (if Z.land (fst a) 1 =? 1
      then (0, bm)
      else if Z.land (snd a) 1 =? 1 then (0, Z.lor ba bm) else (0, 0)))

          (fi + (if Z.land (fst a) 1 =? 1
      then y2
      else if Z.land (snd a) 1 =? 1 then y else 0))
  ). {
      destruct (Z.land (fst a) 1 =? 1).
      - apply tnum_add_sound; auto.
      - destruct (Z.land (snd a) 1 =? 1).
        + apply tnum_add_sound; auto.
        + rewrite tnum_add_comm.
          erewrite tnum_add_0; eauto.
          rewrite Z.add_0_r.
          auto.
    }
  
  (** compute the di for Hacc *)
  destruct (Z.land (fst a) 1 =? 1) eqn: Ha1_1.
  {
    rewrite Z.eqb_eq in Ha1_1.
    assert (Heq: Z.land x 1 = 1). {
      clear - Hgx Ha1_1.
      unfold gamma in Hgx.
      rewrite <- Hgx in Ha1_1.
      
      apply Z.bits_inj_iff.
      unfold Z.eqf.
      intro n.
      assert (N : n < 0 \/ n >= 0) by lia.
      destruct N as [HN | HN]; [destruct n; try lia; simpl; reflexivity | ].

      apply Z.bits_inj_iff in Ha1_1.
      unfold Z.eqf in Ha1_1.
      specialize (Ha1_1 n).
      rewrite! Z.land_spec in *.
      destruct (Z.testbit x n); auto.
    }
    rewrite Heq in Hh1; clear Heq.
    rewrite Z.mul_1_l in Hh1.
    subst h1.

    eapply IHn with (d := tnum_add d (ba, 0))
      (f := tnum_add f (0, bm)) in Hacc; eauto.
    - destruct Hacc as (lr & Hglr & Hacc_v & Hacc_m).
      exists ((ba, bm)::lr).
      simpl.
      split.
      + subst t1.
        split; auto.
      + split; auto.
    - apply tnum_ge_inv_add; auto.
      clear - Hb_inv.
      unfold tnum_ge_inv in *.
      simpl in *.
      lia.
    - apply tnum_ge_inv_add; auto.
      clear - Hb_inv.
      unfold tnum_ge_inv in *.
      simpl in *.
      lia.
    - apply tnum_ge_inv_rshift; auto.
    - apply tnum_ge_inv_lshift; auto.
  }

  destruct (Z.land (snd a) 1 =? 1) eqn: Ha2_1.
  {
    rewrite Z.eqb_eq in Ha2_1.

    assert (Hh1_eq: h1 = 0 \/ h1 = y). {
      clear - Hgx Ha_inv  Hh1.
      pose proof (Z_land_1_eq x) as Heq.
      destruct Heq as [Heq | Heq]; lia.
    }

    eapply IHn with (d := d)
      (f := tnum_add f (0, Z.lor ba bm)) in Hacc; eauto.
    - destruct Hacc as (lr & Hglr & Hacc_v & Hacc_m).
      {
        exists ((0, Z.lor ba bm)::lr).
        simpl.
        split.
        - subst t1.
          split; auto.
          + unfold gamma.
            simpl.
            destruct Hh1_eq as [Hh1_0 | Hh1_y].
            { subst h1.
              rewrite Hh1_0.
              auto.
            }
            rewrite Hh1_y.
            clear - Hgy.
            unfold gamma in *.
            simpl in *.
            subst ba.

            apply Z.bits_inj.
            unfold Z.eqf.
            intro n.
            assert (N : n < 0 \/ n >= 0) by lia.
            destruct N as [HN | HN]; [destruct n; try lia; simpl; reflexivity | ].
            rewrite! Z.land_spec.
            rewrite! Z.lnot_spec by lia.
            rewrite! Z.lor_spec.
            rewrite! Z.land_spec.
            rewrite! Z.lnot_spec by lia.
            rewrite Z.bits_0.
            destruct (Z.testbit y n); simpl; try lia.
            destruct (Z.testbit bm n); simpl; try lia.

          + split.
            * unfold tnum_ge_inv; simpl.
              split; try lia.
              rewrite Z.lor_nonneg.
              unfold tnum_ge_inv in Hb_inv; simpl in Hb_inv.
              lia.
            * auto.
        - rewrite tnum_add_comm.
          erewrite tnum_add_0; eauto.
      }
    - apply tnum_ge_inv_add; auto.
      clear - Hb_inv.
      unfold tnum_ge_inv in *.
      simpl in *.
      split; try lia.
      rewrite Z.lor_nonneg.
      lia.
    - apply tnum_ge_inv_rshift; auto.
    - apply tnum_ge_inv_lshift; auto.
  }

  rewrite Z.eqb_neq in *.
  assert (Heq: Z.land x 1 = 0). {
    clear - Hgx Ha_inv Ha1_1 Ha2_1.
    unfold tnum_ge_inv in *.
    destruct Ha_inv as (Ha & Hb).
    assert (Heq: 0 <= fst a \/ 0 <= 1) by lia.
    rewrite <- Z.land_nonneg in Heq.
    assert (H1: 0 <= 1) by lia.
    apply Z_land_leb with (j := (fst a)) in H1.
    rewrite Z.land_comm in H1.

    assert (Ha0: Z.land (fst a) 1 = 0) by lia.

    assert (Heq1: 0 <= snd a \/ 0 <= 1) by lia.
    rewrite <- Z.land_nonneg in Heq1.
    assert (H2: 0 <= 1) by lia.
    apply Z_land_leb with (j := (snd a)) in H2.
    rewrite Z.land_comm in H2.

    assert (Hb0: Z.land (snd a) 1 = 0) by lia.
    clear - Hgx Ha0 Hb0.
    unfold gamma in Hgx.
    rewrite <- Hgx in Ha0; clear Hgx.

    apply Z.bits_inj_iff in Ha0, Hb0.
    apply Z.bits_inj.
    unfold Z.eqf in *.
    intro n.
    assert (N : n < 0 \/ n >= 0) by lia.
    destruct N as [HN | HN]; [destruct n; try lia; simpl; reflexivity | ].

    specialize (Ha0 n).
    specialize (Hb0 n).
    rewrite! Z.land_spec in *.
    rewrite! Z.lnot_spec in * by lia.
    rewrite Z.bits_0 in *.
    destruct (Z.testbit x n); simpl; try lia.
    destruct (Z.testbit 1 n); simpl; try lia.
    destruct (Z.testbit (snd a) n); simpl; try lia.
  }
  rewrite Heq in Hh1.
  simpl in Hh1.
  subst h1.
  
  clear Hgdf.

  eapply IHn with (x := Z.shiftr x 1) (y := Z.shiftl y 1)
    (d:= d) (f := f) in Hacc; eauto.
  - destruct Hacc as (lr & Hglr & Hacc_v & Hacc_m).
    exists ((0, 0)::lr).
    simpl.
    split.
    + subst t1.
      split; auto.
      * apply gamma_const.
      * split.
        *** unfold tnum_ge_inv; simpl; lia.
        *** auto.
    + rewrite ! tnum_add_comm with (b := (0,0)).
      erewrite ! tnum_add_0; eauto.
  - apply tnum_ge_inv_rshift; auto.
  - apply tnum_ge_inv_lshift; auto.
Qed.


Lemma partial_product_fst_0: forall l n a k
  (Ha_inv : tnum_ge_inv a)
  (Hga : 0 = fst a)
  (Hl : gamma_list (partial_product n 0 k) l),
  tnum_add_sum (map (fun a : Z * Z => (fst a, 0)) l) (0,0) = (0,0)%Z.
Proof.
  induction l; simpl; intros.
  {
    auto.
  }

  rewrite tnum_add_0 with (i := fst a).
  2:{
    unfold gamma; simpl.
    rewrite Z.lnot_0.
    rewrite Z.land_m1_r.
    auto.
  }

  destruct n as [| n1]; simpl in Hl.
  { inversion Hl. }

  destruct Hl as (Hga1 & Ha1_inv & Hl).

  rewrite Z.shiftr_0_l in Hl.
  apply IHl with (a := a0) in Hl; auto.
  
  unfold gamma in Hga1.
  rewrite Z.land_comm in Hga1.
  rewrite Z.land_0_r in Hga1.
  rewrite <- Hga1.
  auto.
Qed.

Lemma partial_product_snd_eq: forall l n a b acc_m j k
  (Ha_inv : tnum_ge_inv a)
  (Hb_inv : tnum_ge_inv b)
  (Hgb : gamma b j)
  (Hl : gamma_list (partial_product n 0 k) l)
  (Hacc_m : acc_m = tnum_add_sum (map (fun a : Z * Z => (0, snd a)) l) b),
    gamma acc_m j.
Proof.
  induction l; simpl; intros.
  { subst.
    auto.
  }

  destruct n as [| n1]; simpl in Hl.
  { inversion Hl. }

  destruct Hl as (Hga1 & Ha1_inv & Hl).

  rewrite Z.shiftr_0_l in Hl.
  apply IHl with (a := a0)
    (b := tnum_add b (0, snd a))
    (acc_m := acc_m) (j := j) in Hl; auto.

  - apply tnum_ge_inv_add; auto.
    clear - Ha1_inv.
    unfold tnum_ge_inv in *.
    destruct Ha1_inv as (Ha & Hb).
    simpl; split; lia.
  - replace j with (j + 0) by lia.
    apply tnum_add_sound; auto.
    unfold gamma; simpl.
    auto.
Qed.

Lemma Z_size_leb: forall a b, 0 <= a <= b -> (Z_size a <= Z_size b)%nat.
Proof.
  intros.
  unfold Z_size.
  destruct a; destruct b; simpl; try lia.
  revert p p0 H.
  induction p; simpl; intros; try lia.
  - destruct p0; simpl in *; try lia; rewrite ! Pos2Nat.inj_succ;
    apply le_n_S.
    + apply IHp; auto.
    + apply IHp; auto.
      lia.
  - destruct p0; simpl in *; try lia; rewrite ! Pos2Nat.inj_succ;
    apply le_n_S.
    + apply IHp; auto. lia.
    + apply IHp; auto.
Qed.

(** [tnum_mul_simple_sound] proves the soundness of the abstract multiplication *)
Lemma tnum_mul_simple_sound : forall a b i j
  (Ha_inv: tnum_ge_inv a)
  (Hb_inv: tnum_ge_inv b)
  (Hga: gamma a i)
  (Hgb: gamma b j),
    gamma (tnum_mul_simple a b (Z_size i)) (i*j).
Proof.
  unfold tnum_mul_simple; intros.
  destruct tnum_mul_simple_rec as (acc_v & acc_m) eqn: Hmul.
  pose proof (gamma_const 0) as Hg0.
  assert (Hinv0: tnum_ge_inv (0, 0)). {
    unfold tnum_ge_inv; simpl; lia.
  }
  eapply value_mask_decompose_sum
    with (di := 0) (fi := 0) in Hmul; eauto.
  rewrite partial_product_eq.
  assert (Hi_ge: 0 <= i). {
    clear - Ha_inv Hga.
    unfold tnum_ge_inv, gamma in *.
    rewrite <- Hga in Ha_inv.
    destruct Ha_inv as (Ha & Hb).
    clear Hga.
    rewrite Z.land_nonneg in Ha.
    rewrite Z.lnot_nonneg in Ha.
    lia.
  }
  assert (Hj_ge: 0 <= j). {
    clear - Hb_inv Hgb.
    unfold tnum_ge_inv, gamma in *.
    rewrite <- Hgb in Hb_inv.
    destruct Hb_inv as (Ha & Hb).
    clear Hgb.
    rewrite Z.land_nonneg in Ha.
    rewrite Z.lnot_nonneg in Ha.
    lia.
  }

  unfold Zpartial_product.
  destruct a as (av & am).
  destruct i; simpl in *; try lia.
  - unfold gamma in Hga, Hgb.
    rewrite Z.land_comm in Hga, Hgb.
    rewrite Z.land_0_r in Hga.
    destruct Hmul as (l & Hl & Hacc_v & Hacc_m).
    destruct l; inversion Hl.
    simpl in *.
    subst.
    rewrite tnum_add_0 with (i := 0); auto.
  - destruct Hmul as (l & Hl & Hacc_v & Hacc_m).

    apply value_mask_decompose_tnum_sum with
      (lv := map (fun a : Z * Z => (fst a, 0)) l)
      (lm := map (fun a : Z * Z => (0, snd a)) l)
      (d := (0,0)) (di := 0) in Hl; auto.

    unfold tnum_add_sum in *; simpl in *.
    rewrite <- Hacc_v in Hl.
    rewrite <- Hacc_m in Hl.
    auto.
Qed.

Lemma tnum_add_snd_0 : forall a b,
  tnum_add (a, 0) (b, 0) = (a + b, 0).
Proof.
  intros. unfold tnum_add. simpl.
  rewrite Z.lxor_nilpotent. simpl.
  rewrite Z.lnot_0. rewrite Z.land_m1_r. reflexivity.
Qed.

Lemma Z_mul_step : forall a b k,
  0 <= a -> 0 <= k -> Z.mul (Z.land a (Z.ones (k + 1))) b =
  Z.mul (Z.land a 1) b + Z.mul (Z.land (Z.shiftr a 1) (Z.ones k)) (Z.shiftl b 1).
Proof.
  intros. rewrite Z.shiftl_mul_pow2; try lia.
  rewrite (Z.mul_comm b).
  rewrite Z.mul_assoc.
  rewrite <- Z.mul_add_distr_r.
  destruct (Z.eqb_spec b 0) as [E|E].
  - subst b. rewrite !Z.mul_0_r. reflexivity.
  - apply Z.mul_cancel_r; try lia.
    rewrite (Z_bits_decomp (Z.land a (Z.ones (k + 1))) 1); try lia.
    2: { rewrite Z.land_ones; lia. }
    assert (Hequiv1: Z.land (Z.land a (Z.ones (k + 1))) (Z.ones 1) = Z.land a 1).
    { rewrite <- Z.land_assoc. rewrite (Z.land_comm _ 1).
      rewrite Z.land_ones_low; simpl; try lia. }
    assert (Hequiv2: Z.shiftl (Z.shiftr (Z.land a (Z.ones (k + 1))) 1) 1 = Z.land (Z.shiftr a 1) (Z.ones k) * 2 ^ 1).
    { rewrite Z.shiftl_mul_pow2; try lia.
      apply Z.mul_cancel_r; try lia.
      rewrite Z.shiftr_land. rewrite (Z_shiftr_ones); try lia. }
    rewrite Hequiv1, Hequiv2. reflexivity.
Qed.

Lemma tnum_mul_equiv : forall a b i
  (Ha_inv: tnum_ge_inv a)
  (Hga: gamma a i),
    tnum_mul a b (Z_size i) = tnum_mul_simple a b (Z_size i).
Proof.
  intros. unfold tnum_mul, tnum_mul_simple.
  rewrite (surjective_pairing (tnum_mul_simple_rec (Z_size i) a b (0, 0) (0, 0))).
  assert (H1 : forall n a b d f,
    snd d = 0 -> 0 <= fst a -> (fst d + Z.mul (Z.land (fst a) (Z.ones (Z.of_nat n))) (fst b), 0)
                  = fst (tnum_mul_simple_rec n a b d f)).
  { intros n. induction n as [| n' IHn'].
    - intros. rewrite Z.ones_equiv. rewrite Z.land_0_r.
      rewrite Z.add_0_r. simpl.
      rewrite surjective_pairing. rewrite H. reflexivity.
    - intros. unfold tnum_mul_simple_rec; fold tnum_mul_simple_rec.
      rewrite (surjective_pairing d) at 2.
      rewrite (surjective_pairing d) at 4. rewrite H. rewrite tnum_add_snd_0.
      assert ((if Z.land (fst a0) 1 =? 1 then (fst d + fst b0, 0) else (fst d, 0))
              = (fst d + Z.mul (Z.land (fst a0) 1) (fst b0), 0)).
      { destruct (Z.eqb_spec (Z.land (fst a0) 1) 1) as [E|E].
        - rewrite E. rewrite Z.mul_1_l. reflexivity.
        - assert (Z.land (fst a0) 1 = 0).
          { pose proof (Z_land_1_eq (fst a0)). lia. }
          rewrite H1. rewrite Z.add_0_r. reflexivity. }
      rewrite H1.
      rewrite <- IHn'.
      + unfold fst at 4. rewrite tnum_lshift_fst. rewrite tnum_rshift_fst.
        rewrite Nat2Z.inj_succ; rewrite <- Z.add_1_r.
        set (k := Z.of_nat n'). rewrite Z_mul_step; try lia. 
        rewrite Z.add_assoc. reflexivity.
      + destruct (Z.land (fst a0) 1 =? 1); reflexivity + apply H.
      + rewrite tnum_rshift_fst. apply Z.shiftr_nonneg. apply H0. }
  assert (Hequiv1: (fst a * fst b, 0) = fst (tnum_mul_simple_rec (Z_size i) a b (0, 0) (0, 0))).
  { rewrite <- H1; try reflexivity.
    2:{ unfold tnum_ge_inv in Ha_inv. lia. }
    assert (fst a = Z.land (fst a) (Z.ones (Z.of_nat (Z_size i)))).
    { assert (0 <= i) by apply (tnum_ge_inv_gamma _ _ Hga Ha_inv).
      assert (fst a <= i) by apply (tnum_ge_inv_gamma_bound _ _ Hga Ha_inv).
      destruct i eqn:Ei; try lia.
      - unfold gamma in Hga. simpl in Hga. rewrite <- Hga. reflexivity.
      - unfold tnum_ge_inv in Ha_inv. rewrite Z.land_ones_low; try lia.
        rewrite Z_size_equiv. unfold Z_size_Z. rewrite (Z.abs_eq _ H).
        assert (Z.log2 (fst a) <= Z.log2 (Z.pos p)) by apply (Z.log2_le_mono _ _ H0).
        lia. }
    rewrite H at 1. reflexivity. }
  assert (H2: forall n a b d f,
    tnum_mul_rec n a b f = let (res_d, res_f) := tnum_mul_simple_rec n a b d f in res_f).
  { intros n. induction n as [| n' IHn'].
    - intros. simpl. reflexivity.
    - intros. unfold tnum_mul_rec; fold tnum_mul_rec.
      unfold tnum_mul_simple_rec; fold tnum_mul_simple_rec.
      rewrite (IHn' _ _ (if Z.land (fst a0) 1 =? 1 then tnum_add d (fst b0, 0) else d) _).
      reflexivity. }
  assert (Hequiv2: tnum_mul_rec (Z_size i) a b (0, 0) = snd (tnum_mul_simple_rec (Z_size i) a b (0, 0) (0, 0))).
  { rewrite (H2 _ _ _ (0,0) _). reflexivity. }
  rewrite Hequiv1, Hequiv2. reflexivity.
Qed.

Lemma tnum_mul_sound : forall a b i j
  (Ha_inv: tnum_ge_inv a)
  (Hb_inv: tnum_ge_inv b)
  (Hga: gamma a i)
  (Hgb: gamma b j),
    gamma (tnum_mul a b (Z_size i)) (i * j).
Proof.
  intros. rewrite (tnum_mul_equiv _ _ i); auto.
  apply tnum_mul_simple_sound; auto.
Qed.