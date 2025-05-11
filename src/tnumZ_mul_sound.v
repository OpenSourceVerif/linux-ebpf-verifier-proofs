From Coq Require Import List ZArith Lia.
From bpf.src Require Import tnumZ tnumZ_add_sound tnumZ_sub_sound tnumZ_shift_sound.
Import ListNotations.

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

Definition tnum_add_sum (l: list tnum) (d: tnum): tnum := (**default = (0, 0) *)
  List.fold_right (fun a b => tnum_add a b) d l.

Lemma tnum_add_sum_cons: forall l a d,
  tnum_add_sum (a :: l) d = tnum_add a (tnum_add_sum l d).
Proof.
  unfold tnum_add_sum; induction l; simpl; intros.
  - auto.
  - rewrite <- IHl.
    simpl.
    rewrite tnum_add_comm.
    auto.
Qed.

Lemma tnum_add_sum_tail: forall l a d,
  tnum_add_sum (l++[a]) d = (tnum_add_sum l (tnum_add a d)).
Proof.
  unfold tnum_add_sum; induction l as [| t tl]; simpl; intros.
  - auto.
  - rewrite <- IHtl.
    rewrite ! fold_right_app.
    simpl.
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
  (Hi: 0 <= i)
  (Hd: gamma a i),
    exists i1 i2, i = i1+i2 /\ gamma (fst a, 0) i1 /\ gamma (0, snd a) i2.
Proof.    
  destruct a as (av, am); simpl; intros.
  exists av, (i-av).
  repeat split.
  - pose proof (smallest_concrete (av, am) i Hi Hd) as Hge.
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

Lemma value_mask_decompose_tnum_sum_1_2: forall l lv lm ls d di ls_l1 ls_l2
  (Hge: 0 <= di)
  (Hd : gamma d di)
  (Hg : forall (a : tnum) (i : Z), In (a, i) l -> gamma a i /\ 0 <= i)
  (Hv : lv = map (fun a : Z * Z * Z => (fst (fst a), 0)) l)
  (Hm : lm = map (fun a : Z * Z * Z => (0, snd (fst a))) l)
  (Hs : ls = map (fun a : tnum * Z => snd a) l)
  (Hls_eq : list_eq_z_three ls ls_l1 ls_l2 = true),
    exists d1 d2,
      di = d1 + d2 /\
      gamma (tnum_add_sum lv (fst d, 0)) (fold_left (fun a b : Z => a + b) ls_l1 d1) /\
      gamma (tnum_add_sum lm (0, snd d)) (fold_left (fun a b : Z => a + b) ls_l2 d2).
Proof.
  induction l as [| a l].
  { 
    simpl; intros; subst.
    destruct ls_l1.
    2: { destruct ls_l2; inversion Hls_eq. }
    destruct ls_l2; [| inversion Hls_eq].
    unfold tnum_add_sum; simpl.
    apply value_mask_decompose_a_tnum; auto.
  }
  simpl; intros; subst.
  destruct a as ((av & am) & i).
  destruct ls_l1 as [| a1 ls_tl1].
  { destruct ls_l2; inversion Hls_eq. }
  destruct ls_l2 as [| a2 ls_tl2].
  { inversion Hls_eq. }
  simpl in *.
  destruct (i =? a1 + a2) eqn: Hls_12_eq; [| inversion Hls_eq].
  rewrite Z.eqb_eq in Hls_12_eq.
  apply IHl with
    (lv := map (fun a : Z * Z * Z => (fst (fst a), 0)) l)
    (lm := map (fun a : Z * Z * Z => (0, snd (fst a))) l)
    (d := d) (di := di) in Hls_eq; auto.
  destruct Hls_eq as (td1 & td2 & Hdi_eq & Hls_eq1 & Hls_eq2).

  assert (Heq: (av, am, i) = (av, am, i) \/ In (av, am, i) l) by auto.
  specialize (Hg _ _ Heq); clear Heq.
  destruct Hg as (Hg & Hi_ge).
  pose proof (value_mask_decompose_a_tnum _ _ Hi_ge Hg) as Hi_eq.
  simpl in Hi_eq.
  destruct Hi_eq as (i1 & i2 & Hi_eq & Hgi1_eq& Hgi2_eq).
  exists (i1 + td1 - a1), (i2 + td2 - a2).
  rewrite ! Z.sub_add.
  split; [lia | ].
  split.
  - pose proof (list_fold_left_z_add_eq ls_tl1 i1 td1) as Heq.
    rewrite Heq; clear Heq.
    apply tnum_add_sound; auto.
  - pose proof (list_fold_left_z_add_eq ls_tl2 i2 td2) as Heq.
    rewrite Heq; clear Heq.
    apply tnum_add_sound; auto.
Qed.

(**r [Lemma 9] Value-mask-decomposed tnum summations*)
Lemma value_mask_decompose_tnum_sum: forall l lv lm ls d di
  (Hge: 0 <= di)
  (Hd: gamma d di)
  (Hg: forall a i, List.In (a,i) l -> gamma a i /\ 0 <= i)
  (Hv: lv = List.map (fun a => (fst (fst a), 0)) l) (**r sum_0_n-1 (Tj.v, 0) *)
  (Hm: lm = List.map (fun a => (0, snd (fst a))) l) (**r sum_0_n-1 (0, Tj.m) *)
  (Hs: ls = List.map (fun a => snd a) l)
  ,
    gamma (
      tnum_add (tnum_add_sum lv (fst d, 0)) (tnum_add_sum lm (0, snd d)))
      (List.fold_left (fun a b => a + b) ls di). (**r sum_0_n-1 S *)
Proof.
  intros.
  pose proof (list_split_exists ls) as Hls_eq.
  destruct Hls_eq as (ls_l1 & ls_l2 & Hls_eq).

  pose proof (value_mask_decompose_tnum_sum_1_2 l lv lm ls d di ls_l1 ls_l2 Hge Hd Hg Hv Hm Hs Hls_eq) as Hi_eq.
  destruct Hi_eq as (i1 & i2 & Hi_eq & Hgi1_eq& Hgi2_eq).

  pose proof (sum_add_split_eq _ _ _ di _ _ Hls_eq Hi_eq) as Hls_sum.
  rewrite Hls_sum.
  
  apply tnum_add_sound; auto.
Qed.

Fixpoint concrete_product (n: nat) (x y: Z): list Z :=
  match n with
  | O => []
  | S n1 =>
    let xn := if Z.testbit x (Z.of_nat n) then 1 else 0 in
    let zn := Z.shiftl (xn * y) (Z.of_nat n) in
    (concrete_product n1 x y) ++ [zn]
  end.


Fixpoint gamma_list (v: list Z) (l: list tnum): Prop :=
  match v, l with
  | [], [] => True
  | va::vtl, a::tl => gamma a va /\ gamma_list vtl tl
  | _, _ => False
  end.

Lemma gamma_list_imply: forall l
  (Hg: forall a i, List.In (a,i) l -> gamma a i /\ 0 <= i),
    gamma_list (List.map snd l) (List.map fst l).
Proof.
  induction l; simpl; intros.
  auto.

  split.
  - assert (Heq: a = (fst a, snd a) \/ In (fst a, snd a) l).
    + left.
      destruct a; auto.
    + specialize (Hg (fst a) (snd a) Heq); clear Heq.
      destruct Hg as (Hg & _); auto.
  - apply IHl.
    intros a0 i Hin.
    apply Hg.
    right; auto.
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
    destruct H as (Ha2 & Htl2).
    simpl.
    split; auto.
Qed.

Lemma gamma_list_tail_if: forall l1 l2 a b,
  gamma_list l1 l2 /\ gamma b a ->
    gamma_list (l1 ++ [a]) (l2 ++ [b]).
Proof.
  induction l1; simpl; intros.
  - destruct l2; simpl; inversion H.
    + split; auto.
    + destruct H as (H & _); inversion H.
  - destruct l2 as [| a2 tl2]; simpl in *; [ inversion H|].
    + destruct H as (H & _); inversion H.
    + destruct H as ((Ha2 & H) & Ha0).
      split; auto.
Qed.

Lemma gamma_list_tail_only_if: forall l1 l2 a b,
  gamma_list (l1 ++ [a]) (l2 ++ [b]) ->
    gamma_list l1 l2 /\ gamma b a.
Proof.
  induction l1; simpl; intros.
  - destruct l2; simpl; inversion H.
    + split; auto.
    + destruct l2; simpl; inversion H1.
  - destruct l2 as [| a2 tl2]; simpl in *; [ inversion H|].
    + destruct l1; simpl; inversion H1.
    + destruct H as (Ha2 & H).
      apply IHl1 in H.
      destruct H as (Hl1 & Ha0).
      repeat split; auto.
Qed.

Lemma gamma_list_tail_iff: forall l1 l2 a b,
  gamma_list l1 l2 /\ gamma b a <->
    gamma_list (l1 ++ [a]) (l2 ++ [b]).
Proof.
  split.
  apply gamma_list_tail_if.
  apply gamma_list_tail_only_if.
Qed.

Lemma value_mask_decompose_sum_1: forall n a b x y
  (Hgx: gamma a x)
  (Hgy: gamma b y),
  exists l,
    (List.map snd l) = (concrete_product n x y) /\
    gamma_list (List.map snd l) (List.map fst l).
Proof.
  induction n; intros.
  { exists []; simpl. auto. }

  remember (Z.shiftl
      ((if Z.testbit x (Z.of_nat (S n)) then 1 else 0) * y) (Z.of_nat (S n)))
      as res eqn: Hres.
  replace (concrete_product (S n) x y) with
    ((concrete_product n x y) ++ [res]).
  2:{ simpl; subst; auto. }

  specialize (IHn a b x y Hgx Hgy).
  destruct IHn as (l1 & Hl & Hg).
  rewrite <- Hl.

  destruct (Z.testbit x (Z.of_nat (S n))) eqn: Hx.
  - remember (tnum_lshift b (Z.of_nat (S n))) as Q eqn: HQ.
    assert (Heq: gamma Q res).
    { subst.
      apply tnum_lshift_sound.
      rewrite Z.mul_1_l.
      auto.
    }
    exists (l1 ++ [(Q, res)]).
    split.
    + rewrite map_last.
      simpl; auto.
    + rewrite ! map_app.
      simpl.
      apply gamma_list_app; auto.
      simpl.
      split; auto.
  - rewrite Z.mul_0_l in Hres.
    rewrite Z.shiftl_0_l in Hres.
    subst res.
    exists (l1 ++ [((0, 0), 0)]).
    split.
    + rewrite map_last.
      simpl; auto.
    + rewrite ! map_app.
      simpl.
      apply gamma_list_app; auto.
      simpl.
      split; auto.
      unfold gamma.
      simpl.
      auto.
Qed.

Lemma map_snd_app: forall l2 l res,
  map snd l = l2 ++ [res] ->
  exists (l1 : list (tnum * Z)) (k : tnum * Z),
    l = l1 ++ [k] /\ map snd l1 = l2 /\ snd k = res.
Proof.
  induction l2; simpl; intros.
  { destruct l; inversion H.
    destruct l; inversion H2.
    exists [],  p.
    simpl; auto.
  }

  destruct l as [| a1 tl].
  {
    simpl in H.
    inversion H.
  }

  simpl in H.
  inversion H.
  apply IHl2 in H2.
  destruct H2 as (tl1 & tk & Heq1 & Heq2 & Heq3).
  exists (a1:: tl1), tk.
  subst.
  simpl; auto.
Qed.

Lemma value_mask_decompose_sum_2: forall n a b x y l acc_v acc_m d f
  (Hgx: gamma a x)
  (Hgy: gamma b y)
  (Hacc: tnum_mul_simple_rec n a b d f = (acc_v, acc_m))

  (Hl_eq: List.map snd l = (concrete_product n x y))
  (Hgl: gamma_list (List.map snd l) (List.map fst l))
  
  ,
    acc_v = (tnum_add_sum
              (List.map (fun a => (fst (fst a), 0)) l) (**r sum_0_n-1 (Tj.v, 0) *)
              d).
Proof.
  induction n; intros.
  { simpl in *. inversion Hacc; subst.
    destruct l; inversion Hl_eq.
    simpl.
    auto.
  }

  destruct a as (va, ma).
  destruct b as (vb, mb).

  remember (Z.shiftl
      ((if Z.testbit x (Z.of_nat (S n)) then 1 else 0) * y) (Z.of_nat (S n)))
      as res eqn: Hres.
  replace (concrete_product (S n) x y) with
    ((concrete_product n x y) ++ [res]) in Hl_eq.
  2:{ simpl; subst; auto. }
  simpl in Hacc.

  destruct (tnum_mul_simple_rec n _ _ _ _)
     as (acc_v1, acc_m1)  eqn: Hmul.
    
  destruct (Z.land va 1 =? 1) eqn: Hknown; [
    rewrite Z.eqb_eq in Hknown |
    rewrite Z.eqb_neq in Hknown
  ].
  - (* x[j] is a known 1 *)
    inversion Hacc.
    rename H0 into Hacc_v.
    rename H1 into Hacc_m.
    clear Hacc.

    assert (Heq: exists l1 k, l = l1 ++ [k] /\ map snd l1 = concrete_product n x y /\
      snd k = res). {
      clear - Hl_eq.
      destruct l as [| a1 tl].
      - simpl in Hl_eq.
        exfalso.
        assert (Hnil: forall l (r: Z), l ++ [r] <> []). {
          clear.
          destruct l; simpl; intros.
          - intros HF. inversion HF.
          - intros HF. inversion HF.
        }
        eapply Hnil; eauto.
      - apply map_snd_app; auto.
    }
    destruct Heq as (l1 & k & Hl1_eq & Hl1_map & Hk_eq).
    subst l.
    rewrite ! map_last in Hgl.
    rewrite <- gamma_list_tail_iff in Hgl.
    destruct Hgl as (Hgl1 & Hgk).
    rewrite ! map_last in Hl_eq.
    rewrite app_inj_tail_iff in Hl_eq.
    destruct Hl_eq as (Hl1_eq & Hk2).

    rewrite ! map_last.
    rewrite tnum_add_sum_tail. ../..
    eapply IHn with (x := Z.shiftr x 1) (y := Z.shiftl y 1) (l := l1) in Hmul; eauto.
Qed.  

(**r [Property P2.] ACCV and ACCM are value-mask-decomposed summations of partial products. *)
Lemma value_mask_decompose_sum: forall n va ma vb mb x y acc_v acc_m d f di fi
  (Hgd: 0 <= di)
  (Hd: gamma d di)
  (Hgf: 0 <= fi)
  (Hf: gamma f fi)

  (Hgx: gamma (va, ma) x)
  (Hgy: gamma (vb, mb) y)
  (Hacc: tnum_mul_simple_rec n (va, ma) (vb, mb) d f = (acc_v, acc_m)),
  exists l,
    (List.map snd l) = (concrete_product n x y) /\
    gamma_list (List.map snd l) (List.map fst l) /\
    acc_v = (tnum_add_sum
              (List.map (fun a => (fst (fst a), 0)) l) (**r sum_0_n-1 (Tj.v, 0) *)
              d) /\
    acc_m = (tnum_add_sum
              (List.map (fun a => (0, snd (fst a))) l) (**r sum_0_n-1 (0, Tj.m) *)
              f).
Proof.
  induction n; intros.
  - exists [].
    simpl in *.
    inversion Hacc.
    repeat split; auto.
  - simpl in Hacc.
    remember (Z.shiftl
        ((if Z.testbit x (Z.of_nat (S n)) then 1 else 0) * y) (Z.of_nat (S n)))
        as res eqn: Hres.
    replace (concrete_product (S n) x y) with
      ((concrete_product n x y) ++ [res]).
    2:{ simpl; subst; auto. }
    
    destruct (tnum_mul_simple_rec n (tnum_rshift (va, ma) 1) (tnum_lshift (vb, mb) 1) d f)
     as (acc_v1, acc_m1)  eqn: Hmul.
    
    destruct (Z.land va 1 =? 1) eqn: Hknown; [
      rewrite Z.eqb_eq in Hknown |
      rewrite Z.eqb_neq in Hknown
    ].
    + (* x[j] is a known 1 *)
      inversion Hacc.
      rename H0 into Hacc_v.
      rename H1 into Hacc_m.
      clear Hacc.
      apply IHn with (x := x) (y := y) (di := di)(fi := fi) in Hmul; auto.
    +
    
    rewrite Z.shiftl_mul_pow2; [| lia].
    rewrite <- two_p_equiv.
    Search (two_p  _).
    unfold Z.testbit, Z.of_nat.
    destruct n; simpl; auto.
    destruct x; simpl; auto. 
    Search Z.shiftl. unfold Z.shiftl, Z.testbit; simpl. }
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