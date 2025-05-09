From Coq Require Import List ZArith Lia.
From bpf.src Require Import tnumZ tnumZ_sub_sound.
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

Lemma tnum_add_0: forall a,
  tnum_add (0, 0) a = tnum_add a (0, 0).
Proof.
  unfold tnum_add; destruct a as (av, am); simpl; intros.
  rewrite ! Z.add_0_r.
  rewrite ! Z.lor_0_r. 
  f_equal.
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

(**r Lemma 9 *)
Lemma value_mask_decompose_tnum_sum: forall l lv lm ls d di
  (Hd: gamma d di)
  (Hg: forall a i, List.In (a,i) l -> gamma a i)
  (Hv: lv = List.map (fun a => (fst (fst a), 0)) l) (**r sum_0_n-1 (Tj.v, 0) *)
  (Hm: lm = List.map (fun a => (0, snd (fst a))) l) (**r sum_0_n-1 (0, Tj.m) *)
  (Hs: ls = List.map (fun a => snd a) l)
  ,
    gamma (
      tnum_add (tnum_add_sum lv (fst d, 0)) (tnum_add_sum lm (0, snd d)))
      (List.fold_left (fun a b => a + b) ls di). (**r sum_0_n-1 S *)
Proof.
  induction l.
  { 
    simpl; intros; subst.
    unfold tnum_add_sum; simpl.
    apply tnum_add_decompose; auto.
  }
  simpl; intros; subst.
  destruct a as ((av, am), i).
  simpl in *.
  remember (map (fun a : Z * Z * Z => (fst (fst a), 0)) l) as lv eqn: Hlv.
  remember (map (fun a : Z * Z * Z => (0, snd (fst a))) l) as lm eqn: Hlm.
  remember (map (fun a : tnum * Z => snd a) l) as ls eqn: Hls.
 ../..
  assert (Hgi: gamma (av, am) i). {
    apply Hg.
    auto.
  }

  (Hgi : gamma (av, am) i)
  (Hgd : gamma d di)
  (HG: gamma (tnum_add (tnum_add_sum lv0 (fst d, 0))
                       (tnum_add_sum lm0 (0, snd d)))
             (fold_left (fun a b : Z => a + b) ls0 di)),
      gamma (tnum_add (tnum_add (av, 0) (tnum_add_sum lv (fst d, 0)))
                      (tnum_add (0, am) (tnum_add_sum lm (0, snd d))))
            (fold_left (fun a b : Z => a + b) ls (di + i)).

  unfold tnum_add_sum in *; simpl.
  intros.

Qed.

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