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
From bpf.src Require Import Zmore.

Definition tnum := (Z * Z)%type.

Definition gamma (a: tnum) (x: Z) : Prop :=
   (Z.land x (Z.lnot (snd a))) = (fst a).

Definition wf_tnum (a: tnum): Prop := (Z.land (fst a) (snd a)) = 0.

(** forall a b are generated randomly, the and+xor ensures the wf *)
Lemma random_and_xor_valid: forall a b,
  wf_tnum (a, Z.lxor (Z.land a b) b).
Proof.
  unfold wf_tnum; simpl; intros.
  apply Z.bits_inj.
  unfold Z.eqf.
  simpl.  intros n.
  assert (Hn0: n < 0 \/ n >= 0) by lia.
  destruct Hn0.
  - destruct n ; try lia. simpl. reflexivity.
  - rewrite! Z.land_spec.
    rewrite! Z.lxor_spec.
    rewrite! Z.land_spec.
    rewrite Z.bits_0.
    destruct (Z.testbit a n) eqn: Ha; try auto.
    destruct (Z.testbit b n) eqn: Hb; try auto.
Qed.

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

Definition tnum_in(a b: tnum): bool :=
  if Z.eqb (Z.land (snd b) (Z.lnot (snd a))) 0 then
    Z.eqb (fst a) (Z.land (fst b) (Z.lnot (snd a)))
  else
    false.


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
    (Z.land dv (Z.lnot mu), mu).

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

Lemma gamma_const : forall c,
  gamma (c, 0) c.
Proof.
  unfold gamma.
  simpl. intros.
  rewrite Z.lnot_0.
  rewrite Z.land_m1_r.
  reflexivity.
Qed.


Definition tnum_lshift (a: tnum) (shift: Z): tnum :=
  ( Z.shiftl (fst a) shift, Z.shiftl (snd a) shift).

Definition tnum_rshift (a: tnum) (shift: Z): tnum :=
  ( Z.shiftr (fst a) shift, Z.shiftr (snd a) shift).


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