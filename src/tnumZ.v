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

Lemma gamma_const_uniq : forall a i,
  snd a = 0 -> gamma a i -> i = fst a.
Proof.
  intros. unfold gamma in H0.
  rewrite H in H0. rewrite Z.lnot_0 in H0.
  rewrite Z.land_m1_r in H0. auto.
Qed.

Lemma gamma_0 : forall i,
  gamma (0, 0) i -> i = 0.
Proof.
  intros. unfold gamma in H; simpl in H.
  rewrite <- Z.ldiff_land in H.
  rewrite Z.ldiff_0_r in H.
  apply H.
Qed.

Definition tnum_lshift (a: tnum) (shift: Z): tnum :=
  ( Z.shiftl (fst a) shift, Z.shiftl (snd a) shift).

Definition tnum_rshift (a: tnum) (shift: Z): tnum :=
  ( Z.shiftr (fst a) shift, Z.shiftr (snd a) shift).


Definition Z_size (x: Z) : nat :=
  match x with
  | Zpos p | Zneg p => Pos.to_nat (Pos.size p)
  | _ => 0
  end.

Definition Z_size_Z (x: Z) : Z :=
  match x with
  | Z0 => 0
  | _ => Z.log2 (Z.abs x) + 1
  end.

Lemma Z_size_equiv : forall x, Z.of_nat (Z_size x) = Z_size_Z x.
Proof.
  intros x. unfold Z_size, Z_size_Z.
  destruct x; try reflexivity;
  rewrite <- Z.log2_shiftl; simpl;
  try apply positive_nat_Z;
  try apply Pos2Z.is_pos;
  try lia.
Qed.

Lemma Z_size_Z_nonneg : forall x, 0 <= Z_size_Z x.
Proof.
  intros. unfold Z_size_Z. destruct x.
  - simpl. lia.
  - assert (0 <= Z.log2 (Z.abs (Z.pos p))) by apply Z.log2_nonneg. lia.
  - assert (0 <= Z.log2 (Z.abs (Z.neg p))) by apply Z.log2_nonneg. lia.
Qed.

Definition tnum_num_bits (a: tnum): nat :=
  Nat.max (Z_size (fst a)) (Z_size (snd a)).

Fixpoint tnum_mul_rec (fuel: nat) (a b f: tnum): tnum :=
  match fuel with
  | O => f
  | S n =>
    let c1 := Z.eqb (Z.land (fst a) 1) 1 in
    let c2 := Z.eqb (Z.land (snd a) 1) 1 in
    let acc_m := if c1 then tnum_add f (0, snd b)
                  else if c2 then tnum_add f (0, Z.lor (fst b) (snd b)) 
                  else f in
      tnum_mul_rec n (tnum_rshift a 1) (tnum_lshift b 1) acc_m
  end.

Definition tnum_mul (a b: tnum) (width: nat): tnum :=
  let acc_v := (Z.mul (fst a) (fst b), 0) in
  let acc_m := tnum_mul_rec width a b (0, 0) in
    tnum_add acc_v acc_m.

Fixpoint tnum_mul_simple_rec (fuel: nat) (a b d f: tnum): tnum * tnum :=
  match fuel with
  | O => (d, f)
  | S n =>
    let c1 := Z.eqb (Z.land (fst a) 1) 1 in
    let c2 := Z.eqb (Z.land (snd a) 1) 1 in
    let acc_v := if c1 then tnum_add d (fst b, 0) else d in
    let acc_m := if c1 then tnum_add f (0, snd b)
                  else if c2 then tnum_add f (0, Z.lor (fst b) (snd b))
                  else f in
      tnum_mul_simple_rec n (tnum_rshift a 1) (tnum_lshift b 1) acc_v acc_m
  end.

Definition tnum_mul_simple (a b: tnum) (width: nat): tnum :=
  (*let n := tnum_num_bits a in *)
  let (acc_v, acc_m) := tnum_mul_simple_rec width a b (0, 0) (0, 0) in
    tnum_add acc_v acc_m.

(* Here is Truncating Division but I use Z.div instead of Z.quot
   to be consistent with the divu definition in CompCert's Int64. *)
Definition tnum_udiv (a b: tnum): tnum :=
  if Z.eqb (fst b) 0 && Z.eqb (snd b) 0 then
    (0, 0) (* BPF div specification: x / 0 = 0 *)
  else if Z.eqb (snd a) 0 && Z.eqb (snd b) 0 then
    (Z.div (fst a) (fst b), 0) (* concrete udiv *)
  else if Z.eqb (fst b) 0 then
    (0, -1) (* -1 represents unsigned_max *)
  else let max_res := Z.div (fst a + snd a) (fst b) in
    (0, Z.ones (Z_size_Z max_res)).

Definition Z_is_pow2 (n : Z) : bool :=
  (0 <? n) && (Z.land n (n - 1) =? 0).

Definition Z_pow2 (n : Z) : Prop :=
  0 < n /\ exists x, 0 <= x /\ 2 ^ x = n.

Definition mod_get_low_bits (a b: tnum):tnum :=
  if Z.odd (fst b) || Z.odd (snd b) then (0, -1)
  else let b_max := fst b + snd b in
    let mask := (Z.land b_max (-b_max)) - 1 in
      (Z.land (fst a) mask, Z.lor (Z.land (snd a) mask) (Z.lnot mask)).
      (* set bits except low_bits in res.m to 1 *)

(* Here is Truncating Remainder but I use Z.modulo instead of Z.rem
   to be consistent with the modu definition in CompCert's Int64. *)
Definition tnum_umod (a b: tnum): tnum :=
  if Z.eqb (fst b) 0 && Z.eqb (snd b) 0 then
    a (* BPF mod specification: x % 0 = x *)
  else if Z.eqb (snd a) 0 && Z.eqb (snd b) 0 then
    (Z.modulo (fst a) (fst b), 0) (* concrete udiv *)
  else if Z.eqb (snd b) 0 && Z_is_pow2 (fst b) then
    (Z.land (fst a) ((fst b) - 1), Z.land (snd a) ((fst b) - 1))
  else if Z.eqb (fst b) 0 then
    (0, -1) (* -1 represents unsigned_max *)
  else let res := mod_get_low_bits a b in
    let a_max := fst a + snd a in
    let b_max := fst b + snd b in
    let mask := Z.ones (Z_size_Z (Z.min a_max b_max)) in
      (Z.land (fst res) mask, Z.land (snd res) mask).
