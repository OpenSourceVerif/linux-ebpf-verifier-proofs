From Coq Require Import List ZArith Bool.
From compcert.lib Require Import Integers.
Import ListNotations.
Require Import tnumZ.

Definition u8 := byte.
Definition s32 := int.
Definition u32 := int.
Definition u64 := int64.
Definition s64 := int64.

Definition u64_of_u8 (v: u8): u64 := Int64.repr (Byte.unsigned v).

Definition s32_of_u64 (v: u64): s32 := Int.repr (Int64.signed v).

Definition s32_of_u8 (v: u8): s32 := Int.repr (Byte.signed v).

Definition s64_of_u8 (v: u8): s64 := Int64.repr (Byte.signed v).

Definition u64_of_s32 (v: s32): u64 := Int64.repr (Int.signed v).

Definition u64_of_u32 (v: u32): u64 := Int64.repr (Int.unsigned v).

Definition tnum: Type := u64 * u64.
(*
Record tnum := {
  tnum_value: int64;
  tnum_mask:  int64;
}.

Definition tnum_unknown: tnum := {|
  tnum_value  := Int64.zero;
  tnum_mask   := Int64.mone;
|}.
*)

Definition tnum_unknown: tnum := (Int64.zero, Int64.mone).

Definition tnum_const (value: u64): tnum := (value, Int64.zero).

Definition tnum_range (min max: u64): tnum :=
  let chi   := Int64.xor min max in
  let bits  := u64_of_u8 (Byte.repr (Int64.size chi)) in (**r fls64 is to find last set bit in a 64-bit word *)
    if Int64.lt (Int64.repr 63) bits then
      tnum_unknown
    else
      let delta := Int64.sub (Int64.shl Int64.one bits) Int64.one in
        (Int64.and min (Int64.not delta), delta).

Definition tnum_lshift (a: tnum) (shift: int64): tnum :=
  (Int64.shl (fst a) shift, Int64.shl (snd a) shift).
Definition tnum_rshift (a: tnum) (shift: int64): tnum :=
  (Int64.shru (fst a) shift, Int64.shru (snd a) shift).
Definition tnum_arshift (a: tnum) (shift: int64): tnum :=
  (Int64.shr (fst a) shift, Int64.shr (snd a) shift).

Definition tnum_add (a b: tnum): tnum :=
  let sm    := Int64.add (snd a) (snd b) in
  let sv    := Int64.add (fst a) (fst b) in
  let sigma := Int64.add sm sv in
  let chi   := Int64.xor sigma sv in
  let mu    := Int64.or chi (Int64.or (snd a) (snd b)) in
    (Int64.and sv (Int64.not mu), mu).

Definition tnum_sub (a b: tnum): tnum :=
  let dv    := Int64.sub (fst a) (fst b) in
  let alpha := Int64.add dv (snd a) in
  let beta  := Int64.sub dv (snd b) in
  let chi   := Int64.xor alpha beta in
  let mu    := Int64.or chi (Int64.or (snd a) (snd b)) in
    (Int64.and dv (Int64.not mu), mu).

Definition tnum_and (a b: tnum): tnum :=
  let alpha := Int64.or (fst a) (snd a) in
  let beta  := Int64.or (fst b) (snd b) in
  let v     := Int64.and (fst a) (fst b) in
    (v, Int64.and alpha (Int64.and beta (Int64.not v))).

Definition tnum_or (a b: tnum): tnum :=
  let v   := Int64.or (fst a) (fst b) in
  let mu  := Int64.or (snd a) (snd b) in
    (v, Int64.and mu (Int64.not v)).

Definition tnum_xor (a b: tnum): tnum :=
  let v   := Int64.xor (fst a) (fst b) in
  let mu  := Int64.or (snd a) (snd b) in
    (Int64.and v (Int64.not mu), mu).

Definition tnum_neg (a : tnum): tnum :=
  tnum_sub (Int64.zero, Int64.zero) a.

Fixpoint tnum_mul_rec_early_ret (fuel: nat) (a b acc_m: tnum) : tnum :=
  match fuel with
  | O => acc_m
  | S n =>
    if orb (negb (Int64.eq (fst a) Int64.zero))
           (negb (Int64.eq (snd a) Int64.zero)) then
      let c1 := negb (Int64.eq (Int64.and (fst a) Int64.one) Int64.zero) in
      let c2 := negb (Int64.eq (Int64.and (snd a) Int64.one) Int64.zero) in
      let acc_m := if c1 then tnum_add acc_m (Int64.zero, snd b)
                    else if c2 then tnum_add acc_m (Int64.zero, Int64.or (fst b) (snd b))
                    else acc_m in
        tnum_mul_rec_early_ret n (tnum_rshift a Int64.one) (tnum_lshift b Int64.one) acc_m
    else
      acc_m
  end.

Fixpoint tnum_mul_rec (fuel: nat) (a b acc_m: tnum) : tnum :=
  match fuel with
  | O => acc_m
  | S n =>
    let c1 := Int64.eq (Int64.and (fst a) Int64.one) Int64.one in
    let c2 := Int64.eq (Int64.and (snd a) Int64.one) Int64.one in
    let acc_m := if c1 then tnum_add acc_m (Int64.zero, snd b)
                  else if c2 then tnum_add acc_m (Int64.zero, Int64.or (fst b) (snd b))
                  else acc_m in
      tnum_mul_rec n (tnum_rshift a Int64.one) (tnum_lshift b Int64.one) acc_m
  end.

Definition tnum_mul (a b: tnum) (width: nat): tnum :=
  let acc_v := (Int64.mul (fst a) (fst b), Int64.zero) in
  let acc_m := tnum_mul_rec width a b (Int64.zero, Int64.zero) in
    tnum_add acc_v acc_m.

Definition Int64_size (x: u64) : Z :=
  Z_size_Z (Int64.unsigned x).

Definition Int64_ones (n : Z) : u64 :=
  Int64.repr (Z.ones n).

Definition Int64_odd (x: u64) : bool :=
  Z.odd (Int64.unsigned x).

Definition Int64_is_pow2 (x: u64) : bool :=
  Z_is_pow2 (Int64.unsigned x).

Definition Int64_min (a b : u64) : Z :=
  Z.min (Int64.unsigned a) (Int64.unsigned b).

Definition tnum_udiv (a b: tnum): tnum :=
  if (Int64.eq (fst b) Int64.zero) && (Int64.eq (snd b) Int64.zero) then
    (Int64.zero, Int64.zero) (* BPF div specification: x / 0 = 0 *)
  else if (Int64.eq (snd a) Int64.zero) && (Int64.eq (snd b) Int64.zero) then
    (Int64.divu (fst a) (fst b), Int64.zero) (* concrete udiv *)
  else if (Int64.eq (fst b) Int64.zero) then
    (Int64.zero, Int64.mone) (* -1 represents unsigned_max *)
  else let max_res := Int64.divu (Int64.add (fst a) (snd a)) (fst b) in
    (Int64.zero, Int64_ones (Int64_size max_res)).

Definition tnum_union (a b: tnum) : tnum :=
  let (a_v, a_m) := a in
  let (b_v, b_m) := b in
  let v := Int64.and a_v b_v in
  let mu := Int64.or (Int64.xor a_v b_v) (Int64.or a_m b_m) in
    (Int64.and v (Int64.not mu), mu).

Definition tnum_union_opt (oa ob: option tnum) : option tnum :=
  match oa, ob with
  | None, ob => ob
  | oa, None => oa
  | Some a, Some b => Some (tnum_union a b)
  end.

Definition Int64_min_signed := Int64.repr Int64.min_signed.

Definition Int64_msb (x: s64) : bool := Int64.lt x Int64.zero.

Definition tnum_get_positive (a: tnum) : option tnum :=
  let (v, m) := a in
  if Int64_msb v then None
  else if Int64_msb m then
    Some (v, Int64.and m (Int64.not Int64_min_signed))
  else Some a.

Definition tnum_get_negative (a: tnum) : option tnum :=
  let (v, m) := a in
  if Int64_msb v then Some a
  else if Int64_msb m then
    Some (Int64.or v Int64_min_signed, Int64.and m (Int64.not Int64_min_signed))
  else None.

Definition tnum_abs (a: tnum) : tnum :=
  if Int64_msb (fst a) then tnum_neg a else a.

Definition tnum_sdiv_helper (a b: tnum) : tnum :=
  let a_abs := tnum_abs a in
  let b_abs := tnum_abs b in
  let res_abs := tnum_udiv a_abs b_abs in
  if Bool.eqb (Int64_msb (fst a)) (Int64_msb (fst b)) then
    res_abs
  else
    tnum_neg res_abs.

Definition tnum_sdiv_common (a b: tnum) : tnum :=
  let a_pos := tnum_get_positive a in
  let a_neg := tnum_get_negative a in
  let b_pos := tnum_get_positive b in
  let b_neg := tnum_get_negative b in
  let calc (oa ob: option tnum) :=
    match oa, ob with
    | Some x, Some y => Some (tnum_sdiv_helper x y)
    | _, _ => None
    end in
  let res_opt := 
    tnum_union_opt (tnum_union_opt (calc a_pos b_pos) (calc a_neg b_neg))
                   (tnum_union_opt (calc a_pos b_neg) (calc a_neg b_pos)) in
  match res_opt with
  | Some res => res
  | None => tnum_unknown (* impossible *)
  end.

Definition tnum_sdiv (a b: tnum): tnum :=
  let (a_v, a_m) := a in
  let (b_v, b_m) := b in
  if Int64.eq b_m Int64.zero then
    if Int64.eq b_v Int64.zero then 
      (Int64.zero, Int64.zero) (* BPF div specification: x / 0 = 0 *)
    else if Int64.eq a_m Int64.zero then
      if (Int64.eq a_v Int64_min_signed) && (Int64.eq b_v Int64.mone) then
        (Int64_min_signed, Int64.zero) (* BPF div specification: S_MIN / -1 = S_MIN *)
      else
        (Int64.divs a_v b_v, Int64.zero) (* concrete sdiv *)
    else
      tnum_sdiv_common a b
  else if Int64.eq b_v Int64.zero then
    (Int64.zero, Int64.mone) (* tnum_unknown *)
  else
    tnum_sdiv_common a b.

Definition mod_get_low_bits (a b: tnum):tnum :=
  if Int64_odd (fst b) || Int64_odd (snd b) then (Int64.zero, Int64.mone)
  else let b_max := Int64.add (fst b) (snd b) in
    let mask := Int64.sub (Int64.and b_max (Int64.neg b_max)) Int64.one in
      (Int64.and (fst a) mask, Int64.or (Int64.and (snd a) mask) (Int64.not mask)).

Definition tnum_umod (a b: tnum): tnum :=
  if (Int64.eq (fst b) Int64.zero) && (Int64.eq (snd b) Int64.zero) then
    a (* BPF mod specification: x % 0 = x *)
  else if (Int64.eq (snd a) Int64.zero) && (Int64.eq (snd b) Int64.zero) then
    (Int64.modu (fst a) (fst b), Int64.zero) (* concrete umod *)
  else if Int64.eq (snd b) Int64.zero && Int64_is_pow2 (fst b) then
    (Int64.and (fst a) (Int64.sub (fst b) Int64.one),
     Int64.and (snd a) (Int64.sub (fst b) Int64.one))
  else if (Int64.eq (fst b) Int64.zero) then
    (Int64.zero, Int64.mone) (* -1 represents unsigned_max *)
  else let res := mod_get_low_bits a b in
    let a_max := Int64.add (fst a) (snd a) in
    let b_max := Int64.add (fst b) (snd b) in
    let mask := Int64_ones (Z_size_Z (Int64_min a_max b_max)) in
      (Int64.and (fst res) mask, Int64.and (snd res) mask).

Definition tnum_intersect (a b: tnum): tnum :=
  let v   := Int64.xor (fst a) (fst b) in
  let mu  := Int64.and (snd a) (snd b) in
    (Int64.and v (Int64.not mu), mu).

Definition tnum_cast (a: tnum) (size: u8): tnum :=
  let v   := Int64.and (fst a) (Int64.sub (Int64.shl Int64.one (Int64.mul (u64_of_u8 size) (Int64.repr 8))) Int64.one) in
  let m   := Int64.and (snd a) (Int64.sub (Int64.shl Int64.one (Int64.mul (u64_of_u8 size) (Int64.repr 8))) Int64.one) in
    (v, m).

Definition tnum_is_const (a: tnum): bool := Int64.eq (snd a) Int64.zero.

Definition tnum_equals_const (a: tnum) (b: u64): bool :=
  andb (tnum_is_const a) (Int64.eq (fst a) b).

Definition tnum_is_unknown (a: tnum): bool := Int64.eq (Int64.not (snd a)) Int64.zero.

(*
Definition tnum_is_aligned (a: tnum) (size: u64): bool :=
  if negb (negb (Int64.eq size Int64.zero)) then
    true
  else
    negb (negb (Int64.eq (Int64.and (Int64.or (fst a) (snd a)) (Int64.sub size Int64.one)) Int64.zero)). *)
Definition tnum_is_aligned (a: tnum) (size: u64): bool :=
  if Int64.eq size Int64.zero then
    true
  else
    Int64.eq (Int64.and (Int64.or (fst a) (snd a)) (Int64.sub size Int64.one)) Int64.zero.

Definition tnum_in (a b: tnum): bool :=
  if negb (Int64.eq (Int64.and (snd b) (Int64.not (snd a))) Int64.zero) then
    false
  else
    let v := Int64.and (fst b) (Int64.not (snd a)) in
      Int64.eq (fst a) v.

(**r Unused:
int tnum_sbin(char *str, size_t size, struct tnum a)
  *)

Definition tnum_subreg (a: tnum): tnum := tnum_cast a (Byte.repr 4).

Definition tnum_clear_subreg (a: tnum): tnum := tnum_lshift (tnum_rshift a (Int64.repr 32)) (Int64.repr 32).

Definition tnum_with_subreg (reg subreg: tnum): tnum := tnum_or (tnum_clear_subreg reg) (tnum_subreg subreg).

Definition tnum_const_subreg (a: tnum) (value: u32): tnum := tnum_with_subreg a (tnum_const (u64_of_u32 value)).

Definition tnum_subreg_is_const (a: tnum): bool := Int64.eq (snd (tnum_subreg a)) Int64.zero.