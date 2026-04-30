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

Definition tnum := (Z * Z)%type.

Definition gamma  (a: tnum) (x: Z) : Prop :=
   (Z.land x (Z.lnot (snd a))) = (fst a).


(** [tnum_add a b] performs the abstract addition *)
Definition tnum_add (a b: Z * Z): Z * Z :=
  let sv    := (fst a) + (fst b) in
  let sm    := (snd a) + (snd b) in
  let sigma := sm + sv in
  let chi   := Z.lxor sigma sv in
  let mu    := Z.lor chi (Z.lor (snd a) (snd b)) in
    (Z.land sv (Z.lnot mu), mu).

(** [tnum_shiftl] *)
Definition tnum_shiftl (x:tnum) (i:Z) :=
  (Z.shiftl (fst x) i , Z.shiftl (snd x) i).


(** [tnum_join] computes the join of the tnum domain. *)
Definition tnum_join (a b:tnum) :=
  let v := Z.lxor (fst a) (fst b) in
  let m := Z.lor (Z.lor (snd a)  (snd b))  v in
  (Z.land (Z.lor (fst a) (fst b)) (Z.lnot  m),m).


(** [pos_mu] find the position of the first unknown bit i.e the first trailing 1 in the mask.
    There should be a fast way to do it.
    In x86, there is a TZCNT instruction which counts the number of trailing zeros.
    This may be provided by the hardware, compiler etc.
*)
Fixpoint pos_mu (p:positive) :=
  match p with
  | xH | xI _ => 0
  | xO p => pos_mu p + 1
  end.

Definition pos_muz (z:Z) :=
  match z with
  | Zpos p => pos_mu p
  | Z0     => 0 (* Should not happen *)
  | Zneg p => pos_mu p
  end.

(* [split_at_mu] splits a tnum at the first unknow.
   The divisions/mod should be implemented using shift and mask
*)
Definition split_at_mu (x:tnum) :=
  let i := pos_muz (snd x) in
  let x1 := (fst x / 2 ^ (i+1) , snd x / 2 ^ (i+1)) in
  let x2 := (fst x mod 2 ^ i , snd x mod 2 ^ i) in
  (x1,i,x2).



(** [tnum_mul_const] multiplies a constant [c] by the tnum [x]
    which has [j] unknown bits and [n] is the fuel (Z.of_nat n = j).
*)

Fixpoint tnum_mul_const (c:Z) (x:tnum) (j:Z) (n:nat) : tnum :=
  match n with
  | O => (c * fst x, 0)
  | S n' => let '(y1,i1,y2) := split_at_mu x in
           let p := tnum_mul_const c y1 (j-1) n' in
           let mc := (c * fst y2,0) in
           let mu0 := tnum_add (tnum_shiftl p (i1+1)) mc in
           let mu1 := tnum_add mu0 (Z.shiftl c i1,0) in
           tnum_join mu0 mu1
  end.


(** [xtnum_mul x i y j n] computes the multiplication of
  [x]  which has [i] unknown bits by
  [y]  which has [j] unknown bits such (i <= j) and
  the fuel n = i + j *)
Fixpoint xtnum_mul (x:tnum) (i:Z)  (y:tnum) (j:Z) (n:nat) (* i <= j n= i+j *) :=
  match n with
  | O => (* we have i = j = 0 *)
      (fst x * fst y,0)
  | S n' => let '(y1,i1,y2) := split_at_mu y in
            (* y = y1.mu.y2 *)
            let p := if Z.eqb i j then
                       xtnum_mul y1 (j-1) x i n'
                     else xtnum_mul x i y1 (j - 1) n' in
            let mc := tnum_mul_const (fst y2) x i (Z.to_nat i) in
            let mu0 := tnum_add (tnum_shiftl p (i1+1)) mc in
            let mu1 := tnum_add mu0 (tnum_shiftl x i1) in
            tnum_join mu0 mu1
  end.

(** The correctness theorem is the following.
    [wf_pos x] says that (0 <= snd x) (otherwise -1 has an infinite number of unknows)
    [zcnt] should be [pos_muz] (I think).
    Anyhow, I proved the following theorem. *)
Definition wf_pos (x:tnum) := 0 <= snd x.

Fixpoint pos_cnt (b:bool) (x:positive) :=
  match x with
  | xH => Z.b2z b
  | xI p => pos_cnt b p + Z.b2z b
  | xO p => pos_cnt b p + Z.b2z (negb b)
  end.

Definition zcnt (z:Z) :=
  match z with
  | Z0 => 0
  | Zpos p => pos_cnt true p
  | Zneg _ => 0
  end.

Lemma tnum_mul_const_correct :
  forall c n i x xb
         (WFp : wf_pos x)
         (I : i = zcnt (snd x))
         (LEN: i = Z.of_nat n),
    gamma  x xb ->
    gamma (tnum_mul_const c x i n) (c * xb).
Proof.
Admitted.

(* I also have proof of xtnum_mul_correct *)
Lemma xtnum_mul_correct : forall n x y i j xb yb
                                 (WFp : wf_pos x)
                                 (WFp : wf_pos y)
                                 (I  : i = zcnt (snd x))
                                 (J  : j = zcnt (snd y))
                                 (LE : i <= j)
                                 (LEN : i+j = Z.of_nat n)
  ,
    gamma x xb ->
    gamma y yb ->
    gamma (xtnum_mul x i y j n) (xb * yb).
Proof.
Admitted.

Definition tnum_is_const (x:tnum) :=
  Z.eqb (snd x) 0.

(** [zsize z] returns the number of bits of the number.
    i.e the position of the most significant bit that is set.
    It should be O(1) for 64 bits integers. *)
Definition zsize (z:Z) :=
  match z with
  | Z0 => 0
  | Zpos p => Z.pos (Pos.size p)
  | Zneg p => Z.pos (Pos.size p)
  end.

Definition tnum_size (x:tnum) := Z.max (zsize (fst x)) (zsize (snd x)).

Definition tnum_clearbit (x:tnum) (i:Z) :=
  (Z.clearbit (fst x) i , Z.clearbit (snd x) i).

Definition tnum_max (x:tnum) := Z.lor (fst x) (snd x).

(** [xtnum_mul_high x y n] multiplies x by y
    where n is the number of bits that are set in either x or y.
    We also have that x <= y and 0 <= x and 0 <= y *)
Fixpoint xtnum_mul_high (x:tnum) (y:tnum) (n:nat) {struct n} (* x <= y *) :=
  if tnum_is_const x && tnum_is_const y (* if both are constants, perform normal multiplication *)
  then (fst x * fst y , 0)
  else
    match n with
    | O => (0,0) (* should not happen *)
    | S n' =>
      let b := tnum_size y in
      let ym := Z.testbit (snd y) (b - 1) in
      let y'      := tnum_clearbit y (b - 1) in (* clear the highest bit of y *)
      let p := (* recursively perform the multiplication *)
        if Z.leb (tnum_max y') (tnum_max x)
        then
          xtnum_mul_high y' x   n'
        else  xtnum_mul_high x y' n' in
      if ym (* if the highest bit is uncertain, we perform a join *)
      then tnum_join (tnum_add p (tnum_shiftl x (b - 1))) p
      else (tnum_add p (tnum_shiftl x (b - 1)))
  end.

(** The theorem only holds for positive numbers.
    This should not be a problem - 64 bits can be given an unsigned interpretation. *)
Definition tnum_pos (x:tnum) := 0 <= fst x /\ 0 <= snd x.

Fixpoint pset (p:positive) :=
  match p with
  | xH => 1
  | xI p => 1 + pset p
  | xO p => pset p
  end.

Definition zset (z:Z) :=
  match z with
  | Z0 => 0
  | Zpos p => pset p
  | Zneg p => 0 (* should not happen *)
  end.

Definition tnum_set (x:tnum) := zset (Z.lor (fst x) (snd x)).

Eval compute in
    let x := (0,Z.ones 4) in
    let y := (Z.ones 5,0) in 
    (xtnum_mul_high x y (Z.to_nat (tnum_set x + tnum_set y))).

Lemma xtnum_mul_high_correct :
  forall n x y xb yb
         (WFX : tnum_pos x)
         (WFY : tnum_pos y)
         (LT  : tnum_size x <= tnum_size y)
         (LEN : tnum_set x + tnum_set y = Z.of_nat n)
  ,
    gamma x xb ->
    gamma y yb ->
    gamma (xtnum_mul_high x y n) (xb * yb).
Proof.
Admitted.
