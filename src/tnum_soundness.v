From Coq Require Import ZArith Lia.
From compcert Require Import Values Integers.
From bpf.semantics Require Import ebpfSyntax ebpfBinSem.
From bpf.tnum Require Import tnum tnum_proof.

Open Scope Z_scope.

(** Abstract operands use an exact tnum for immediates. *)
Definition tnum_of_operand (v : tnum + int) : tnum :=
  match v with
  | inl t => t
  | inr i => tnum_const (int64_of_int i)
  end.

(** [eval_alu64] masks every shift count to six bits.  Keep the
    abstract interpreter in lockstep with that concrete semantics,
    including for immediate operands outside the verifier-accepted
    range [0, 63]. *)
Definition tnum_shift_amount (i : int) : int64 :=
  let masked :=
    Int.and (int_of_int64 (int64_of_int i)) (Int.repr 63) in
  Int64.repr (Int.unsigned masked).

Definition tnum_alu64 (op : aluOp) (dst : tnum)
    (operand : tnum + int) : tnum :=
  let src := tnum_of_operand operand in
  match op with
  | LSH =>
      match operand with
      | inr i => tnum_lshift dst (tnum_shift_amount i)
      | inl _ => tnum_unknown
      end
  | RSH =>
      match operand with
      | inr i => tnum_rshift dst (tnum_shift_amount i)
      | inl _ => tnum_unknown
      end
  | ARSH =>
      match operand with
      | inr i => tnum_arshift dst (tnum_shift_amount i)
      | inl _ => tnum_unknown
      end
  | ADD => tnum_add dst src
  | SUB => tnum_sub dst src
  | MUL => tnum_mul dst src
  | DIV => tnum_udiv dst src
  | SDIV => tnum_sdiv dst src
  | OR => tnum_or dst src
  | AND => tnum_and dst src
  | NEG => tnum_neg dst
  | MOD => tnum_umod dst src
  | SMOD => tnum_smod dst src
  | XOR => tnum_xor dst src
  | MOV => src
  | MOVSX c => tnum_movsx c src
  | END e s => tnum_end e s dst
  end.

Inductive match_operand : (val + int) -> (tnum + int) -> Prop :=
| match_op_reg : forall (v : val) (t : tnum),
    gamma_val v t ->
    match_operand (inl v) (inl t)
| match_op_imm : forall (i : int),
    match_operand (inr i) (inr i).

(** Small facts used to connect CompCert values and the tnum model. *)

Lemma gamma_val_const :
  forall i, gamma_val (Vlong i) (tnum_const i).
Proof.
  intros i. apply mem_tnum_zero.
Qed.

Lemma gamma_val_unknown :
  forall i, gamma_val (Vlong i) tnum_unknown.
Proof.
  intros i. apply tnum_unknown_gamma.
Qed.

Lemma masked_shift_in_range :
  forall x,
    Int.ltu (Int.and x (Int.repr 63)) Int64.iwordsize' = true.
Proof.
  intros x. unfold Int.ltu.
  apply Coqlib.zlt_true.
  change (Int.unsigned (Int.and x (Int.repr 63)) < 64).
  rewrite Int.and_commut.
  eapply Z.le_lt_trans.
  - apply Int.and_le.
  - change (Int.unsigned (Int.repr 63)) with 63.
    lia.
Qed.

Theorem tnum_alu64_sound :
  forall (op : aluOp)
         (dst_v : val) (dst_t : tnum)
         (src_v : val + int) (src_t : tnum + int),
  gamma_val dst_v dst_t ->
  match_operand src_v src_t ->
  gamma_val
    (eval_alu64 op dst_v src_v)
    (tnum_alu64 op dst_t src_t).
Proof.
  intros op dst_v dst_t src_v src_t Hdst Hsrc.
  inversion Hsrc as [src_r src_a Hsrc_gamma | imm]; subst.
  - destruct dst_v; simpl in Hdst; try contradiction.
    destruct src_r; simpl in Hsrc_gamma; try contradiction.
    destruct op; simpl.
    + exact
        (tnum_add_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + exact
        (tnum_sub_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + exact
        (tnum_mul_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + exact
        (tnum_udiv_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + apply tnum_sdiv_sound; assumption.
    + exact
        (tnum_or_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + exact
        (tnum_and_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + rewrite masked_shift_in_range. apply gamma_val_unknown.
    + rewrite masked_shift_in_range. apply gamma_val_unknown.
    + exact (tnum_neg_sound dst_t (Vlong i) Hdst).
    + exact
        (tnum_umod_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + apply tnum_smod_sound; assumption.
    + exact
        (tnum_xor_sound dst_t src_a (Vlong i) (Vlong i0)
          Hdst Hsrc_gamma).
    + exact Hsrc_gamma.
    + exact (tnum_movsx_sound c src_a (Vlong i0) Hsrc_gamma).
    + rewrite masked_shift_in_range. apply gamma_val_unknown.
    + match goal with
      | e : endOp, s : endSize |- _ =>
          exact (tnum_end_sound e s dst_t (Vlong i) Hdst)
      end.
  - destruct dst_v; simpl in Hdst; try contradiction.
    pose proof (gamma_val_const (int64_of_int imm)) as Himm.
    destruct op; simpl.
    + exact
        (tnum_add_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + exact
        (tnum_sub_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + exact
        (tnum_mul_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + exact
        (tnum_udiv_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + apply tnum_sdiv_sound; assumption.
    + exact
        (tnum_or_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + exact
        (tnum_and_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + exact
        (tnum_lshift_sound dst_t (Vlong i)
          (Int.and (int_of_int64 (int64_of_int imm)) (Int.repr 63))
          Hdst
          (masked_shift_in_range
            (int_of_int64 (int64_of_int imm)))).
    + exact
        (tnum_rshift_sound dst_t (Vlong i)
          (Int.and (int_of_int64 (int64_of_int imm)) (Int.repr 63))
          Hdst
          (masked_shift_in_range
            (int_of_int64 (int64_of_int imm)))).
    + exact (tnum_neg_sound dst_t (Vlong i) Hdst).
    + exact
        (tnum_umod_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + apply tnum_smod_sound; assumption.
    + exact
        (tnum_xor_sound dst_t (tnum_const (int64_of_int imm))
          (Vlong i) (Vlong (int64_of_int imm)) Hdst Himm).
    + exact Himm.
    + exact
        (tnum_movsx_sound c (tnum_const (int64_of_int imm))
          (Vlong (int64_of_int imm)) Himm).
    + exact
        (tnum_arshift_sound dst_t (Vlong i)
          (Int.and (int_of_int64 (int64_of_int imm)) (Int.repr 63))
          Hdst
          (masked_shift_in_range
            (int_of_int64 (int64_of_int imm)))).
    + match goal with
      | e : endOp, s : endSize |- _ =>
          exact (tnum_end_sound e s dst_t (Vlong i) Hdst)
      end.
Qed.
