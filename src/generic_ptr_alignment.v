(**
  check_generic_ptr_alignment() 的对齐建模。

  对应 verifier.c 中 check_generic_ptr_alignment()：
  - 非 strict alignment 直接通过；
  - 1 字节访问直接通过；
  - 否则计算 reg_off = tnum_add(reg->var_off, tnum_const(reg->off + off))，
    再检查 tnum_is_aligned(reg_off, size)。
 *)

From Coq Require Import ZArith Bool Lia.
From compcert.lib Require Import Integers.
From bpf.tnum Require Import tnum tnum_proof.
Open Scope Z_scope.

Record verifier_reg_state : Type := {
  reg_var_off : tnum;
  reg_fixed_off : Z
}.

Definition generic_ptr_reg_off (reg : verifier_reg_state) (off : Z)
    : tnum :=
  tnum_add (reg_var_off reg)
    (tnum_const (Int64.repr (reg_fixed_off reg + off))).

Definition generic_ptr_alignment_checked (reg : verifier_reg_state)
    (off size : Z) (strict : bool) : bool :=
  if negb strict then true
  else if Z.eqb size 1 then true
  else tnum_is_aligned (generic_ptr_reg_off reg off) (Int64.repr size).

Lemma aligned_mem_tnum_low_bits_zero :
  forall a x low_bits,
    mem_tnum x a ->
    tnum_low_bits_zero a low_bits = true ->
    Int64.and x low_bits = Int64.zero.
Proof.
  intros.
  eapply tnum_low_bits_zero_sound; eauto.
Qed.

Theorem generic_ptr_alignment_checked_sound :
  forall reg off size strict,
    Int64_is_pow2 (Int64.repr size) = true ->
    generic_ptr_alignment_checked reg off size strict = true ->
    strict = false \/
    size = 1 \/
    forall v,
      mem_tnum v (reg_var_off reg) ->
      (Int64.signed (Int64.repr size) |
        Int64.signed (Int64.add v (Int64.repr (reg_fixed_off reg + off)))).
Proof.
  intros reg off size strict Hpow Hchecked.
  unfold generic_ptr_alignment_checked in Hchecked.
  destruct strict eqn:Hstrict.
  - destruct (Z.eqb size 1) eqn:Hsize.
    + right; left. apply Z.eqb_eq; exact Hsize.
    + right; right.
      intros v Hmem.
      destruct (Int64_pow2_unsigned_exponent_smod (Int64.repr size)) as [k [Hk Hsize']].
      { exact Hpow. }
      pose proof (tnum_add_mem_sound (reg_var_off reg)
                  (tnum_const (Int64.repr (reg_fixed_off reg + off)))
                  v (Int64.repr (reg_fixed_off reg + off)) Hmem
                  (mem_tnum_zero (Int64.repr (reg_fixed_off reg + off)))) as Hmem_add.
      assert (Hlow_bits :
        Int64.and (Int64.add v (Int64.repr (reg_fixed_off reg + off)))
          (Int64.sub (Int64.repr size) Int64.one) = Int64.zero).
      {
        unfold tnum_is_aligned in Hchecked.
        destruct (Int64.eq (Int64.repr size) Int64.zero) eqn:Hzero.
        - apply Int64.same_if_eq in Hzero.
          rewrite Hzero in Hsize'.
          rewrite Int64.unsigned_zero in Hsize'.
          lia.
        - simpl in Hchecked.
          apply aligned_mem_tnum_low_bits_zero
            with (a := generic_ptr_reg_off reg off)
                 (x := Int64.add v (Int64.repr (reg_fixed_off reg + off))).
          + exact Hmem_add.
          + exact Hchecked.
      }
      apply Int64_and_pow2_low_bits_zero_divide_signed_smod with
        (k := k) in Hlow_bits; auto.
  - left; reflexivity.
Qed.

Definition fixed_stack_reg : verifier_reg_state := {|
  reg_var_off := tnum_const (Int64.repr 0);
  reg_fixed_off := 0
|}.

Definition fixed_stack_alignment_checked (off size : Z) : bool :=
  generic_ptr_alignment_checked fixed_stack_reg off size true.
