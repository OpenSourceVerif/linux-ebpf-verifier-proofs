From Coq Require Import List ZArith.
From compcert.lib Require Import Integers.
From bpf.src Require Import tnum.

Import ListNotations.

Definition mem_tnum (x: int64) (a: tnum): bool :=
  Int64.eq (Int64.and x (Int64.not (snd a))) (fst a).

Definition wf_tnum (a: tnum): bool :=
  Int64.eq (Int64.and (fst a) (snd a)) Int64.zero.

Theorem tnum_add_sound : forall a b i j,
  wf_tnum a = true -> wf_tnum b = true ->
  mem_tnum i a = true -> mem_tnum j b = true ->
    mem_tnum (Int64.add i j) (tnum_add a b) = true.
Proof.

Qed.