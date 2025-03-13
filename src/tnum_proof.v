From Coq Require Import List ZArith.
From compcert.lib Require Import Integers.
From bpf.src Require Import tnum.

Import ListNotations.

Definition mem_tnum (x: int64) (a: tnum): bool :=
  Int64.eq (Int64.and x (Int64.not (snd a))) (fst a).

Definition wf_tnum (a: tnum): bool :=
  Int64.eq (Int64.and (fst a) (snd a)) Int64.zero.

Lemma add_distrib_int64 : forall a b c d,
  Int64.add (Int64.add a b) (Int64.add c d) = Int64.add (Int64.add c a) (Int64.add d b).
Proof.
  intros.
  rewrite Int64.add_assoc.
  rewrite Int64.add_permut with (x := b)(y := c)(z := d).
  rewrite <- Int64.add_assoc.
  rewrite Int64.add_commut with (x := a)(y := c).
  rewrite Int64.add_commut with (x := b)(y := d).
  reflexivity.
Qed.

Theorem tnum_add_sound : forall a b i j,
  wf_tnum a = true -> wf_tnum b = true ->
  mem_tnum i a = true -> mem_tnum j b = true ->
    mem_tnum (Int64.add i j) (tnum_add a b) = true.
Proof.
  intros.
  unfold mem_tnum, wf_tnum , tnum_add in *.
  simpl.
  destruct a as [va ma], b as [vb mb]; simpl in *.
  apply Int64.same_if_eq in H, H0, H1, H2.
  Search(Int64.add).
  apply Int64.add_is_or in H,H0.
  rewrite add_distrib_int64.
  rewrite H, H0.
  Search (Int64.or).
  Search (Int64.or (Int64.or _ _) _).
  


  rewrite Int64.not_or_and_not.
  rewrite Int64.not_or_and_not.



Qed.