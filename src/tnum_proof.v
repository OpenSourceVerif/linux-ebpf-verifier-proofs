From Coq Require Import List ZArith Lia.
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

Lemma int64_eq_if_same:
  forall x y : int64, x = y -> Int64.eq x y = true.
Proof.
  intros.
  subst.
  apply Int64.eq_true.
Qed.

Lemma mem_tnum_wf_tnum : forall i a
    (MEMA : mem_tnum i a = true),
  wf_tnum a = true.
Proof.
  unfold mem_tnum,wf_tnum.
  intros.
  destruct a as [va ma]; simpl in *.
  apply int64_eq_if_same.
  apply Int64.same_if_eq in MEMA.
  subst.
  rewrite Int64.and_assoc.
  rewrite Int64.and_commut with (x := Int64.not _).
  rewrite Int64.and_not_self in *.
  rewrite Int64.and_zero.
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
  apply int64_eq_if_same.
  apply Int64.same_if_eq in H, H0, H1, H2.
  subst va vb.
  apply Int64.same_bits_eq.
  intros.
  rewrite Int64.and_assoc in *.
  rewrite Int64.and_commut with (x := Int64.not _) in H.
  rewrite Int64.and_commut with (x := Int64.not _) in H0.
  rewrite Int64.and_not_self in *.
  clear H H0.
  rewrite ! Int64.bits_and; try assumption.
  rewrite add_distrib_int64.
  destruct (Int64.testbit
   (Int64.not
      (Int64.or
         (Int64.xor
            (Int64.add
               (Int64.add (Int64.and i (Int64.not ma)) ma)
               (Int64.add (Int64.and j (Int64.not mb)) mb))
            (Int64.add (Int64.and i (Int64.not ma))
               (Int64.and j (Int64.not mb))))
         (Int64.or ma mb))) i0) eqn: HT.
  2: {
    lia.
  }
  rewrite ! Bool.andb_true_r.
  remember (Int64.and j (Int64.not mb)) as hB eqn: Hb.
  remember (Int64.and i (Int64.not ma)) as hA eqn: Ha.
  remember (Int64.add hA hB) as hR eqn: Hr.

  rewrite Int64.add_commut with (y := ma) in HT.
  rewrite Int64.add_assoc in HT.
  rewrite Int64.add_commut with (x := hA) in HT.
  rewrite Int64.add_commut with (y := mb) in HT.
  rewrite Int64.add_assoc in HT.
  rewrite Int64.add_commut with (y := hA) in HT.
  rewrite <- Hr in HT.

  rewrite Int64.bits_not in HT; try assumption.
  rewrite Int64.bits_or in HT; try assumption.
  rewrite Int64.bits_xor in HT; try assumption.
  rewrite Int64.bits_or in HT; try assumption.
  rewrite Bool.negb_true_iff in HT.
  rewrite ! Bool.orb_false_iff in HT.
  destruct HT as (Hx & Ha0 & Hb0).
  apply Bool.xorb_eq in Hx.
  unfold u64 in *.
  rewrite <- Hx.

Compute (Int64.and Int64.zero (Int64.not Int64.one)).
Compute (Int64.and Int64.one (Int64.not Int64.zero)).
Compute (Int64.testbit (Int64.add Int64.one Int64.zero) 1).
Compute (Int64.testbit (Int64.add Int64.zero (Int64.add Int64.one Int64.one)) 1).
(*
ma = 0
i0 = 1
mb = 1
i = 1
j = 0

hB = 0
hA = 1 
hR = 1

Int64.testbit (Int64.add i j) i0 = 
Int64.testbit (Int64.add 1 0) 1 = false

Int64.testbit (Int64.add ma (Int64.add mb hR)) i0 =
Int64.testbit (Int64.add 0 (Int64.add 1 1)) 1 = true
*)

  pose proof (Int64.bits_not ma i0 H1) as Ha1.
  pose proof (Int64.bits_not mb i0 H1) as Hb1.
  rewrite Ha0 in Ha1.
  rewrite Hb0 in Hb1.
  simpl in *.
  
  Search(Int64.testbit (Int64.and _ _) _).
  destruct (Int64.testbit hR i0) eqn: HR0.
  - subst hR hA hB.

  Search(Int64.add _ _).
  Search(xorb _ _ = false).

  rewrite Int64.add_commut with (x := hA) in HT.
  rewrite Int64.add_assoc in HT.

  Search(Int64.and _ _).
  Search(Int64.and _ _ = Int64.zero).

  apply Int64.add_is_or in H as Hor1.
  apply Int64.add_is_or in H0 as Hor2.
  rewrite Hor1, Hor2 in HT.
  clear Hor1 Hor2.
  Search(Int64.and _ _ = Int64.zero).
    rewrite ! Int64.bits_and; try assumption.
    
  }
  rewrite Heq.
  f_equal.
  Search(Int64.testbit).
  
  apply Int64.add_is_or in H,H0.
  rewrite add_distrib_int64.
  rewrite H, H0.
  Search (Int64.or).
  Search (Int64.or (Int64.or _ _) _).
  


  rewrite Int64.not_or_and_not.
  rewrite Int64.not_or_and_not.



Qed.