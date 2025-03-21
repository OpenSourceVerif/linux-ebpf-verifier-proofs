From Coq Require Import ZArith Bool Lia.

Lemma Zodd_b2z : forall b, Z.odd (Z.b2z b) = b.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma decomp : forall x,
      (x = 2 * (x / 2) + Z.b2z (Z.odd x))%Z.
  Proof.
    intros.
    rewrite <- Z.bit0_odd.
    rewrite Z.bit0_mod.
    apply Z_div_mod_eq_full.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma add_shift : forall a b,
      ((a + b) / 2 =
         (a / 2 + (b / 2) + (Z.b2z (Z.odd a && Z.odd b))))%Z.
  Proof.
    intros.
    rewrite! Zodd_mod.
    destruct (Zeq_bool (a mod 2) 1 && Zeq_bool (b mod 2) 1) eqn:LB.
    - simpl.
      rewrite andb_true_iff in LB.
      destruct LB as (LB1 & LB2).
      apply Zeq_bool_eq in LB1.
      apply Zeq_bool_eq in LB2.
      lia.
    - simpl.
      rewrite andb_false_iff  in LB.
      destruct LB.
      apply Zeq_bool_neq in H.
      lia.
      apply Zeq_bool_neq in H.
      lia.
  Qed.

  Lemma b2z_div2 : forall b,
      (Z.b2z b / 2 = 0)%Z.
  Proof.
    destruct b; reflexivity.
  Qed.