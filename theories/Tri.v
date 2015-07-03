Declare ML Module "nat3_interp_plugin".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.

Delimit Scope nat3_scope with nat3.

Module Nat3.
  Inductive st :=
  | e3
  | t3
  | m3 (n: st)
  | m3p1 (n: st)
  | m3p2 (n: st).

  Inductive t :=
  | z3
  | s3 (n: st).

  Bind Scope nat3_scope with t st.
End Nat3.

Definition nat3 := Nat3.t.
Definition nat3st := Nat3.st.

Section props.
  Import Nat3.
  Fixpoint nat3st_to_nat (n: nat3st): nat :=
    match n with
      | e3 => 1
      | t3 => 2
      | m3 p => 3 * nat3st_to_nat p
      | m3p1 p => S (3 * nat3st_to_nat p)
      | m3p2 p => S (S (3 * nat3st_to_nat p))
    end.

  Fixpoint nat3_to_nat (n: nat3): nat :=
    match n with
      | z3 => 0
      | s3 p => nat3st_to_nat p
    end.

  Goal nat3_to_nat (s3 (m3p2 (m3p1 (m3 (m3p1 t3))))) = 194.
  Proof. reflexivity. Qed.

  Fixpoint nat3st_succ (n: nat3st): nat3st :=
    match n with
      | e3 => t3
      | t3 => m3 e3
      | m3 p => m3p1 p
      | m3p1 p => m3p2 p
      | m3p2 p => m3 (nat3st_succ p)
    end.

  Fixpoint nat3_succ (n: nat3): nat3 :=
    match n with
      | z3 => s3 e3
      | s3 p => s3 (nat3st_succ p)
    end.

  Fixpoint nat_to_nat3 (n: nat): nat3 :=
    match n with
      | 0 => z3
      | S p => nat3_succ (nat_to_nat3 p)
    end.

  Lemma nat3st_succ_S:
    forall (n: nat3st),
      nat3st_to_nat (nat3st_succ n) = S (nat3st_to_nat n).
  Proof.
    induction n as [| |n IHn| n IHn| n IHn]; try now simpl.
    simpl.
    repeat rewrite <- plus_n_O.
    repeat rewrite IHn.
    simpl.
    repeat rewrite <- plus_n_Sm.
    reflexivity.
  Qed.
      
  Lemma nat3_succ_S:
    forall (n: nat3),
      nat3_to_nat (nat3_succ n) = S (nat3_to_nat n).
  Proof.
    destruct n as [| n]; try now simpl.
    now apply nat3st_succ_S.
  Qed.
  
  Lemma nat_eq_nat3:
    forall (n: nat),
      nat3_to_nat (nat_to_nat3 n) = n.
  Proof.
    induction n as [| n IHn].
    - simpl.
      reflexivity.
    - simpl.
      now rewrite nat3_succ_S, IHn.
  Qed.

  Definition tm3 (n: nat3): nat3 :=
    match n with
      | z3 => z3
      | s3 n => s3 (m3 n)
    end.
  
  Definition tm3p1 (n: nat3): nat3 :=
    match n with
      | z3 => s3 e3
      | s3 n => s3 (m3p1 n)
    end.
  
  Definition tm3p2 (n: nat3): nat3 :=
    match n with
      | z3 => s3 t3
      | s3 n => s3 (m3p2 n)
    end.
  
  Lemma nat_to_nat3_m3:
    forall (n: nat),
      nat_to_nat3 (3 * n) = tm3 (nat_to_nat3 n).
  Proof.
    induction n as [| n IHn]; try now simpl.
    simpl in *.
    rewrite <- plus_n_O in *.
    repeat rewrite <- plus_n_Sm; simpl.
    rewrite IHn; simpl.
    clear IHn.
    remember (nat_to_nat3 n) as m; clear n Heqm.
    destruct m; try now simpl.
  Qed.
  
  Lemma nat_to_nat3_m3p1:
    forall (n: nat),
      nat_to_nat3 (S (3 * n)) = tm3p1 (nat_to_nat3 n).
  Proof.
    induction n as [| n IHn]; try now simpl.
    simpl in *.
    repeat rewrite <- plus_n_Sm; simpl.
    repeat rewrite <- plus_n_O in *.
    rewrite IHn; simpl.
    clear IHn.
    remember (nat_to_nat3 n) as m; clear n Heqm.
    destruct m; try now simpl.
  Qed.
  
  Lemma nat_to_nat3_m3p2:
    forall (n: nat),
      nat_to_nat3 (S (S (3 * n))) = tm3p2 (nat_to_nat3 n).
  Proof.
    induction n as [| n IHn]; try now simpl.
    simpl in *.
    repeat rewrite <- plus_n_Sm; simpl.
    repeat rewrite <- plus_n_O in *.
    rewrite IHn; simpl.
    clear IHn.
    remember (nat_to_nat3 n) as m; clear n Heqm.
    destruct m; try now simpl.
  Qed.
  
  Lemma t_eq_nat:
    forall (n: nat3),
      nat_to_nat3 (nat3_to_nat n) = n.
  Proof.
    intros [| n]; try now simpl.
    induction n as [| | n IHn| n IHn| n IHn]; try now simpl.
    - simpl in *.
      generalize (nat_to_nat3_m3 (nat3st_to_nat n)); simpl.      
      rewrite <- plus_n_O.
      intro H; rewrite H.
      now rewrite IHn.
    - simpl in *.
      generalize (nat_to_nat3_m3p1 (nat3st_to_nat n)); simpl.      
      rewrite <- plus_n_O.
      intro H; rewrite H.
      now rewrite IHn.
    - simpl in *.
      generalize (nat_to_nat3_m3p2 (nat3st_to_nat n)); simpl.      
      rewrite <- plus_n_O.
      intro H; rewrite H.
      now rewrite IHn.
  Qed.
End props.

Coercion nat3_to_nat: nat3 >-> nat.