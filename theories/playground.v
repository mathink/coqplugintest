Require Import TESTLIB.Tri.

Time Check 1000%nat.
(* 1000 *)
(*      : nat *)
(* Finished transaction in 0. secs (0.003837u,0.00016s) *)
Time Check 1000%nat3.
(* 1000%nat3 *)
(*      : Nat3.t *)
(* Finished transaction in 0. secs (0.000191u,5.00000000001e-06s) *)

Time Check 10000%nat.
(* 10000 *)
(*      : nat *)
(* Finished transaction in 0. secs (0.058169u,0.002563s) *)
Time Check 10000%nat3.
(* 10000%nat3 *)
(*      : Nat3.t *)
(* Finished transaction in 0. secs (0.000197u,3.99999999999e-06s) *)


Goal (3%nat) = nat3_to_nat (3%nat3).
Proof.
  now simpl.
Qed.

Goal (3%nat3) = nat_to_nat3 (3%nat).
Proof.
  now simpl.
Qed.