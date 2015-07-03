Declare ML Module "nat_interp_plugin".

(* natural number *)
Inductive Nat :=
| Zero: Nat
| Succ: Nat -> Nat.

Delimit Scope Nat_scope with Nat.
Bind Scope Nat_scope with Nat.

Arguments Succ _%Nat.
