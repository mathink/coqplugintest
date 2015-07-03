(* plugin test for nat *)

open Pcoq
open Pp
open Util
open Names
open Coqlib
open Glob_term
open Libnames
open Bigint
open Coqlib
open Notation
open Pp
open Util
open Names

(* to use Coq's constructor in OCaml *)
let make_kn dir id = Libnames.encode_mind dir id
let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
			      
let nat_module_name = ["TESTLIB";"Nat"]
let nat_module = make_dir nat_module_name

let nat_kn = make_kn nat_module (id_of_string "Nat")
let nat_path = Libnames.make_path nat_module (id_of_string "Nat")

let glob_Nat = IndRef (nat_kn,0)

let path_of_Zero = ((nat_kn, 0), 1)
let path_of_Succ = ((nat_kn, 0), 2)
let glob_Zero = ConstructRef path_of_Zero
let glob_Succ = ConstructRef path_of_Succ
		     
(*  *)
let threshold = of_int 100
       
(* 整数を nat 型の形式に変換 *)
let int_to_Nat dloc n =
  if is_pos_or_zero n then begin
      if less_than threshold n then
	Flags.if_warn msg_warning (strbrk "Too Large Number");
      let ref_Zero = GRef (dloc, glob_Zero) in
      let ref_Succ = GRef (dloc, glob_Succ) in
      let rec mk_Nat acc n =
	if n <> zero then
	  mk_Nat (GApp (dloc, ref_Succ, [acc])) (sub_1 n)
	else
	  acc
      in
      mk_Nat ref_Zero n
    end
  else
    user_err_loc (dloc, "int_to_Nat",
		  str "Cannot Interpret a Negative Number.")


exception Non_closed_number_Nat

let rec nat_to_int = function
  | GApp (_, GRef (_, s), [a]) when s = glob_Succ -> add_1 (nat_to_int a)
  | GRef (_, z) when z = glob_Zero -> zero
  | _ -> raise Non_closed_number_Nat

let uninterp_Nat p =
  try
    Some (nat_to_int p)
  with
    Non_closed_number_Nat -> None

let _ =
  Notation.declare_numeral_interpreter
    "Nat_scope"
    (nat_path, ["TESTLIB";"Nat"])
    int_to_Nat
    ([GRef (dummy_loc, glob_Succ); GRef (dummy_loc, glob_Zero)],
     uninterp_Nat,
     true)
;;

       
