(* plugin test for nat *)

open Util
open Glob_term
open Libnames
open Bigint

(* utility *)
let three = of_int 3
let mult_3 n = mult three n
let mult_3_add_1 n = add (mult_3 n) one
let mult_3_add_2 n = add (mult_3 n) two
			 
       
(* to use Coq's constructor in OCaml *)
let make_dir l = Names.make_dirpath (List.map Names.id_of_string (List.rev l))
let make_kn dir mn id =
  Names.make_mind (Names.MPdot (Names.MPfile (make_dir dir), mn))
		  Names.empty_dirpath
		  (Names.label_of_id id)
let make_path dir id = Libnames.make_path (make_dir dir) id

let nat3_label = Names.mk_label "Nat3"
let nat3_module = ["TESTLIB";"Tri"]

(*
 substructure of nat3
 *)
(* 
  パスは、ファイル内のモジュール名まで含める。
  カーネルネームは、ファイル名まで。
  ということかな？
 *)
let nat3st_id = Names.id_of_string "st"
let nat3st_kn = make_kn nat3_module nat3_label nat3st_id
let nat3st_path = make_path (nat3_module@["Nat3"]) nat3st_id

let glob_nat3st = IndRef (nat3st_kn,0)

let path_of_e3 = ((nat3st_kn, 0), 1)
let path_of_t3 = ((nat3st_kn, 0), 2)
let path_of_m3 = ((nat3st_kn, 0), 3)
let path_of_m3p1 = ((nat3st_kn, 0), 4)
let path_of_m3p2 = ((nat3st_kn, 0), 5)
		     
let glob_e3 = ConstructRef path_of_e3
let glob_t3 = ConstructRef path_of_t3
let glob_m3 = ConstructRef path_of_m3
let glob_m3p1 = ConstructRef path_of_m3p1
let glob_m3p2 = ConstructRef path_of_m3p2

(* 整数を nat 型の形式に変換 *)
let int_to_nat3st dloc n =
  let ref_e3 = GRef (dloc, glob_e3) in
  let ref_t3 = GRef (dloc, glob_t3) in
  let ref_m3 = GRef (dloc, glob_m3) in
  let ref_m3p1 = GRef (dloc, glob_m3p1) in
  let ref_m3p2 = GRef (dloc, glob_m3p2) in
  let rec mk_nat3st n =
    if n = one then ref_e3
    else if n = two then ref_t3
    else let (q, r) = euclid n three in
	 let ref_c = if r = zero then ref_m3
		     else if r = one then ref_m3p1
		     else ref_m3p2 in
	 GApp (dloc, ref_c, [mk_nat3st q])
  in
  mk_nat3st n

let error_non_positive dloc =
  user_err_loc (dloc, "int_to_nat3st",
		Pp.str "Cannot Interpret a Non Positive Number.")

let interp_nat3st dloc n =
  if is_strictly_pos n then int_to_nat3st dloc n
  else error_non_positive dloc
		 
exception Non_closed_number_nat3st

let rec nat3st_to_int = function
  | GRef (_, e) when e = glob_e3 -> one
  | GRef (_, t) when t = glob_t3 -> two
  | GApp (_, GRef (_, s), [a]) when s = glob_m3 -> mult_3 (nat3st_to_int a)
  | GApp (_, GRef (_, s), [a]) when s = glob_m3p1 -> mult_3_add_1 (nat3st_to_int a)
  | GApp (_, GRef (_, s), [a]) when s = glob_m3p2 -> mult_3_add_2 (nat3st_to_int a)
  | _ -> raise Non_closed_number_nat3st

let uninterp_nat3st n =
  try
    Some (nat3st_to_int n)
  with
    Non_closed_number_nat3st -> None
	       
let _ =
  Notation.declare_numeral_interpreter
    "nat3_scope"
    (nat3st_path, nat3_module)
    interp_nat3st
    ([GRef (dummy_loc, glob_e3);
      GRef (dummy_loc, glob_t3);
      GRef (dummy_loc, glob_m3);
      GRef (dummy_loc, glob_m3p1);
      GRef (dummy_loc, glob_m3p2)],
     uninterp_nat3st,
     true)

(* 
  nat3
 *)
let nat3t_id = Names.id_of_string "t"
let nat3t_kn = make_kn nat3_module nat3_label nat3t_id
let nat3t_path = make_path (nat3_module@["Nat3"]) nat3t_id

let glob_nat3t = IndRef (nat3t_kn,0)

let path_of_z3 = ((nat3t_kn, 0), 1)
let path_of_s3 = ((nat3t_kn, 0), 2)

let glob_z3 = ConstructRef path_of_z3
let glob_s3 = ConstructRef path_of_s3

let int_to_nat3t dloc n =
  let ref_z3 = GRef (dloc, glob_z3) in
  let ref_s3 = GRef (dloc, glob_s3) in
  let rec mk_nat3t n =
    if n = zero then ref_z3
    else GApp (dloc, ref_s3, [int_to_nat3st dloc n])
  in
  mk_nat3t n

let error_negative dloc = 
  user_err_loc (dloc, "int_to_nat3t",
		Pp.str "Cannot Interpret a Negative Number.")

let interp_nat3t dloc n =
  if is_pos_or_zero n then int_to_nat3t dloc n
  else error_negative dloc

exception Non_closed_number_nat3t

let rec nat3t_to_int = function
  | GApp (_, GRef (_, s), [a]) when s = glob_s3 -> nat3st_to_int a
  | GRef (_, z) when z = glob_z3 -> zero
  | _ -> raise Non_closed_number_nat3t

let uninterp_nat3t p =
  try
    Some (nat3t_to_int p)
  with
    Non_closed_number_nat3t -> None

let _ =
  Notation.declare_numeral_interpreter
    "nat3_scope"
    (nat3t_path, nat3_module)
    interp_nat3t
    ([GRef (dummy_loc, glob_z3);
      GRef (dummy_loc, glob_s3)],
     uninterp_nat3t,
     true)
;;

       
