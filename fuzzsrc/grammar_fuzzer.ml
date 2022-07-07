open Parsetree
open Fuzz_utils

(** Generate Parsetree.constant **)

let genInt () =
  (* let sign = if Rand.randBool () then "+" else "=" in *)
  let n = Rand.randInt () in
  let suffix =
    if Rand.randBool () then Some (Rand.amongv ['l'; 'L'; 'n']) else None
  in
  Pconst_integer (Int.to_string n, suffix)

let genChar () = Pconst_char (Rand.amongv char_literals)

let genStr () =
  let len = Rand.randInt ~bound:100 () in
  let s = ref "" in
  for _i = 1 to len do
    let c = Rand.amongv char_literals in
    s := (Char.escaped c) ^ !s
  done;
  Pconst_string (!s, None) (* TODO: what is rhs? *)

let genFloat () =
  (* let sign = if Rand.randBool () then "+" else "=" in *)
  let n = Rand.randFloat () in
  Pconst_float (Float.to_string n, None)

let genConstant () = Rand.amongf [genInt; genChar; genStr; genFloat]




let genExpressionDesc () =
  Pexp_constant (genConstant ())

let genExpression () =
  {
    pexp_desc = genExpressionDesc ();
    pexp_loc = Location.none;
    pexp_attributes = [];
  }

let genStructureItemDesc () =
  Pstr_eval (genExpression (), [])

let genStructureItem () =
  {
    pstr_desc = genStructureItemDesc ();
    pstr_loc = Location.none;
  }

let genStructure () =
  Rand.genList genStructureItem

let genSignature () = []