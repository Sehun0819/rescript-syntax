open Parsetree
open Fuzz_utils

let genConstant () =
  match Rand.choose 4 with
  | 0 -> Pconst_integer ("3", None)
  | 1 -> Pconst_char 'a'
  | 2 -> Pconst_string ("abc", None)
  | 3 -> Pconst_float ("1.0", None)
  | _ -> assert false

let genExpressionDesc () =
  Pexp_constant (genConstant ())

let genExpression () =
  {
    pexp_desc = genExpressionDesc ();
    pexp_loc = emptyLoc;
    pexp_attributes = [];
  }

let genStructureItemDesc () =
  Pstr_eval (genExpression (), [])

let genStructureItem () =
  {
    pstr_desc = genStructureItemDesc ();
    pstr_loc = emptyLoc;
  }

let genStructure () =
  Rand.genList genStructureItem

let genSignature () = []