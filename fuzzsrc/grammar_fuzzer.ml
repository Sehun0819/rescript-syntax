open Asttypes
open Longident
open Parsetree
open Rand
open Fuzz_utils

(** Generate Parsetree.constant **)

let genInt () =
  (* let sign = if Rand.randBool () then "+" else "=" in *)
  let n = Rand.randInt () in
  let suffix =
    if Rand.randBool () then Some (Rand.amongv ['l'; 'L'; 'n']) else None
  in
  Int.to_string n, suffix

let genChar () = Rand.amongv char_literals

let genString () =
  let len = Rand.randInt ~bound:100 () in
  let s = ref "" in
  for _i = 1 to len do
    let c = Rand.amongv char_literals in
    s := (Char.escaped c) ^ !s
  done;
  !s (* TODO: what is rhs? *)

let genFloat () =
  (* let sign = if Rand.randBool () then "+" else "=" in *)
  let n = Rand.randFloat () in
  Float.to_string n

let genConstant () =
  match Rand.randInt ~bound:4 () with
  | 0 ->
    let n, suffix = genInt () in
    Pconst_integer (n, suffix)
  | 1 -> Pconst_char (genChar ())
  | 2 -> Pconst_string (genString (), None)
  | 3 -> Pconst_float (genFloat (), None)
  | _ -> assert false

let genArglabel () =
  match Rand.randInt ~bound:3 () with
  | 0 -> Nolabel
  | 1 -> Labelled (genString ())
  | 2 -> Optional (genString ())
  | _ -> assert false

let rec genLongident () =
  match Rand.randInt ~bound:3 () with
  | 0 -> Lident (genString ())
  | 1 -> Ldot (genLongident (), genString())
  | 2 -> Lapply (genLongident (), genLongident ())
  | _ -> assert false

let genLoc genA () =
  {
    txt = genA ();
    loc = Location.none;
  }

let genRecFlag () = if Rand.randBool () then Nonrecursive else Recursive

let genDirectionFlag () = if Rand.randBool () then Upto else Downto

let genPrivateFlag () = if Rand.randBool () then Private else Public

let genMutableFlag () = if Rand.randBool () then Immutable else Mutable

let genVirtualFlag () = if Rand.randBool () then Virtual else Concrete

let genOverrideFlag () = if Rand.randBool () then Override else Fresh

let genClosedFlag () = if Rand.randBool () then Closed else Open

let genVariance () =
  match Rand.randInt ~bound:3 () with
  | 0 -> Covariant
  | 1 -> Contravariant
  | 2 -> Invariant
  | _ -> assert false

let rec genAttribute () =
  let l = {
    txt = genString ();
    loc = Location.none;
  } in
  let p = genPayload () in
  (l, p)

and genExtension () = genAttribute ()

and genAttributes () = Rand.genList genAttribute

and genPayload () =
  match Rand.randInt ~bound:4 () with
  | 0 -> PStr (genStructure ())
  | 1 -> PSig (genSignature ())
  | 2 -> PTyp (genCoretype ())
  | 3 ->
    let o = if Rand.randBool () then Some (genExpression ()) else None in
    PPat (genPattern (), o)
  | _ -> assert false

and genCoretype () =
  {
    ptyp_desc = genCoretypeDesc ();
    ptyp_loc = Location.none;
    ptyp_attributes = genAttributes ();
  }

and genCoretypeDesc () =
  match Rand.randInt ~bound:12 () with
  | 0 -> Ptyp_any
  | 1 -> Ptyp_var (genString ())
  | 2 -> Ptyp_arrow (genArglabel (), genCoretype (), genCoretype ())
  | 3 -> Ptyp_tuple (genList genCoretype)
  | 4 -> Ptyp_constr (genLoc genLongident (), genList genCoretype)
  | 5 -> Ptyp_object (genList genObjectfield, genClosedFlag ())
  | 6 -> Ptyp_class (genLoc genLongident (), genList genCoretype)
  | 7 -> Ptyp_alias (genCoretype (), genString ())
  | 8 ->
    let o = if Rand.randBool () then Some (genList genString) else None in
    Ptyp_variant (genList genRowfield, genClosedFlag (), o)
  | 9 -> Ptyp_poly (genList (genLoc genString), genCoretype ())
  | 10 -> Ptyp_package (genPackagetype ())
  | 11 -> Ptyp_extension (genExtension ())
  | _ -> assert false

and genPackagetype () =
  let genLiCt () = (genLoc genLongident (), genCoretype ()) in
  genLoc genLongident (), genList genLiCt

and genRowfield () =
  if Rand.randBool () then
    Rtag (genLoc genString (), genAttributes (), Rand.randBool (), genList genCoretype)
  else
    Rinherit (genCoretype ())

and genObjectfield () =
  if Rand.randBool () then
    Otag (genLoc genString (), genAttributes (), genCoretype ())
  else
    Oinherit (genCoretype ())

and genPattern () =
  {
    ppat_desc = genPatternDesc ();
    ppat_loc = Location.none;
    ppat_attributes = genAttributes ();
  }

and genPatternDesc () =
  match Rand.randInt ~bound:18 () with
  | 0 -> Ppat_any
  | 1 -> Ppat_var (genLoc genString ())
  | 2 -> Ppat_alias (genPattern (), genLoc genString ())
  | 3 -> Ppat_constant (genConstant ())
  | 4 -> Ppat_interval (genConstant (), genConstant ())
  | 5 -> Ppat_tuple (genList genPattern)
  | 6 -> 
    let o = if Rand.randBool () then Some (genPattern ()) else None in
    Ppat_construct (genLoc genLongident (), o)
  | 7 ->
    let o = if Rand.randBool () then Some (genPattern ()) else None in
    Ppat_variant (genString (), o)
  | 8 ->
    let genLiPt () = (genLoc genLongident (), genPattern ()) in
    Ppat_record (genList genLiPt, genClosedFlag ())
  | 9 -> Ppat_array (genList genPattern)
  | 10 -> Ppat_or (genPattern (), genPattern ())
  | 11 -> Ppat_constraint (genPattern (), genCoretype ())
  | 12 -> Ppat_type (genLoc genLongident ())
  | 13 -> Ppat_lazy (genPattern ())
  | 14 -> Ppat_unpack (genLoc genString ())
  | 15 -> Ppat_exception (genPattern ())
  | 16 -> Ppat_extension (genExtension ())
  | 17 -> Ppat_open (genLoc genLongident (), genPattern ())
  | _ -> assert false

and genExpression () =
  {
    pexp_desc = genExpressionDesc ();
    pexp_loc = Location.none;
    pexp_attributes = genAttributes ();
  }

and genExpressionDesc () =
  match Rand.randInt ~bound:36 () with
  | 0 -> Pexp_ident (genLoc genLongident ())
  | 1 -> Pexp_constant (genConstant ())
  | 2 -> Pexp_let (genRecFlag (), genList genValuebinding, genExpression ())
  | 3 -> Pexp_function (genList genCase)
  | 4 -> Pexp_fun (genArglabel (), genOption genExpression, genPattern (), genExpression ())
  | 5 ->
    let genAlExp () = genArglabel (), genExpression () in
    Pexp_apply (genExpression (), genList genAlExp)
  | 6 -> Pexp_match (genExpression (), genList genCase)
  | 7 -> Pexp_try (genExpression (), genList genCase)
  | 8 -> Pexp_tuple (genList genExpression)
  | 9 -> Pexp_construct (genLoc genLongident (), genOption genExpression)
  | 10 -> Pexp_variant (genString (), genOption genExpression)
  | 11 -> 
    let genLiExp () = genLoc genLongident (), genExpression () in
    Pexp_record (genList genLiExp, genOption genExpression)
  | 12 -> Pexp_field (genExpression (), genLoc genLongident ())
  | 13 -> Pexp_setfield (genExpression (), genLoc genLongident (), genExpression ())
  | 14 -> Pexp_array (genList genExpression)
  | 15 -> Pexp_ifthenelse (genExpression (), genExpression (), genOption genExpression)
  | 16 -> Pexp_sequence (genExpression (), genExpression ())
  | 17 -> Pexp_while (genExpression (), genExpression ())
  | 18 -> Pexp_for (genPattern (), genExpression (), genExpression (), genDirectionFlag (), genExpression ())
  | 19 -> Pexp_constraint (genExpression (), genCoretype ())
  | 20 -> Pexp_coerce (genExpression (), genOption genCoretype, genCoretype ())
  | 21 -> Pexp_send (genExpression (), genLoc genString ())
  | 22 -> Pexp_new (genLoc genLongident ())
  | 23 -> Pexp_setinstvar (genLoc genString (), genExpression ())
  | 24 ->
    let genLlExp () = genLoc genString (), genExpression () in
    Pexp_override (genList genLlExp)
  | 25 -> Pexp_letmodule (genLoc genString (), genModuleExpr (), genExpression ())
  | 26 -> Pexp_letexception (genExtensionConstructor (), genExpression ())
  | 27 -> Pexp_assert (genExpression ())
  | 28 -> Pexp_lazy (genExpression ())
  | 29 -> Pexp_poly (genExpression (), genOption genCoretype)
  | 30 -> Pexp_object (genClassStructure ())
  | 31 -> Pexp_newtype (genLoc genString (), genExpression ())
  | 32 -> Pexp_pack (genModuleExpr ())
  | 33 -> Pexp_open (genOverrideFlag (), genLoc genLongident (), genExpression ())
  | 34 -> Pexp_extension (genExtension ())
  | 35 -> Pexp_unreachable
  | _ -> assert false

and genCase () =
  {
    pc_lhs = genPattern ();
    pc_guard = genOption genExpression;
    pc_rhs = genExpression ();
  }

and genValueDesc () =
  {
    pval_name = genLoc genString ();
    pval_type = genCoretype ();
    pval_prim = genList genString;
    pval_attributes = genAttributes ();
    pval_loc = Location.none;
  }

and genTypeDecl () =
  let genCtVar () = genCoretype (), genVariance () in
  let genCtCtLoc () = genCoretype (), genCoretype (), Location.none in
  {
    ptype_name = genLoc genString ();
    ptype_params = genList genCtVar;
    ptype_cstrs = genList genCtCtLoc;
    ptype_kind = genTypeKind ();
    ptype_private = genPrivateFlag ();
    ptype_manifest = genOption genCoretype;
    ptype_attributes = genAttributes ();
    ptype_loc = Location.none;
  }

and genTypeKind () =
  match Rand.randInt ~bound:4 () with
  | 0 -> Ptype_abstract
  | 1 -> Ptype_variant (genList genConstructorDecl)
  | 2 -> Ptype_record (genList genLabelDecl)
  | 3 -> Ptype_open
  | _ -> assert false

and genLabelDecl () =
  {
    pld_name = genLoc genString ();
    pld_mutable = genMutableFlag ();
    pld_type = genCoretype ();
    pld_loc = Location.none;
    pld_attributes = genAttributes ();
  }

and genConstructorDecl () =
  {
    pcd_name = genLoc genString ();
    pcd_args = genConstructorArgs ();
    pcd_res = genOption genCoretype;
    pcd_loc = Location.none;
    pcd_attributes = genAttributes ();
  }

and genConstructorArgs () =
  if Rand.randBool () then
    Pcstr_tuple (genList genCoretype)
  else
    Pcstr_record (genList genLabelDecl)

and genTypeExtension () =
  let genCtVar () = genCoretype (), genVariance () in
  {
    ptyext_path = genLoc genLongident ();
    ptyext_params = genList genCtVar;
    ptyext_constructors = genList genExtensionConstructor;
    ptyext_private = genPrivateFlag ();
    ptyext_attributes = genAttributes ();
  }

and genExtensionConstructor () =
  {
    pext_name = genLoc genString ();
    pext_kind = genExtensionConstructorKind ();
    pext_loc = Location.none;
    pext_attributes = genAttributes ();
  }

and genExtensionConstructorKind () =
  if Rand.randBool () then
    Pext_decl (genConstructorArgs (), genOption genCoretype)
  else
    Pext_rebind (genLoc genLongident ())

and genClassType () =
  {
    pcty_desc = genClassTypeDesc ();
    pcty_loc = Location.none;
    pcty_attributes = genAttributes ();
  }

and genClassTypeDesc () =
  match Rand.randInt ~bound:5 () with
  | 0 -> Pcty_constr (genLoc genLongident (), genList genCoretype)
  | 1 -> Pcty_signature (genClassSignature ())
  | 2 -> Pcty_arrow (genArglabel (), genCoretype (), genClassType ())
  | 3 -> Pcty_extension (genExtension ())
  | 4 -> Pcty_open (genOverrideFlag (), genLoc genLongident (), genClassType ())
  | _ -> assert false

and genClassSignature () =
  {
    pcsig_self = genCoretype ();
    pcsig_fields = genList genClassTypeField;
  }

and genClassTypeField () =
  {
    pctf_desc = genClassTypeFieldDesc ();
    pctf_loc = Location.none;
    pctf_attributes = genAttributes ();
  }

and genClassTypeFieldDesc () =
  match Rand.randInt ~bound:6 () with
  | 0 -> Pctf_inherit (genClassType ())
  | 1 -> Pctf_val (genLoc genString (), genMutableFlag (), genVirtualFlag (), genCoretype ())
  | 2 -> Pctf_method (genLoc genString (), genPrivateFlag (), genVirtualFlag (), genCoretype ())
  | 3 -> Pctf_constraint (genCoretype (), genCoretype ())
  | 4 -> Pctf_attribute (genAttribute ())
  | 5 -> Pctf_extension (genExtension ())
  | _ -> assert false

and genClassInfos genExpr =
  let genCtVar () = genCoretype (), genVariance () in
  {
    pci_virt = genVirtualFlag ();
    pci_params = genList genCtVar;
    pci_name = genLoc genString ();
    pci_expr = genExpr ();
    pci_loc = Location.none;
    pci_attributes = genAttributes ();
  }

and genClassDesc () = genClassInfos genClassType

and genClassTypeDecl () = genClassInfos genClassType

and genClassExpr () =
  {
    pcl_desc = genClassExprDesc ();
    pcl_loc = Location.none;
    pcl_attributes = genAttributes ();
  }

and genClassExprDesc () =
  match Rand.randInt ~bound:8 () with
  | 0 -> Pcl_constr (genLoc genLongident (), genList genCoretype)
  | 1 -> Pcl_structure (genClassStructure ())
  | 2 -> Pcl_fun (genArglabel (), genOption genExpression, genPattern (), genClassExpr ())
  | 3 ->
    let genAlExp () = genArglabel (), genExpression () in
    Pcl_apply (genClassExpr (), genList genAlExp)
  | 4 -> Pcl_let (genRecFlag (), genList genValuebinding, genClassExpr ())
  | 5 -> Pcl_constraint (genClassExpr (), genClassType ())
  | 6 -> Pcl_extension (genExtension ())
  | 7 -> Pcl_open (genOverrideFlag (), genLoc genLongident (), genClassExpr ())
  | _ -> assert false

and genClassStructure () =
  {
    pcstr_self = genPattern ();
    pcstr_fields = genList genClassField;
  }

and genClassField () =
  {
    pcf_desc = genClassFieldDesc ();
    pcf_loc = Location.none;
    pcf_attributes = genAttributes ();
  }

and genClassFieldDesc () =
  match Rand.randInt ~bound:7 () with
  | 0 -> Pcf_inherit (genOverrideFlag (), genClassExpr (), genOption (genLoc genString))
  | 1 -> Pcf_val (genLoc genString (), genMutableFlag (), genClassFieldKind ())
  | 2 -> Pcf_method (genLoc genString (), genPrivateFlag (), genClassFieldKind ())
  | 3 -> Pcf_constraint (genCoretype (), genCoretype ())
  | 4 -> Pcf_initializer (genExpression ())
  | 5 -> Pcf_attribute (genAttribute ())
  | 6 -> Pcf_extension (genExtension ())
  | _ -> assert false

and genClassFieldKind () =
  if Rand.randBool () then
    Cfk_virtual (genCoretype ())
  else
    Cfk_concrete (genOverrideFlag (), genExpression ())

and genClassDecl () =
  let genCtVar () = genCoretype (), genVariance () in
  {
    pci_virt = genVirtualFlag ();
    pci_params = genList genCtVar;
    pci_name = genLoc genString ();
    pci_expr = genClassExpr ();
    pci_loc = Location.none;
    pci_attributes = genAttributes ();
  }

and genModuleType () =
  {
    pmty_desc = genModuleTypeDesc ();
    pmty_loc = Location.none;
    pmty_attributes = genAttributes ();
  }

and genModuleTypeDesc () =
  match Rand.randInt ~bound:7 () with
  | 0 -> Pmty_ident (genLoc genLongident ())
  | 1 -> Pmty_signature (genSignature ())
  | 2 -> Pmty_functor (genLoc genString (), genOption genModuleType, genModuleType ())
  | 3 -> Pmty_with (genModuleType (), genList genWithConstraint)
  | 4 -> Pmty_typeof (genModuleExpr ())
  | 5 -> Pmty_extension (genExtension ())
  | 6 -> Pmty_alias (genLoc genLongident ())
  | _ -> assert false

and genSignature () = genList genSignatureItem

and genSignatureItem () =
  {
    psig_desc = genSignatureItemDesc ();
    psig_loc = Location.none;
  }

and genSignatureItemDesc () =
  match Rand.randInt ~bound:13 () with
  | 0 -> Psig_value (genValueDesc ())
  | 1 -> Psig_type (genRecFlag (), genList genTypeDecl)
  | 2 -> Psig_typext (genTypeExtension ())
  | 3 -> Psig_exception (genExtensionConstructor ())
  | 4 -> Psig_module (genModuleDecl ())
  | 5 -> Psig_recmodule (genList genModuleDecl)
  | 6 -> Psig_modtype (genModuleTypeDecl ())
  | 7 -> Psig_open (genOpenDesc ())
  | 8 -> Psig_include (genIncludeDesc ())
  | 9 -> Psig_class (genList genClassDesc)
  | 10 -> Psig_class_type (genList genClassTypeDecl)
  | 11 -> Psig_attribute (genAttribute ())
  | 12 -> Psig_extension (genExtension (), genAttributes ())
  | _ -> assert false
 
and genModuleDecl () =
  {
    pmd_name = genLoc genString ();
    pmd_type = genModuleType ();
    pmd_attributes = genAttributes ();
    pmd_loc = Location.none;
  }

and genModuleTypeDecl () =
  {
    pmtd_name = genLoc genString ();
    pmtd_type = genOption genModuleType;
    pmtd_attributes = genAttributes ();
    pmtd_loc = Location.none;
  }

and genOpenDesc () =
  {
    popen_lid = genLoc genLongident ();
    popen_override = genOverrideFlag ();
    popen_loc = Location.none;
    popen_attributes = genAttributes ();
  }

(* and genIncludeInfos genMod =
  {
    pincl_mod = genMod ();
    pincl_loc = Location.none;
    pincl_attributes = genAttributes ();
  } *)

and genIncludeDesc () =
  {
    pincl_mod = genModuleType ();
    pincl_loc = Location.none;
    pincl_attributes = genAttributes ();
  }

and genIncludeDecl () =
  {
    pincl_mod = genModuleExpr ();
    pincl_loc = Location.none;
    pincl_attributes = genAttributes ();
  }

and genWithConstraint () =
  match Rand.randInt ~bound:4 () with
  | 0 -> Pwith_type (genLoc genLongident (), genTypeDecl ())
  | 1 -> Pwith_module (genLoc genLongident (),genLoc genLongident ())
  | 2 -> Pwith_typesubst (genLoc genLongident (), genTypeDecl ())
  | 3 -> Pwith_modsubst (genLoc genLongident (),genLoc genLongident ())
  | _ -> assert false

and genModuleExpr () =
  {
    pmod_desc = genModuleExprDesc ();
    pmod_loc = Location.none;
    pmod_attributes = genAttributes ();
  }

and genModuleExprDesc () =
  match Rand.randInt ~bound:7 () with
  | 0 -> Pmod_ident (genLoc genLongident ())
  | 1 -> Pmod_structure (genStructure ())
  | 2 -> Pmod_functor (genLoc genString (), genOption genModuleType, genModuleExpr ())
  | 3 -> Pmod_apply (genModuleExpr (), genModuleExpr ())
  | 4 -> Pmod_constraint (genModuleExpr (), genModuleType ())
  | 5 -> Pmod_unpack (genExpression ())
  | 6 -> Pmod_extension (genExtension ())
  | _ -> assert false

and genStructure () = genList genStructureItem

and genStructureItem () =
  {
    pstr_desc = genStructureItemDesc ();
    pstr_loc = Location.none;
  }

and genStructureItemDesc () =
  match Rand.randInt ~bound:15 () with
  | 0 -> Pstr_eval (genExpression (), genAttributes ())
  | 1 -> Pstr_value (genRecFlag (), genList genValuebinding)
  | 2 -> Pstr_primitive (genValueDesc ())
  | 3 -> Pstr_type (genRecFlag (), genList genTypeDecl)
  | 4 -> Pstr_typext (genTypeExtension ())
  | 5 -> Pstr_exception (genExtensionConstructor ())
  | 6 -> Pstr_module (genModuleBinding ())
  | 7 -> Pstr_recmodule (genList genModuleBinding)
  | 8 -> Pstr_modtype (genModuleTypeDecl ())
  | 9 -> Pstr_open (genOpenDesc ())
  | 10 -> Pstr_class (genList genClassDecl)
  | 11 -> Pstr_class_type (genList genClassTypeDecl)
  | 12 -> Pstr_include (genIncludeDecl ())
  | 13 -> Pstr_attribute (genAttribute ())
  | 14 -> Pstr_extension (genExtension (), genAttributes ())
  | _ -> assert false

and genValuebinding () =
  {
    pvb_pat = genPattern ();
    pvb_expr = genExpression ();
    pvb_attributes = genAttributes();
    pvb_loc = Location.none;
  }

and genModuleBinding () =
  {
    pmb_name = genLoc genString ();
    pmb_expr = genModuleExpr ();
    pmb_attributes = genAttributes ();
    pmb_loc = Location.none;
  }