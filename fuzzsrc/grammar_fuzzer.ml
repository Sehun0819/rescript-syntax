open Asttypes
open Longident
open Parsetree
open Rand
open Fuzz_utils

(** Generate Parsetree.constant **)

let numNonterminal = ref 0
let addNonterminal () = numNonterminal := 1 + !numNonterminal; print_endline ("num nonterminals: " ^ (string_of_int !numNonterminal))
let threshold = 6

let among (l1: 'a Lazy.t list) (l2: 'a Lazy.t list) : 'a =
  let l = if !numNonterminal >= threshold then l1 else l1 @ l2 in
  let size = List.length l in
  let pick = List.nth l (randInt ~bound:size ()) in
  Lazy.force pick

let genList f =
  let lenMax = if !numNonterminal >= threshold then 1 else 5 in
  let len = randInt ~bound:lenMax (); in
  let len = if len = 0 then 1 else len in
  let l = ref [] in
  for _i = 1 to len do
    l := f ():: !l;
  done;
  !l

let genInt () =
  let n = Rand.randInt () in
  let suffix =
    if Rand.randBool () then Some (Rand.amongv ['l'; 'L'; 'n']) else None
  in
  Int.to_string n, suffix

let genChar () = Rand.amongv char_literals

let numString = ref 0
let genString () =
  let n = !numString in
  numString := 1 + n;
  "random_string_" ^ (string_of_int n)

let numIdentCap = ref 0
let genIdentCapital () =
  let n = !numIdentCap in
  numIdentCap := 1 + n;
  "Ident_" ^ (string_of_int n)

let numIdent = ref 0
let genIdent () =
  let n = !numIdent in
  numIdent := 1 + n;
  "ident_" ^ (string_of_int n)

let genFloat () =
  (* let sign = if Rand.randBool () then "+" else "=" in *)
  let n = Rand.randFloat () in
  Float.to_string n

let genConstant () =
  among [
    lazy (let n, suffix = genInt () in
          Pconst_integer (n, suffix));
    lazy (Pconst_char (genChar ()));
    lazy (Pconst_string (genString (), None));
    lazy (Pconst_float (genFloat (), None));
  ] []

let genArglabel () =
  among [
    lazy Nolabel;
    lazy (Labelled (genString ()));
    lazy (Optional (genString ()));
  ] []

let rec genLongident () =
  addNonterminal ();
  among [
    lazy (Lident (genIdent ()));
  ] [
    lazy (Ldot (genLongident (), genIdent ()));
    lazy (Lapply (genLongident (), genLongident ()));
  ]

let genLongidentCapital () =
  addNonterminal ();
  among [
    lazy (Lident (genIdentCapital ()));
  ] [] (* [
    lazy (Ldot (genLongident (), genString ()));
    lazy (Lapply (genLongident (), genLongident ()));
  ] *)

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
  among [
    lazy (Covariant);
    lazy (Contravariant);
    lazy (Invariant);
  ] []

let rec genAttribute () =
  let l = {
    txt = genIdent ();
    loc = Location.none;
  } in
  let p = genPayload () in
  (l, p)

and genExtension () = genAttribute ()

(* and genAttributes () = Rand.genList genAttribute *)
and genAttributes () = [];

and genPayload () =
  addNonterminal ();
  among [
    lazy (PTyp (genCoretype ()));
    lazy (let o = if Rand.randBool () then Some (genExpression ()) else None in
          PPat (genPattern (), o));
  ] [
    lazy (PStr (genStructure ()));
    lazy (PSig (genSignature ()));
  ]

and genCoretype () =
  {
    ptyp_desc = genCoretypeDesc ();
    ptyp_loc = Location.none;
    ptyp_attributes = genAttributes ();
  }

and genCoretypeDesc () =
  addNonterminal ();
  among [
    lazy (Ptyp_any);
    lazy (Ptyp_var (genIdent ()));
  ] [
    lazy (Ptyp_arrow (genArglabel (), genCoretype (), genCoretype ()));
    lazy (Ptyp_tuple (genList genCoretype));
    lazy (Ptyp_constr (genLoc genLongident (), genList genCoretype));
    lazy (Ptyp_object (genList genObjectfield, genClosedFlag ()));
    lazy (Ptyp_class (genLoc genLongident (), genList genCoretype));
    lazy (Ptyp_alias (genCoretype (), genIdent ()));
    lazy (let o = if Rand.randBool () then Some (genList genString) else None in
          Ptyp_variant (genList genRowfield, genClosedFlag (), o));
    lazy (Ptyp_poly (genList (genLoc genIdent), genCoretype ()));
    lazy (Ptyp_package (genPackagetype ()));
    lazy (Ptyp_extension (genExtension ()));
  ]

and genPackagetype () =
  let genLiCt () = (genLoc genLongident (), genCoretype ()) in
  genLoc genLongident (), genList genLiCt

and genRowfield () =
  addNonterminal ();
  among [
    lazy (Rinherit (genCoretype ()));
  ] [
    lazy (Rtag (genLoc genString (), genAttributes (), Rand.randBool (), genList genCoretype));
  ]

and genObjectfield () =
  addNonterminal ();
  among [
    lazy (Oinherit (genCoretype ()));
  ][
    lazy (Otag (genLoc genString (), genAttributes (), genCoretype ()));
  ] 

and genPattern () =
  {
    ppat_desc = genPatternDesc ();
    ppat_loc = Location.none;
    ppat_attributes = genAttributes ();
  }

and genPatternDesc () =
  addNonterminal ();
  among [
    lazy (Ppat_any);
    lazy (Ppat_var (genLoc genIdent ()));
    lazy (Ppat_constant (genConstant ()));
    lazy (Ppat_interval (genConstant (), genConstant ()));
    lazy (Ppat_unpack (genLoc genIdentCapital ()));
  ] [
    lazy (Ppat_alias (genPattern (), genLoc genString ()));
    lazy (Ppat_tuple (genList genPattern));
    lazy (let o = if Rand.randBool () then Some (genPattern ()) else None in
          Ppat_construct (genLoc genLongidentCapital (), o));
    lazy (let o = if Rand.randBool () then Some (genPattern ()) else None in
          Ppat_variant (genIdentCapital (), o));
    lazy (let genLiPt () = (genLoc genLongident (), genPattern ()) in
          Ppat_record (genList genLiPt, genClosedFlag ()));
    lazy (Ppat_array (genList genPattern));
    lazy (Ppat_or (genPattern (), genPattern ()));
    lazy (Ppat_constraint (genPattern (), genCoretype ()));
    lazy (Ppat_type (genLoc genLongident ()));
    lazy (Ppat_lazy (genPattern ()));
    lazy (Ppat_exception (genPattern ()));
    lazy (Ppat_extension (genExtension ()));
    lazy (Ppat_open (genLoc genLongidentCapital (), genPattern ()));
  ]

and genPatternLval ~isRec () =
  {
    ppat_desc = genPatternDescLval ~isRec ();
    ppat_loc = Location.none;
    ppat_attributes = genAttributes ();
  }

and genPatternDescLval ~isRec () =
  addNonterminal ();
  if isRec then Ppat_var (genLoc genString ()) else
  among [
    lazy (Ppat_any);
    lazy (Ppat_var (genLoc genString ()));
  ] [
    lazy (Ppat_alias (genPatternLval ~isRec (), genLoc genIdent ()));
    lazy (Ppat_tuple (genList (genPatternLval  ~isRec)));
    lazy (Ppat_constraint (genPatternLval  ~isRec (), genCoretype ()));
    (* lazy (Ppat_type (genLoc genLongident ())); <- ??? *)
    (* lazy (Ppat_extension (genExtension ())); <- ??? *)
    lazy (Ppat_open (genLoc genLongidentCapital (), genPattern ()));
  ]

and genExpression () =
  {
    pexp_desc = genExpressionDesc ();
    pexp_loc = Location.none;
    pexp_attributes = genAttributes ();
  }

and genExpressionDesc () =
  addNonterminal ();
  among [
    lazy (Pexp_constant (genConstant ()));
    lazy (Pexp_unreachable);
  ] [
    lazy (Pexp_ident (genLoc genLongident ()));
    lazy (let recFlag = genRecFlag () in
          let valuebindings =
            match recFlag with
            | Nonrecursive -> genList (genValuebinding ~isRec:false)
            | Recursive -> genList (genValuebinding ~isRec:true)
          in
          Pexp_let (recFlag, valuebindings, genExpression ()));
    lazy (Pexp_function (genList genCase));
    lazy (Pexp_fun (genArglabel (), genOption genExpression, genPattern (), genExpression ()));
    lazy (let genAlExp () = genArglabel (), genExpression () in
          Pexp_apply (genExpression (), genList genAlExp));
    lazy (Pexp_match (genExpression (), genList genCase));
    lazy (Pexp_try (genExpression (), genList genCase));
    lazy (Pexp_tuple (genList genExpression));
    lazy (Pexp_construct (genLoc genLongident (), genOption genExpression));
    lazy (Pexp_variant (genString (), genOption genExpression));
    lazy (let genLiExp () = genLoc genLongident (), genExpression () in
          Pexp_record (genList genLiExp, genOption genExpression));
    lazy (Pexp_field (genExpression (), genLoc genLongident ()));
    lazy (Pexp_setfield (genExpression (), genLoc genLongident (), genExpression ()));
    lazy (Pexp_array (genList genExpression));
    lazy (Pexp_ifthenelse (genExpression (), genExpression (), genOption genExpression));
    lazy (Pexp_sequence (genExpression (), genExpression ()));
    lazy (Pexp_while (genExpression (), genExpression ()));
    lazy (Pexp_for (genPattern (), genExpression (), genExpression (), genDirectionFlag (), genExpression ()));
    lazy (Pexp_constraint (genExpression (), genCoretype ()));
    lazy (Pexp_coerce (genExpression (), genOption genCoretype, genCoretype ()));
    lazy (Pexp_send (genExpression (), genLoc genString ()));
    lazy (Pexp_new (genLoc genLongident ()));
    lazy (Pexp_setinstvar (genLoc genString (), genExpression ()));
    lazy (let genLlExp () = genLoc genString (), genExpression () in
          Pexp_override (genList genLlExp));
    lazy (Pexp_letmodule (genLoc genString (), genModuleExpr (), genExpression ()));
    lazy (Pexp_letexception (genExtensionConstructor (), genExpression ()));
    lazy (Pexp_assert (genExpression ()));
    lazy (Pexp_lazy (genExpression ()));
    lazy (Pexp_poly (genExpression (), genOption genCoretype));
    lazy (Pexp_object (genClassStructure ()));
    lazy (Pexp_newtype (genLoc genString (), genExpression ()));
    lazy (Pexp_pack (genModuleExpr ()));
    lazy (Pexp_open (genOverrideFlag (), genLoc genLongident (), genExpression ()));
    lazy (Pexp_extension (genExtension ()));
  ]

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
  addNonterminal ();
  among [
    lazy (Ptype_abstract);
    lazy (Ptype_open);
  ] [
    lazy (Ptype_variant (genList genConstructorDecl));
    lazy (Ptype_record (genList genLabelDecl));
  ]

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
  addNonterminal ();
  among [
    lazy (Pcstr_tuple (genList genCoretype));
    lazy (Pcstr_record (genList genLabelDecl));
  ] []

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
  addNonterminal ();
  among [
    lazy (Pext_rebind (genLoc genLongident ()));
  ] [
    lazy (Pext_decl (genConstructorArgs (), genOption genCoretype));
  ]

and genClassType () =
  {
    pcty_desc = genClassTypeDesc ();
    pcty_loc = Location.none;
    pcty_attributes = genAttributes ();
  }

and genClassTypeDesc () =
  addNonterminal ();
  among [
    lazy (Pcty_constr (genLoc genLongident (), genList genCoretype));
    lazy (Pcty_signature (genClassSignature ()));
    lazy (Pcty_arrow (genArglabel (), genCoretype (), genClassType ()));
    lazy (Pcty_extension (genExtension ()));
    lazy (Pcty_open (genOverrideFlag (), genLoc genLongident (), genClassType ()));
  ] []

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
  addNonterminal ();
  among [
    lazy (Pctf_inherit (genClassType ()));
    lazy (Pctf_val (genLoc genString (), genMutableFlag (), genVirtualFlag (), genCoretype ()));
    lazy (Pctf_method (genLoc genString (), genPrivateFlag (), genVirtualFlag (), genCoretype ()));
    lazy (Pctf_constraint (genCoretype (), genCoretype ()));
    lazy (Pctf_attribute (genAttribute ()));
    lazy (Pctf_extension (genExtension ()));
  ] []

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
  addNonterminal ();
  among [
    lazy (Pcl_constr (genLoc genLongident (), genList genCoretype));
    lazy (Pcl_structure (genClassStructure ()));
    lazy (Pcl_fun (genArglabel (), genOption genExpression, genPattern (), genClassExpr ()));
    lazy (let genAlExp () = genArglabel (), genExpression () in
          Pcl_apply (genClassExpr (), genList genAlExp));
    lazy (let recFlag = genRecFlag () in
          let valuebindings =
            match recFlag with
            | Nonrecursive -> genList (genValuebinding ~isRec:false)
            | Recursive -> genList (genValuebinding ~isRec:true)
          in
          Pcl_let (recFlag, valuebindings, genClassExpr ()));
    lazy (Pcl_constraint (genClassExpr (), genClassType ()));
    lazy (Pcl_extension (genExtension ()));
    lazy (Pcl_open (genOverrideFlag (), genLoc genLongident (), genClassExpr ()));
  ] []

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
  addNonterminal ();
  among [
    lazy (Pcf_inherit (genOverrideFlag (), genClassExpr (), genOption (genLoc genString)));
    lazy (Pcf_val (genLoc genString (), genMutableFlag (), genClassFieldKind ()));
    lazy (Pcf_method (genLoc genString (), genPrivateFlag (), genClassFieldKind ()));
    lazy (Pcf_constraint (genCoretype (), genCoretype ()));
    lazy (Pcf_initializer (genExpression ()));
    lazy (Pcf_attribute (genAttribute ()));
    lazy (Pcf_extension (genExtension ()));
  ] []

and genClassFieldKind () =
  addNonterminal ();
  among [
    lazy (Cfk_virtual (genCoretype ()));
    lazy (Cfk_concrete (genOverrideFlag (), genExpression ()));
  ] []

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
  addNonterminal ();
  among [
    lazy (Pmty_ident (genLoc genLongident ()));
    lazy (Pmty_signature (genSignature ()));
    lazy (Pmty_functor (genLoc genString (), genOption genModuleType, genModuleType ()));
    lazy (Pmty_with (genModuleType (), genList genWithConstraint));
    lazy (Pmty_typeof (genModuleExpr ()));
    lazy (Pmty_extension (genExtension ()));
    lazy (Pmty_alias (genLoc genLongident ()));
  ] []

and genSignature () = genList genSignatureItem

and genSignatureItem () =
  {
    psig_desc = genSignatureItemDesc ();
    psig_loc = Location.none;
  }

and genSignatureItemDesc () =
  addNonterminal ();
  among [
    lazy (Psig_value (genValueDesc ()));
    lazy (Psig_type (genRecFlag (), genList genTypeDecl));
    lazy (Psig_typext (genTypeExtension ()));
    lazy (Psig_exception (genExtensionConstructor ()));
    lazy (Psig_module (genModuleDecl ()));
    lazy (Psig_recmodule (genList genModuleDecl));
    lazy (Psig_modtype (genModuleTypeDecl ()));
    lazy (Psig_open (genOpenDesc ()));
    lazy (Psig_include (genIncludeDesc ()));
    lazy (Psig_class (genList genClassDesc));
    lazy (Psig_class_type (genList genClassTypeDecl));
    lazy (Psig_attribute (genAttribute ()));
    lazy (Psig_extension (genExtension (), genAttributes ()));
  ] []
 
and genModuleDecl () =
  {
    pmd_name = genLoc genString ();
    pmd_type = genModuleType ();
    pmd_attributes = genAttributes ();
    pmd_loc = Location.none;
  }

and genModuleTypeDecl () =
  {
    pmtd_name = genLoc genIdentCapital ();
    pmtd_type = genOption genModuleType;
    pmtd_attributes = genAttributes ();
    pmtd_loc = Location.none;
  }

and genOpenDesc () =
  {
    popen_lid = genLoc genLongidentCapital ();
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
  addNonterminal ();
  among [
    lazy (Pwith_type (genLoc genLongident (), genTypeDecl ()));
    lazy (Pwith_module (genLoc genLongident (),genLoc genLongident ()));
    lazy (Pwith_typesubst (genLoc genLongident (), genTypeDecl ()));
    lazy (Pwith_modsubst (genLoc genLongident (),genLoc genLongident ()));
  ] []

and genModuleExpr () =
  {
    pmod_desc = genModuleExprDesc ();
    pmod_loc = Location.none;
    pmod_attributes = genAttributes ();
  }

and genModuleExprDesc () =
  addNonterminal ();
  among [
    lazy (Pmod_ident (genLoc genLongident ()));
    lazy (Pmod_structure (genStructure ()));
    lazy (Pmod_functor (genLoc genString (), genOption genModuleType, genModuleExpr ()));
    lazy (Pmod_apply (genModuleExpr (), genModuleExpr ()));
    lazy (Pmod_constraint (genModuleExpr (), genModuleType ()));
    lazy (Pmod_unpack (genExpression ()));
    lazy (Pmod_extension (genExtension ()));
  ] []

and genStructure () = genList genStructureItem

and genStructureItem () =
  {
    pstr_desc = genStructureItemDesc ();
    pstr_loc = Location.none;
  }

and genStructureItemDesc () =
  addNonterminal ();
  among [
    lazy (Pstr_eval (genExpression (), genAttributes ()));
    lazy (let recFlag = genRecFlag () in
          let valuebindings =
            match recFlag with
            | Nonrecursive -> genList (genValuebinding ~isRec:false)
            | Recursive -> genList (genValuebinding ~isRec:true)
          in
          Pstr_value (recFlag, valuebindings));
    lazy (Pstr_primitive (genValueDesc ()));
    lazy (Pstr_type (genRecFlag (), genList genTypeDecl));
    lazy (Pstr_typext (genTypeExtension ()));
    lazy (Pstr_exception (genExtensionConstructor ()));
    lazy (Pstr_module (genModuleBinding ()));
    lazy (Pstr_recmodule (genList genModuleBinding));
    lazy (Pstr_modtype (genModuleTypeDecl ()));
    lazy (Pstr_open (genOpenDesc ()));
    lazy (Pstr_class (genList genClassDecl));
    lazy (Pstr_class_type (genList genClassTypeDecl));
    lazy (Pstr_include (genIncludeDecl ()));
    lazy (Pstr_attribute (genAttribute ()));
    lazy (Pstr_extension (genExtension (), genAttributes ()));
  ] []

and genValuebinding ~isRec () =
  {
    pvb_pat = genPatternLval ~isRec ();
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