module FuzzerClflags: sig
  val target: string ref
  val width : int ref
  val interface : bool ref

  val parse : unit -> unit
end = struct
  let target = ref "res"
  let width = ref 100
  let interface = ref false

  let usage = 
    "\n\
     ** To be filled **\n\n"

  let spec =
    [
      ( "-target",
        Arg.String (fun txt -> target := txt),
        "Specify the print target language either binary, ml, ast, sexp, comments or res. Default: res" );
      ( "-width",
        Arg.Int (fun w -> width := w),
        "Specify the line length for the printer (formatter)" );
      ( "-interface",
        Arg.Unit (fun () -> interface := true),
        "Generate an interface" );
    ]

  let parse () = Arg.parse spec (fun f -> ()) usage
end

module Fuzzer = struct
  let fuzz ~isInterface ~target ~width =
    let printEngine =
      match target with
      | "binary" -> Res_driver_binary.printEngine
      | "ml" -> Res_driver_ml_parser.printEngine
      | "ast" -> Res_ast_debugger.printEngine
      | "sexp" -> Res_ast_debugger.sexpPrintEngine
      | "comments" -> Res_ast_debugger.commentsPrintEngine
      | "res" -> Res_driver.printEngine
      | target ->
        print_endline
          ("-print needs to be either binary, ml, ast, sexp, comments or res. \
            You provided " ^ target);
        exit 1
    in

    if isInterface then
      let parsetree = Grammar_fuzzer.genSignature () in
      printEngine.printInterface ~width ~filename:"tempInterface" ~comments:[] parsetree
    else
      let parsetree = Grammar_fuzzer.genStructure () in
      printEngine.printImplementation ~width ~filename:"tempInterface" ~comments:[] parsetree
end

let () =
  FuzzerClflags.parse ();
  Fuzzer.fuzz ~isInterface:!FuzzerClflags.interface
    ~target:!FuzzerClflags.target
    ~width:!FuzzerClflags.width