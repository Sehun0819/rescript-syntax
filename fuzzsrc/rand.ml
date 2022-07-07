(* int bound of `Random.int` should be less than 2^30. *)
let intbound = (Int.shift_left 1 30) - 1

let randInt ?bound:(bound=intbound) () =
  Random.self_init ();
  Random.int bound 

let randFloat ?bound:(bound=Float.max_float) () =
  Random.self_init ();
  Random.float bound 

let randBool () =
  Random.self_init ();
  Random.bool ()

let amongv vlist =
  let size = List.length vlist in
  List.nth vlist (randInt ~bound:size ())

let amongf flist =
  let size = List.length flist in
  let f = List.nth flist (randInt ~bound:size ()) in
  f ()

let genList ?bound:(bound=5) f =
  let l = ref [] in
  for _i = 1 to bound do
    l := f ():: !l;
  done;
  !l
