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

let among ?depth:(depth=0) (l1: 'a Lazy.t list) (l2: 'a Lazy.t list) : 'a =
  let l = if depth <= 0 then l1 else l1 @ l2 in
  let size = List.length l in
  let pick = List.nth l (randInt ~bound:size ()) in
  Lazy.force pick

let amongv vlist =
  let size = List.length vlist in
  List.nth vlist (randInt ~bound:size ())

let genList ?bound:(bound=5) f =
  let l = ref [] in
  for _i = 1 to bound do
    l := f ():: !l;
  done;
  !l

let genOption f =
  if randBool () then Some (f ()) else None