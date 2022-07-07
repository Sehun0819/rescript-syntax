let choose bound =
  Random.self_init ();
  Random.int bound

let genList ?bound:(bound=5) f =
  let l = ref [] in
  for _i = 0 to bound do
    l := f ():: !l;
  done;
  !l
