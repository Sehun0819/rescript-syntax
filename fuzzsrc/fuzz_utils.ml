let emptyLoc: Location.t =
  {
    loc_start = Lexing.dummy_pos;
    loc_end = Lexing.dummy_pos;
    loc_ghost = true;
  }
  