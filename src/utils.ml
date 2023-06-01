
let contains s1 s2 =
  let re = Str.regexp s2
  in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false
 