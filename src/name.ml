include String
let hash = Hashtbl.hash
let pp = Fmt.string

module Map = CCMap.Make(String)
module Set = CCSet.Make(String)

let fresh =
  let r = ref (-1) in
  fun s -> incr r; Fmt.strf "%s%i" s !r
