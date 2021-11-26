include String
let hash = Hashtbl.hash
let pp = Fmt.string

module Map = CCMap.Make(String)
module Set = CCSet.Make(String)
