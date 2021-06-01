type t = string

let pp = Fmt.string

module Map = CCMap.Make(String)
module Set = CCSet.Make(String)
