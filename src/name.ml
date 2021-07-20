include String
let hash = Hashtbl.hash
let pp = Fmt.string

module Map = CCMap.Make(String)
module Set = CCSet.Make(String)

let refresh n = n ^ "'"

let indice_array = [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|]
let rec digits fmt i =
  if i < 0 then
    Format.pp_print_string fmt "₋"
  else if i < 10 then
    Format.pp_print_string fmt indice_array.(i)
  else begin
    digits fmt (i/10) ;
    Format.pp_print_string fmt indice_array.(i mod 10)
  end

let fresh =
  let r = Hashtbl.create 17 in
  fun s ->
    let i = CCHashtbl.get_or r s ~default:0 in
    CCHashtbl.incr r s; Fmt.strf "%s%a" s digits i
