open Source
open Language.Ast

exception Clash of string

module Set =
struct
  include Set.Make(String)

  let disjoint_add x s = if mem x s then raise (Clash x) else add x s
  let disjoint_union s1 s2 = fold disjoint_add s2 s1
end

type ('v, 't) env =
  { vals : ('v, unit) phrase VariableMap.t;
    typs : ('t, unit) phrase TyNameMap.t;
  }

let empty =
  { vals = VariableMap.empty;
    typs = TyNameMap.empty;
  }

let not_found =
  raise Not_found

let extend_val env x v = {env with vals = VariableMap.add x v env.vals}
let extend_typ env y t = {env with typs = TyNameMap.add y t env.typs}
let extend_vals env xs vs = List.fold_left2 extend_val env xs vs
let extend_typs env ys ts = List.fold_left2 extend_typ env ys ts

let find_val x env = try VariableMap.find x env.vals with Not_found -> not_found 
let find_typ y env = try TyNameMap.find y env.typs with Not_found -> not_found 
let find_opt_val x env = VariableMap.find_opt x env.vals
let find_opt_typ y env = TyNameMap.find_opt y env.typs