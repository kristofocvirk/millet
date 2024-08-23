open Source
open Language.Ast

exception Clash of string

module Set =
struct
  include Set.Make(String)

  let disjoint_add x s = if mem x s then raise (Clash x) else add x s
  let disjoint_union s1 s2 = fold disjoint_add s2 s1
end

type ('v, 't, 'l, 'f) env =
  { vals : ('v, unit) phrase VariableMap.t;
    typs : ('t, unit) phrase TyNameMap.t;
    lbls : ('l, unit) phrase LabelMap.t;
    funcs : ('f, unit) phrase VariableMap.t;
    runs : int
  }

let empty =
  { vals = VariableMap.empty;
    typs = TyNameMap.empty;
    lbls = LabelMap.empty;
    funcs = VariableMap.empty;
    runs = 0
  }

let not_found =
  raise Not_found

let update_runs env = {env with runs = env.runs + 1}

let extend_val env x v = {env with vals = VariableMap.add x v env.vals}
let extend_typ env x v = {env with typs = TyNameMap.add x v env.typs}
let extend_lbl env y t = {env with lbls = LabelMap.add y t env.lbls}
let extend_func env x v = {env with funcs = VariableMap.add x v env.funcs}
let extend_vals env xs vs = List.fold_left2 extend_val env xs vs
let extend_typs env xs vs = List.fold_left2 extend_typ env xs vs
let extend_lbls env ys ts = List.fold_left2 extend_typ env ys ts
let extend_funcs env xs vs = List.fold_left2 extend_func env xs vs

let find_val x env = try VariableMap.find x env.vals with Not_found -> not_found 
let find_typ x env = try LabelMap.find x env.lbls with Not_found -> not_found 
let find_lbl y env = try LabelMap.find y env.lbls with Not_found -> not_found 
let find_func x env = try VariableMap.find x env.funcs with Not_found -> not_found 
let find_opt_val x env = VariableMap.find_opt x env.vals
let find_opt_typ x env = TyNameMap.find_opt x env.typs
let find_opt_lbl y env = LabelMap.find_opt y env.lbls
let find_opt_funcs x env = VariableMap.find_opt x env.funcs