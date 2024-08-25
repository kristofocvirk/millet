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

let val_not_found x =
  failwith (string_of_expression (Var x))

let typ_not_found x =
  print_endline "type";
  (TyName.print x Format.std_formatter);
  failwith (Format.flush_str_formatter ())

let lbl_not_found x =
  print_endline "label";
  (Label.print x Format.std_formatter);
  failwith (Format.flush_str_formatter ())

let func_not_found x =
  failwith (string_of_expression (Var x))

let update_runs env = {env with runs = env.runs + 1}

let extend_val env x v = {env with vals = VariableMap.add x v env.vals}
let extend_typ env x v = {env with typs = TyNameMap.add x v env.typs}
let extend_lbl env y t = {env with lbls = LabelMap.add y t env.lbls}
let extend_func env x v = {env with funcs = VariableMap.add x v env.funcs}
let extend_vals env xs vs = List.fold_left2 extend_val env xs vs
let extend_typs env xs vs = List.fold_left2 extend_typ env xs vs
let extend_lbls env ys ts = List.fold_left2 extend_typ env ys ts
let extend_funcs env xs vs = List.fold_left2 extend_func env xs vs

let find_val x env = print_endline "vals";try VariableMap.find x env.vals with Not_found -> val_not_found x
let find_typ x env = print_endline "typs";try TyNameMap.find x env.typs with Not_found -> typ_not_found x
let find_lbl y env = print_endline "lbls";try LabelMap.find y env.lbls with Not_found -> lbl_not_found y 
let find_func x env = print_endline "funcs"; try VariableMap.find x env.funcs with Not_found -> func_not_found x
let find_opt_val x env = VariableMap.find_opt x env.vals
let find_opt_typ x env = TyNameMap.find_opt x env.typs
let find_opt_lbl y env = LabelMap.find_opt y env.lbls
let find_opt_funcs x env = VariableMap.find_opt x env.funcs

let iter_vals f env = VariableMap.iter f env.vals