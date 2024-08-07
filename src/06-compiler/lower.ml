open Emit
module Wasm = Wasm
module Ast = Language.Ast
module Const = Language.Const
module Env = Env

let prompt = ref false
let interpret = ref false
let compile = ref false
let run = ref false
let headless = ref false
let unchecked = ref false
let validate = ref false
let textual = ref false
let print_ast = ref false
let print_sig = ref false
let trace = ref false
let width = ref 80
let box_locals = ref false
let box_globals = ref true
let box_modules = ref true
let box_temps = ref false
let box_scrut = ref false

type null = Null | Nonull

type loc =
  | PreLoc of int
  | LocalLoc of int
  | GlobalLoc of int
  | ClosureLoc of null * int * int * int (* fldidx, localidx, typeidx *)

type func_loc = {funcidx : int; typeidx : int; arity : int}

let as_local_loc = function LocalLoc idx -> idx | _ -> assert false
let as_global_loc = function GlobalLoc idx -> idx | _ -> assert false


(* Representations *)

type rep =
  | DropRep                (* value never used *)
  | BlockRep of null       (* like Boxed, but empty tuples are suppressed *)
  | BoxedRep of null       (* concrete boxed representation *)
  | BoxedAbsRep of null    (* abstract boxed representation *)
  | UnboxedRep of null     (* representation with unboxed type or concrete ref types *)
  | UnboxedLaxRep of null  (* like Unboxed, but Int may have junk high bit *)

let null_rep = function
  | BlockRep n | BoxedRep n | BoxedAbsRep n | UnboxedRep n | UnboxedLaxRep n -> n
  | DropRep -> assert false

(* Configurable *)
let boxed_if flag null = if !flag then BoxedRep null else UnboxedRep null
let local_rep () = boxed_if box_locals Null    (* values stored in locals *)
let clos_rep () = boxed_if box_locals Nonull   (* values stored in closures *)
let global_rep () = boxed_if box_globals Null  (* values stored in globals *)
let struct_rep () = boxed_if box_modules Nonull (* values stored in structs *)
let tmp_rep () = boxed_if box_temps Null       (* values stored in temps *)
let pat_rep () = boxed_if box_scrut Nonull     (* values fed into patterns *)

(* Non-configurable *)
let ref_rep = BoxedAbsRep Null      (* expecting a reference *)
let rigid_rep = UnboxedRep Nonull   (* values produced or to be consumed *)
let lax_rep = UnboxedLaxRep Nonull  (* lax ints produced or consumed *)
let field_rep = BoxedAbsRep Nonull  (* values stored in fields *)
let arg_rep = BoxedAbsRep Nonull    (* argument and result values *)
let unit_rep = BlockRep Nonull      (* nothing on stack *)

let loc_rep = function
  | PreLoc _ -> rigid_rep
  | GlobalLoc _ -> global_rep ()
  | LocalLoc _ -> local_rep ()
  | ClosureLoc _ -> clos_rep ()


let max_func_arity = if !headless then 4 else 12

let clos_arity_idx = 0
let clos_code_idx = 1
let clos_env_idx = 2  (* first environment entry *)


(* Environment *)

type data_con = {tag : int32; typeidx : int32; arity : int}
type data = (string * data_con) list
type env = (loc * func_loc option, data) Env.env
type scope = PreScope | LocalScope | GlobalScope

let make_env () =
  let env = ref Env.empty in
  env

let scope_rep = function
  | PreScope -> rigid_rep
  | LocalScope -> local_rep ()
  | GlobalScope -> global_rep ()


(* Compilation context *)

module ClosKey =
struct
  type t = Wasm.val_type list * Wasm.val_type list * Wasm.field_type list
  let compare = compare
end

module ClosMap = Map.Make(ClosKey)
module IdxMap = Map.Make(Int32)

type clos_idxs = {codeidx : int; closidx : int; envidx : int}
type ctxt_ext =
  { envs : (scope * env ref) list;
    clostypes : clos_idxs ClosMap.t ref;
    data : int ref;
  }
type ctxt = ctxt_ext Emit.ctxt

let make_ext_ctxt () : ctxt_ext =
  { envs = [(PreScope, make_env ())];
    clostypes = ref ClosMap.empty;
    data = ref (-1);
  }
let make_ctxt () : ctxt = Emit.make_ctxt (make_ext_ctxt ())

let enter_scope ctxt scope : ctxt =
  {ctxt with ext = {ctxt.ext with envs = (scope, ref Env.empty) :: ctxt.ext.envs}}

let current_scope ctxt : scope * env ref =
  List.hd ctxt.ext.envs


(* Lowering types *)

let lower_ref null ht : Wasm.ref_type =
  match null with
  | Null -> (Null, ht)
  | Nonull -> (NoNull, ht)

let abs = Wasm.EqHT 
let absref = lower_ref Nonull abs

let sub xs st = Wasm.SubT (Wasm.NoFinal ,List.map (fun x -> x) xs, st)
let field t = Wasm.FieldT (Wasm.Cons, Wasm.ValStorageT t)
let field_mut t = Wasm.FieldT (Wasm.Var , Wasm.ValStorageT t)
let ref_ x = Wasm.RefT (Wasm.NoNull, Wasm.VarHT (Wasm.StatX x))

let rec lower_value_type ctxt rep t : Wasm.val_type =
  match t, rep with
  | t, (BlockRep n | BoxedRep n) -> RefT (lower_ref n (lower_heap_type ctxt t))
  | _, BoxedAbsRep n -> RefT (lower_ref n abs)
  | Ast.TyConst Const.BooleanTy, _ -> NumT I32T 
  | Ast.TyConst Const.IntegerTy, _ -> NumT I32T 
  | Ast.TyConst Const.FloatTy, _ -> NumT F64T 
  | t, (UnboxedRep n | UnboxedLaxRep n) -> RefT (lower_ref n (lower_heap_type ctxt t))
  | _, DropRep -> assert false

and lower_heap_type ctxt t : Wasm.heap_type =
  match t with
  | Ast.TyConst Const.BooleanTy | Ast.TyConst Const.IntegerTy -> I31HT
  | Ast.TyTuple [] -> EqHT 
  | t -> (VarHT (Wasm.StatX (lower_var_type ctxt t)))

and lower_anycon_type ctxt : int =
  emit_type ctxt (sub [] (Wasm.DefStructT (Wasm.StructT [Wasm.FieldT (Wasm.Cons, (Wasm.ValStorageT (Wasm.NumT Wasm.I32T)))])))

and lower_con_type ctxt ts : int =
  if ts = [] then -1 else
  let anycon = lower_anycon_type ctxt in
  let vts = List.map (lower_value_type ctxt field_rep) ts in
  let fts = List.map (fun x -> Wasm.FieldT (Wasm.Cons, Wasm.ValStorageT x)) vts in
  emit_type ctxt (sub [Wasm.VarHT (Wasm.StatX anycon)] (Wasm.DefStructT (Wasm.StructT (field (Wasm.NumT Wasm.I32T) :: fts))))

and lower_var_type ctxt t =
  match t with
  | Ast.TyConst Const.FloatTy ->
    emit_type ctxt (sub [] (Wasm.DefStructT (Wasm.StructT [field (Wasm.NumT Wasm.F64T)])))
  | Ast.TyTuple ts ->
    let ts = List.map (lower_value_type ctxt field_rep) ts in
    emit_type ctxt (sub [] (Wasm.DefStructT  (Wasm.StructT (List.map field ts))))
  | Ast.TyArrow (_, _) -> failwith "TODO lower_var_type functions"
    (*match !arity_opt with
    | T.KnownArity arity -> snd (lower_func_type ctxt arity)
    | T.UnknownArity | T.VariableArity -> lower_anyclos_type ctxt 
    *)
  | _ -> assert false

and lower_anyclos_type ctxt : int =
  emit_type ctxt (sub [] (Wasm.DefStructT (Wasm.StructT [field (Wasm.NumT Wasm.I32T)])))

and lower_func_type ctxt arity : int * int =
  let func ts1 ts2 = Wasm.DefFuncT (Wasm.FuncT (ts1, ts2)) in
  let argts, _ = lower_param_types ctxt arity in
  let key = (argts, [Wasm.RefT absref], []) in
  match ClosMap.find_opt key !(ctxt.ext.clostypes) with
  | Some {codeidx; closidx; _} -> codeidx, closidx
  | None ->
    let anyclos = lower_anyclos_type ctxt in
    let code, def_code = emit_type_deferred ctxt in
    let closdt = (sub [Wasm.VarHT (Wasm.StatX anyclos)] (Wasm.DefStructT (Wasm.StructT [field (Wasm.NumT Wasm.I32T); field (Wasm.RefT(Wasm.NoNull ,Wasm.VarHT (Wasm.StatX code)))]))) in
    let clos = emit_type ctxt closdt in
    let codedt = (sub [] (func ((Wasm.RefT (Wasm.NoNull, Wasm.VarHT (Wasm.StatX clos))) :: argts) [Wasm.RefT absref])) in
    def_code codedt;
    let clos_idxs = {codeidx = code; closidx = clos; envidx = clos} in
    ctxt.ext.clostypes := ClosMap.add key clos_idxs !(ctxt.ext.clostypes);
    code, clos

and lower_clos_type ctxt arity flds : int * int * int =
  let argts, _ = lower_param_types ctxt arity in
  let key = (argts, [Wasm.RefT absref], flds) in
  match ClosMap.find_opt key !(ctxt.ext.clostypes) with
  | Some {codeidx; closidx; envidx} -> codeidx, closidx, envidx
  | None ->
    let code, clos = lower_func_type ctxt arity in
    let envdt =
      (sub [Wasm.VarHT (Wasm.StatX clos)] (Wasm.DefStructT (Wasm.StructT (field (Wasm.NumT Wasm.I32T) :: field (ref_ code) :: flds)))) in
    let clos_env = emit_type ctxt envdt in
    let clos_idxs = {codeidx = code; closidx = clos; envidx = clos_env} in
    ctxt.ext.clostypes := ClosMap.add key clos_idxs !(ctxt.ext.clostypes);
    code, clos, clos_env

and lower_param_types ctxt arity : Wasm.val_type list * int option =
  let field_mut t = Wasm.FieldT (Wasm.Var , Wasm.ValStorageT t) in
  let array ft = Wasm.DefArrayT (Wasm.ArrayT ft) in
  if arity <= max_func_arity then
    List.init arity (fun _ -> Wasm.RefT absref), None
  else
    let argv = emit_type ctxt (sub [] (array (field_mut (Wasm.RefT absref)))) in
    [ref_ argv], Some argv

and lower_block_type ctxt rep t : Wasm.block_type =
  match t, rep with
  | _, DropRep
  | Ast.TyTuple [], BlockRep _ -> Wasm.ValBlockType None 
  | t, _ -> ValBlockType (Some (lower_value_type ctxt rep t))


(* Closure environments *)

let lower_clos_env ctxt vars rec_xs
  : Wasm.field_type list * (Ast.variable * Ast.ty * int) list =
  let fixups = ref [] in
  let flds =
    List.mapi (fun i (x, t) ->
      if Ast.VariableMap.mem x rec_xs then begin
        fixups := (x, t, i) :: !fixups;
        field_mut (lower_value_type ctxt (local_rep ()) t)
      end else
        field (lower_value_type ctxt (clos_rep ()) t)
    ) (Ast.VariableMap.bindings vars)
  in flds, !fixups