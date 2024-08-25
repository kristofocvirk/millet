open Utils

(*pack*)
type pack_size = Pack8 | Pack16 | Pack32 | Pack64
type extension = SX | ZX
let packed_size = function
  | Pack8 -> 1
  | Pack16 -> 2
  | Pack32 -> 4
  | Pack64 -> 8

(*types*)
type type_idx = int
type local_idx = int
type name = Utils.Utf8.unicode 

type var = StatX of type_idx | RecX of int 

type null = NoNull | Null
type mut = Cons | Var
type final = NoFinal | Final
type init = Set | Unset
type 'a limits = {min : 'a; max : 'a option}

type num_type = I32T | I64T | F32T | F64T
type vec_type = V128T
type heap_type =
  | AnyHT | NoneHT | EqHT | I31HT | StructHT | ArrayHT
  | FuncHT | NoFuncHT
  | ExternHT | NoExternHT
  | VarHT of var
  | DefHT of def_type
  | BotHT
and ref_type = null * heap_type
and val_type = NumT of num_type | VecT of vec_type | RefT of ref_type | BotT
and result_type = val_type list
and instr_type = InstrT of result_type * result_type * local_idx list

and storage_type = ValStorageT of val_type | PackStorageT of pack_size
and field_type = FieldT of mut * storage_type

and struct_type = StructT of field_type list
and array_type = ArrayT of field_type
and func_type = FuncT of result_type * result_type

and str_type =
  | DefStructT of struct_type
  | DefArrayT of array_type
  | DefFuncT of func_type

and sub_type = SubT of final * heap_type list * str_type
and rec_type = RecT of sub_type list
and def_type = DefT of rec_type * int

type table_type = TableT of Int.t limits * ref_type
type memory_type = MemoryT of Int.t limits
type global_type = GlobalT of mut * val_type
type local_type = LocalT of init * val_type
type extern_type =
  | ExternFuncT of def_type
  | ExternTableT of table_type
  | ExternMemoryT of memory_type
  | ExternGlobalT of global_type

type export_type = ExportT of extern_type * name
type import_type = ImportT of extern_type * name * name
type module_type = ModuleT of import_type list * export_type list

type block_type = VarBlockType of int | ValBlockType of val_type option

type initop = Explicit | Implicit

type ('t, 'p) memop = {ty : 't; align : int; offset : int; pack : 'p}
type loadop = (num_type, (pack_size * extension) option) memop

(* Instructions *)
type instr =
  (* Constants *)
  | IntConst of num_type * int
  | FloatConst of num_type * float
  | LocalGet of int
  | LocalSet of int
  | LocalTee of int
  
  (* Arithmetic operations *)
  | Add of num_type 
  | Sub of num_type 
  | Mul of num_type
  | Div of num_type 
  | Shl of num_type
  | Shr of num_type
  | ShrU of num_type
  | Ne of num_type
  | Eqz of num_type
  
  (* Control flow *)
  | Call of int
  | CallRef of int
  | Return
  | If of block_type * instr list * instr list  (* (if (then ... ) (else ... )) *)
  | Block of block_type * instr list  (* (block ... ) *)
  | Loop of block_type * instr list   (* (loop ... ) *)
  | Br of int            (* (br <label_index>) *)
  | BrIf of int          (* (br_if <label_index>) *)
  | BrTable of int list * int (* (br_table <labels> <default>) *)
  | Unreachable          (* (unreachable) *)
  
  (* Struct operations *)
  | StructNew of int * initop 
  | StructGet of int * int * extension option 
  | StructSet of int * int

  (* globals *)
  | GlobalGet of int
  | GlobalSet of int
  (* Parametric instucrions *)
  | Drop

  (* Array operations *)
  | ArrayNew of int * initop 
  | ArrayGet of int * extension option
  | ArraySet of int 
  | ArrayLen
  (* Reference types operations *)

  | RefNull of heap_type
  | RefAsNonNull
  | RefEq
  | RefIsNull
  | RefFunc of int
  | RefI31 
  | I31Get of extension
  | RefCast of ref_type

  (* memory *)
  | MemoryInit of int
  | MemoryGrow 
  | MemorySize
  | Load of loadop  


(*local*)
type const = instr list

type local = 
{
  ltype : val_type
}

and global =
{
  gtype : global_type;
  ginit : const;
}


(* Function *)
type func = {
  ftype : int; 
  locals : local list;
  body : instr list;
}

(* Tables & Memories *)

type table =
{
  ttype : table_type;
  tinit : const;
}

type memory =
{
  mtype : memory_type;
}

type segment_mode =
  | Passive
  | Active of {index : int; offset : const}
  | Declarative

type elem_segment =
{
  etype : ref_type;
  einit : const list;
  emode : segment_mode;
}

type data_segment =
{
  dinit : string;
  dmode : segment_mode;
}


(* Modules *)

type type_ = rec_type 

type export_desc =
  | FuncExport of int 
  | TableExport of int
  | MemoryExport of int  
  | GlobalExport of int 

type export =
{
  name : name;
  edesc : export_desc;
}

type import_desc =
  | FuncImport of int
  | TableImport of table_type
  | MemoryImport of memory_type
  | GlobalImport of global_type

type import =
{
  module_name : name;
  item_name : name;
  idesc : import_desc;
}

type start =
{
  sfunc : int;
}

type module_ =
{
  types : type_ list;
  globals : global list;
  tables : table list;
  memories : memory list;
  funcs : func list;
  start : start option;
  elems : elem_segment list;
  datas : data_segment list;
  imports : import list;
  exports : export list;
}


(* Auxiliary functions *)

let empty_module =
{
  types = [];
  globals = [];
  tables = [];
  memories = [];
  funcs = [];
  start = None;
  elems = [];
  datas = [];
  imports = [];
  exports = [];
}

(* Helper function to convert num_type to string *)
type sexpr = Atom of string | Node of string * sexpr list

let string_of_name n =
  let b = Buffer.create 16 in
  let escape uc =
    if uc < 0x20 || uc >= 0x7f then
      Buffer.add_string b (Printf.sprintf "\\u{%02x}" uc)
    else begin
      let c = Char.chr uc in
      if c = '\"' || c = '\\' then Buffer.add_char b '\\';
      Buffer.add_char b c
    end
  in
  List.iter escape n;
  Buffer.contents b

let string_of_var = function
  | StatX x -> string_of_int x
  | RecX x -> "rec." ^ string_of_int x

let string_of_null = function
  | NoNull -> ""
  | Null -> "null "

let string_of_final = function
  | NoFinal -> ""
  | Final -> " final"

let string_of_mut s = function
  | Cons -> s
  | Var -> "(mut " ^ s ^ ")"

let num_size = function
  | I32T | F32T -> 4
  | I64T | F64T -> 8

let string_of_num_type = function
  | I32T -> "i32"
  | I64T -> "i64"
  | F32T -> "f32"
  | F64T -> "f64"

let string_of_vec_type = function
  | V128T -> "v128"

let rec string_of_heap_type = function
  | AnyHT -> "any"
  | NoneHT -> "none"
  | EqHT -> "eq"
  | I31HT -> "i31"
  | StructHT -> "struct"
  | ArrayHT -> "array"
  | FuncHT -> "func"
  | NoFuncHT -> "nofunc"
  | ExternHT -> "extern"
  | NoExternHT -> "noextern"
  | VarHT x -> string_of_var x
  | DefHT dt -> "(" ^ string_of_def_type dt ^ ")"
  | BotHT -> "something"

and str_of_ref_type t = 
  match t with
  | (Null, AnyHT) -> "anyref"
  | (Null, EqHT) -> "eqref"
  | (Null, I31HT) -> "i31ref"
  | (Null, StructHT) -> "structref"
  | (Null, ArrayHT) -> "arrayref"
  | (Null, FuncHT) -> "funcref"
  | t -> string_of_ref_type t

and string_of_ref_type = function
  | (nul, t) -> "(ref " ^ string_of_null nul ^ string_of_heap_type t ^ ")"

and string_of_val_type = function
  | NumT t -> string_of_num_type t
  | VecT t -> string_of_vec_type t
  | RefT t -> string_of_ref_type t
  | BotT -> "bot"


and string_of_result_type = function
  | ts -> "[" ^ String.concat " " (List.map string_of_val_type ts) ^ "]"


and string_of_storage_type = function
  | ValStorageT t -> string_of_val_type t
  | PackStorageT p -> "i" ^ string_of_int (8 * packed_size p)

and string_of_field_type = function
  | FieldT (mut, t) -> string_of_mut (string_of_storage_type t) mut

and string_of_struct_type = function
  | StructT fts ->
    String.concat " " (List.map (fun ft -> "(field " ^ string_of_field_type ft ^ ")") fts)

and string_of_array_type = function
  | ArrayT ft -> string_of_field_type ft

and string_of_func_type = function
  | FuncT (ts1, ts2) ->
    string_of_result_type ts1 ^ " -> " ^ string_of_result_type ts2

and string_of_str_type = function
  | DefStructT st -> "struct " ^ string_of_struct_type st
  | DefArrayT at -> "array " ^ string_of_array_type at
  | DefFuncT ft -> "func " ^ string_of_func_type ft

and string_of_sub_type = function
  | SubT (Final, [], st) -> string_of_str_type st
  | SubT (fin, hts, st) ->
    String.concat " "
      (("sub" ^ string_of_final fin) :: List.map string_of_heap_type hts) ^
    " (" ^ string_of_str_type st ^ ")"

and string_of_rec_type = function
  | RecT [st] -> string_of_sub_type st
  | RecT sts ->
    "rec " ^
    String.concat " " (List.map (fun st -> "(" ^ string_of_sub_type st ^ ")") sts)

and string_of_def_type = function
  | DefT (RecT [st], 0) -> string_of_sub_type st
  | DefT (rt, i) -> "(" ^ string_of_rec_type rt ^ ")." ^ string_of_int i


let string_of_limits = function
  | {min; max} ->
    string_of_int min ^
    (match max with None -> "" | Some n -> " " ^ string_of_int n)

let string_of_memory_type = function
  | MemoryT lim -> string_of_limits lim

let string_of_table_type = function
  | TableT (lim, t) -> string_of_limits lim ^ " " ^ string_of_ref_type t

let string_of_global_type = function
  | GlobalT (mut, t) -> string_of_mut (string_of_val_type t) mut

let string_of_local_type = function
  | LocalT (Set, t) -> string_of_val_type t
  | LocalT (Unset, t) -> "(unset " ^ string_of_val_type t ^ ")"

let string_of_extern_type = function
  | ExternFuncT dt -> "func " ^ string_of_def_type dt
  | ExternTableT tt -> "table " ^ string_of_table_type tt
  | ExternMemoryT mt -> "memory " ^ string_of_memory_type mt
  | ExternGlobalT gt -> "global " ^ string_of_global_type gt


let string_of_export_type = function
  | ExportT (et, name) ->
    "\"" ^ string_of_name name ^ "\" : " ^ string_of_extern_type et

let string_of_import_type = function
  | ImportT (et, module_name, name) ->
    "\"" ^ string_of_name module_name ^ "\" \"" ^
      string_of_name name ^ "\" : " ^ string_of_extern_type et

let string_of_module_type = function
  | ModuleT (its, ets) ->
    String.concat "" (
      List.map (fun it -> "import " ^ string_of_import_type it ^ "\n") its @
      List.map (fun et -> "export " ^ string_of_export_type et ^ "\n") ets
    )

(* ast strings *)

let pack_size = function
  | Pack8 -> "8"
  | Pack16 -> "16"
  | Pack32 -> "32"
  | Pack64 -> "64"

let list f xs = List.map f xs
let list_of_opt = function None -> [] | Some x -> [x]
let tab head f xs = if xs = [] then [] else [Node (head, list f xs)]

let atom f x = Atom (f x)

let decls kind ts = tab kind (atom string_of_val_type) ts

let get o x =
    match o with
    | Some y -> y
    | None -> x

let map f = function
    | Some x -> Some (f x)
    | None -> None

let opt_s f xo = get (map f xo) ""

let string_of_local_idx (x : local_idx)= 
  match x with
  | i -> string_of_int i

let string_of_extension = function
  | SX -> "_s"
  | ZX -> "_u"

let string_of_num_type = function
  | I32T -> "i32"
  | I64T -> "i64"
  | F32T -> "f32"
  | F64T -> "f64"

(* Helper function to convert val_type to string *)
let rec string_of_val_type = function
  | NumT nt -> string_of_num_type nt
  | VecT _ -> "v128" (* Placeholder, since only one vector type is defined *)
  | RefT (null, ht) -> 
    (if null = Null then "null " else "") ^ string_of_heap_type ht
  | BotT -> "bot"

(* Helper function to convert heap_type to string *)
and string_of_heap_type = function
  | AnyHT -> "any"
  | NoneHT -> "none"
  | EqHT -> "eq"
  | I31HT -> "i31"
  | StructHT -> "struct"
  | ArrayHT -> "array"
  | FuncHT -> "func"
  | NoFuncHT -> "nofunc"
  | ExternHT -> "extern"
  | NoExternHT -> "noextern"
  | VarHT (StatX idx) -> Printf.sprintf "(ref %d)" idx
  | VarHT (RecX idx) -> Printf.sprintf "(rec %d)" idx
  | DefHT _ -> "def" (* Simplified *)
  | BotHT -> "bot"

(* Helper function to convert mut to string *)
let string_of_initop = function
  | Explicit -> ""
  | Implicit -> "_default" 

let sexpr_of_block_type = function 
  | VarBlockType x -> [Node ("type " ^ string_of_int x, [])]
  | ValBlockType ts -> decls "result" (list_of_opt ts)

let memop name typ {ty; align; offset; _} sz =
  typ ty ^ "." ^ name ^
  (if offset = 0 then "" else " offset=" ^ string_of_int offset) ^
  (if 1 lsl align = sz then "" else " align=" ^ string_of_int (1 lsl align))

let loadop op =
  match op.pack with
  | None -> memop "load" string_of_num_type op (num_size op.ty)
  | Some (sz, ext) ->
    memop ("load" ^ pack_size sz ^ string_of_extension ext) string_of_num_type op (packed_size sz)


(* Function to convert instructions to string *)
let rec sexpr_of_instr e = 
  let head, inner =
  match e with 
  | IntConst (nt, i) -> Printf.sprintf "%s.const %d" (string_of_num_type nt) i, []
  | FloatConst (nt, f) -> Printf.sprintf "%s.const %f" (string_of_num_type nt) f, []
  | LocalGet idx -> Printf.sprintf "local.get %d" idx, []
  | LocalSet idx -> Printf.sprintf "local.set %d" idx, []
  | LocalTee idx -> Printf.sprintf "local.tee %d" idx, []
  | Add nt -> Printf.sprintf "%s.add" (string_of_num_type nt), []
  | Sub nt -> Printf.sprintf "%s.sub" (string_of_num_type nt), []
  | Mul nt -> Printf.sprintf "%s.mul" (string_of_num_type nt), []
  | Div nt -> Printf.sprintf "%s.div" (string_of_num_type nt), []
  | Shl nt -> Printf.sprintf "%s.shl" (string_of_num_type nt), []
  | Shr nt -> Printf.sprintf "%s.shr" (string_of_num_type nt), []
  | ShrU nt -> Printf.sprintf "%s.shr_u" (string_of_num_type nt), []
  | Ne nt -> Printf.sprintf "%s.ne" (string_of_num_type nt), []
  | Eqz nt -> Printf.sprintf "%s.eqz" (string_of_num_type nt), []
  | Call idx -> Printf.sprintf "call %d" idx, []
  | CallRef idx -> Printf.sprintf "call_ref %d" idx, []
  | Return -> "return", []
  | If (bt, es1, es2) -> 
    "if", sexpr_of_block_type bt @
      [Node ("then", list sexpr_of_instr es1); Node ("else", list sexpr_of_instr es2)]
  | Block (bt, es) -> "block", sexpr_of_block_type bt @ list sexpr_of_instr es
  | Loop (bt, es) -> "loop", sexpr_of_block_type bt @ list sexpr_of_instr es
  | Br idx -> Printf.sprintf "br %d" idx, []
  | BrIf idx -> Printf.sprintf "br_if %d" idx, []
  | BrTable (xs, x) -> "br_table " ^ String.concat " " (list string_of_int (xs @ [x])), []
  | Unreachable -> "unreachable", []
  | StructNew (idx, op) -> Printf.sprintf "struct.new%s %d" (string_of_initop op) idx, []
  | StructGet (x, y, exto) -> "struct.get" ^ opt_s string_of_extension exto ^ " " ^ string_of_int x ^ " " ^ string_of_int y, [] 
  | StructSet (x, y) -> Printf.sprintf "struct.set %s %s" (string_of_local_idx x) (string_of_local_idx y), [] 
  | Drop -> "drop", []
  | ArrayNew (idx, op) -> Printf.sprintf "array.new%s %d" (string_of_initop op) idx, []
  | ArrayGet (x, exto) -> Printf.sprintf "array.get%s %d" (opt_s string_of_extension exto) x, []
  | ArraySet x -> Printf.sprintf "array.set %d" x, []
  | ArrayLen -> Printf.sprintf "array.len", []
  | RefNull ht -> Printf.sprintf "ref.null" , [Atom (string_of_heap_type ht)]
  | RefAsNonNull -> "ref.as_non_null", []
  | RefEq -> "ref.eq", []
  | RefIsNull -> "ref.is_null", []
  | RefFunc idx -> Printf.sprintf "ref.func %d" idx, []
  | RefI31 -> "ref.i31", [] 
  | RefCast t -> "ref.cast", [Atom (str_of_ref_type t)]
  | GlobalGet idx -> Printf.sprintf "global.get %d" idx, []
  | GlobalSet idx -> Printf.sprintf "global.set %d" idx, []
  | I31Get exto -> Printf.sprintf "i31.get%s" (string_of_extension exto), []
  | MemoryInit x -> Printf.sprintf "memory.init %d" x, []
  | MemoryGrow -> Printf.sprintf "memory.grow", []
  | MemorySize -> Printf.sprintf "memory.size", []
  | Load op -> loadop op, []
  in 
  Node (head, inner)

(* Function to print a function *)
let func_with_name name f =
  let {ftype; locals; body} = f in
  Node ("func" ^ name,
    [Node ("type " ^ string_of_int ftype, [])] @
    decls "local" (List.map (fun loc -> loc.ltype) locals) @
    list sexpr_of_instr body
  )

let func_with_index off i f =
  func_with_name (" $" ^ string_of_int (off + i)) f

let func f =
  func_with_name "" f
