open Printf
(* Value Types *)
type value_type =
  | I32
  | I64
  | F32
  | F64
  | RefType of ref_type

and ref_type =
  | FuncRef
  | ExternRef
  | EqRef
  | I31Ref
  | DataRef
  | StructRef
  | ArrayRef

(* Heap Types *)
type heap_type =
  | FuncHeapType
  | ExternHeapType
  | EqHeapType
  | I31HeapType
  | DataHeapType
  | StructHeapType
  | ArrayHeapType

(* Struct Types *)
type struct_field = {
  field_type : value_type;
  mutable_ : bool;  (* Indicates if the field is mutable *)
}

type struct_type = {
  fields : struct_field list;
}

(* Array Types *)
type array_type = {
  element_type : value_type;
  mutable_ : bool;  (* Indicates if the array elements are mutable *)
}

(* Function Types *)
type func_type = {
  params : value_type list;
  results : value_type list;
}

(* Instructions *)
type instr =
  (* Constants *)
  | Const of value_type * int32
  
  (* Arithmetic operations *)
  | Add of value_type
  | Sub of value_type
  | Mul of value_type
  | Div of value_type
  
  (* Control flow *)
  | Call of int
  | Return
  
  (* Struct operations *)
  | StructNew of struct_type
  | StructGet of struct_type * int
  | StructSet of struct_type * int

  (* Array operations *)
  | ArrayNew of array_type
  | ArrayGet of array_type
  | ArraySet of array_type

  (* Reference types operations *)
  | RefNull of heap_type
  | RefIsNull
  | RefFunc of int

(* Function *)
type func = {
  ftype : func_type;
  locals : value_type list;
  body : instr list;
}

(* Export *)
type export_desc =
  | FuncExport of int
  | TableExport of int
  | MemExport of int
  | GlobalExport of int

type export = {
  name : string;
  desc : export_desc;
}

(* Module *)
type module_ = {
  types : func_type list;
  funcs : func list;
  tables : table list;
  mems : mem list;
  globals : global list;
  exports : export list;
}

(* Tables *)
and table = {
  element_type : ref_type;
  initial_size : int;
  max_size : int option;
}

(* Memory *)
and mem = {
  initial_pages : int;
  max_pages : int option;
}

(* Global *)
and global = {
  global_type : value_type;
  mutable_ : bool;
  init : instr list;
}


(* Value Types *)
let rec string_of_value_type = function
  | I32 -> "i32"
  | I64 -> "i64"
  | F32 -> "f32"
  | F64 -> "f64"
  | RefType rt -> string_of_ref_type rt

and string_of_ref_type = function
  | FuncRef -> "funcref"
  | ExternRef -> "externref"
  | EqRef -> "eqref"
  | I31Ref -> "i31ref"
  | DataRef -> "dataref"
  | StructRef -> "structref"
  | ArrayRef -> "arrayref"

let string_of_heap_type = function
  | FuncHeapType -> "func"
  | ExternHeapType -> "extern"
  | EqHeapType -> "eq"
  | I31HeapType -> "i31"
  | DataHeapType -> "data"
  | StructHeapType -> "struct"
  | ArrayHeapType -> "array"

(* Function Types *)
let string_of_func_type ft =
  let params = String.concat " " (List.map string_of_value_type ft.params) in
  let results = String.concat " " (List.map string_of_value_type ft.results) in
  sprintf "(func (param %s) (result %s))" params results

(* Struct Types *)
let string_of_struct_field (sf : struct_field) =
  let mutability = if sf.mutable_ then "(mut " ^ string_of_value_type sf.field_type ^ ")" else string_of_value_type sf.field_type in
  sprintf "(field %s)" mutability

let string_of_struct_type st =
  let fields = String.concat " " (List.map string_of_struct_field st.fields) in
  sprintf "(struct %s)" fields

(* Array Types *)
let string_of_array_type (at : array_type) =
  let mutability = if at.mutable_ then "(mut " ^ string_of_value_type at.element_type ^ ")" else string_of_value_type at.element_type in
  sprintf "(array %s)" mutability

(* Instructions *)
let string_of_instr = function
  | Const (vt, value) -> sprintf "(%s.const %ld)" (string_of_value_type vt) value
  | Add vt -> sprintf "(%s.add)" (string_of_value_type vt)
  | Sub vt -> sprintf "(%s.sub)" (string_of_value_type vt)
  | Mul vt -> sprintf "(%s.mul)" (string_of_value_type vt)
  | Div vt -> sprintf "(%s.div)" (string_of_value_type vt)
  | Call index -> sprintf "(call %d)" index
  | Return -> "(return)"
  | StructNew st -> sprintf "(struct.new %s)" (string_of_struct_type st)
  | StructGet (_, index) -> sprintf "(struct.get %d)" index
  | StructSet (_, index) -> sprintf "(struct.set %d)" index
  | ArrayNew at -> sprintf "(array.new %s)" (string_of_array_type at)
  | ArrayGet _-> "(array.get)"
  | ArraySet _ -> "(array.set)"
  | RefNull ht -> sprintf "(ref.null %s)" (string_of_heap_type ht)
  | RefIsNull -> "(ref.is_null)"
  | RefFunc index -> sprintf "(ref.func %d)" index

let string_of_instr_list instrs =
  String.concat " " (List.map string_of_instr instrs)

(* Function *)
let string_of_func f =
  let params = String.concat " " (List.map string_of_value_type f.ftype.params) in
  let results = String.concat " " (List.map string_of_value_type f.ftype.results) in
  let locals = String.concat " " (List.map string_of_value_type f.locals) in
  let body = string_of_instr_list f.body in
  sprintf "(func (param %s) (result %s) (local %s) %s)" params results locals body

(* Export *)
let string_of_export_desc = function
  | FuncExport index -> sprintf "(func %d)" index
  | TableExport index -> sprintf "(table %d)" index
  | MemExport index -> sprintf "(memory %d)" index
  | GlobalExport index -> sprintf "(global %d)" index

let string_of_export e =
  sprintf "(export \"%s\" %s)" e.name (string_of_export_desc e.desc)

(* Tables *)
let string_of_table t =
  let max_size = match t.max_size with
    | Some max -> string_of_int max
    | None -> "" in
  sprintf "(table %d %s %s)" t.initial_size max_size (string_of_ref_type t.element_type)

(* Memories *)
let string_of_mem m =
  let max_pages = match m.max_pages with
    | Some max -> string_of_int max
    | None -> "" in
  sprintf "(memory %d %s)" m.initial_pages max_pages

(* Globals *)
let string_of_global g =
  let mutability = if g.mutable_ then "(mut " ^ string_of_value_type g.global_type ^ ")" else string_of_value_type g.global_type in
  let init = string_of_instr_list g.init in
  sprintf "(global %s %s)" mutability init

(* Module *)
let string_of_module m =
  let types = String.concat "\n" (List.map string_of_func_type m.types) in
  let funcs = String.concat "\n" (List.map string_of_func m.funcs) in
  let tables = String.concat "\n" (List.map string_of_table m.tables) in
  let mems = String.concat "\n" (List.map string_of_mem m.mems) in
  let globals = String.concat "\n" (List.map string_of_global m.globals) in
  let exports = String.concat "\n" (List.map string_of_export m.exports) in
  sprintf "(module\n%s\n%s\n%s\n%s\n%s\n%s)" types funcs tables mems globals exports
