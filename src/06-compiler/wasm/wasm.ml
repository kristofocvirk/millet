open Printf
(* Value Types *)
type numeric_type = 
  | I32
  | I64
  | F32
  | F64

type abs_heap_type =
  | FuncRef
  | ExternRef
  | EqRef
  | I31Ref
  | DataRef
  | StructRef
  | ArrayRef

type ref_type = 
  | AbsHeapType of abs_heap_type
  | HeapType of int

type value_type =
  | NumType of numeric_type
  | RefType of ref_type 

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

type comp_type =
  | ArrayType of array_type
  | FuncType of func_type 
  | StructType of struct_type

(* Instructions *)
type instr =
  (* Constants *)
  | Const of numeric_type * int32
  | LocalGet of int
  
  (* Arithmetic operations *)
  | Add of numeric_type 
  | Sub of numeric_type 
  | Mul of numeric_type
  | Div of numeric_type 
  
  (* Control flow *)
  | Call of int
  | Return
  | If of instr list * instr list  (* (if (then ... ) (else ... )) *)
  | Block of instr list  (* (block ... ) *)
  | Loop of instr list   (* (loop ... ) *)
  | Br of int            (* (br <label_index>) *)
  | BrIf of int          (* (br_if <label_index>) *)
  | BrTable of int list * int (* (br_table <labels> <default>) *)
  | Unreachable          (* (unreachable) *)
  
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
  name : string;
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
  types : comp_type list;
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

let string_of_abs_heap_type = function
  | FuncRef -> "funcref"
  | ExternRef -> "externref"
  | EqRef -> "eqref"
  | I31Ref -> "i31ref"
  | DataRef -> "dataref"
  | StructRef -> "structref"
  | ArrayRef -> "arrayref"

let string_of_ref_type = function
  | AbsHeapType aht -> string_of_abs_heap_type aht
  | HeapType ht -> string_of_int ht


let string_of_numeric_type (num_typ : numeric_type) = 
  match num_typ with
  | I32 -> "i32"
  | I64 -> "i64"
  | F32 -> "f32"
  | F64 -> "f64"

let string_of_value_type = function
  | NumType nt -> string_of_numeric_type nt
  | RefType rt -> string_of_ref_type rt

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

let string_of_comp_type = function 
  | ArrayType at -> string_of_array_type at 
  | StructType st -> string_of_struct_type st
  | FuncType ft -> string_of_func_type ft

(* Instructions *)
let rec string_of_instr = function
  | Const (vt, value) -> sprintf "%s.const %ld\n" (string_of_numeric_type vt) value
  | LocalGet i -> sprintf "local.get %s\n" (string_of_int i)
  | Add nt -> sprintf "%s.add\n" (string_of_numeric_type nt)
  | Sub nt -> sprintf "%s.sub\n" (string_of_numeric_type nt)
  | Mul nt -> sprintf "%s.mul\n" (string_of_numeric_type nt)
  | Div nt -> sprintf "%s.div\n" (string_of_numeric_type nt)
  | Call index -> sprintf "call %d\n" index
  | Return -> "return\n"
  | If (then_instrs, else_instrs) -> 
      let then_part = String.concat "" (List.map string_of_instr then_instrs) in
      let else_part = String.concat "" (List.map string_of_instr else_instrs) in
      sprintf "(if\n(then\n%s)\n(else\n%s))\n" then_part else_part
  | Block instrs ->
      let body = String.concat "" (List.map string_of_instr instrs) in
      sprintf "(block\n%s)\n" body
  | Loop instrs ->
      let body = String.concat "" (List.map string_of_instr instrs) in
      sprintf "(loop\n%s)" body
  | Br label_index -> sprintf "br %d\n" label_index
  | BrIf label_index -> sprintf "br_if %d\n" label_index
  | BrTable (labels, default) ->
      let labels_str = String.concat " " (List.map string_of_int labels) in
      sprintf "br_table %s %d\n" labels_str default
  | Unreachable -> "unreachable\n"
  | StructNew st -> sprintf "struct.new %s\n" (string_of_struct_type st)
  | StructGet (_, index) -> sprintf "struct.get %d\n" index
  | StructSet (_, index) -> sprintf "struct.set %d\n" index
  | ArrayNew at -> sprintf "array.new %s\n" (string_of_array_type at)
  | ArrayGet _-> "array.get\n"
  | ArraySet _ -> "array.set\n"
  | RefNull ht -> sprintf "ref.null %s\n" (string_of_heap_type ht)
  | RefIsNull -> "ref.is_null\n"
  | RefFunc index -> sprintf "ref.func %d\n" index
  
let string_of_instr_list instrs =
  String.concat " " (List.map string_of_instr instrs)

(* Function *)
let string_of_func (f : func) =
  let name = f.name in
  let params = String.concat " " (List.map string_of_value_type f.ftype.params) in
  let results = String.concat " " (List.map string_of_value_type f.ftype.results) in
  let locals = String.concat " " (List.map string_of_value_type f.locals) in
  let body = string_of_instr_list f.body in
  sprintf "(func $%s (param %s) (result %s) (local %s)\n %s)" name params results locals body

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
let append_if_non_empty str acc =
  if str = "" then acc else acc ^ "\n" ^ str

let string_of_module m =
  let types = String.concat "\n" (List.map string_of_comp_type m.types) in
  let funcs = String.concat "\n" (List.map string_of_func m.funcs) in
  let tables = String.concat "\n" (List.map string_of_table m.tables) in
  let mems = String.concat "\n" (List.map string_of_mem m.mems) in
  let globals = String.concat "\n" (List.map string_of_global m.globals) in
  let exports = String.concat "\n" (List.map string_of_export m.exports) in
  let module_body = ""
    |> append_if_non_empty types
    |> append_if_non_empty funcs
    |> append_if_non_empty tables
    |> append_if_non_empty mems
    |> append_if_non_empty globals
    |> append_if_non_empty exports
  in
  sprintf "(module %s)" module_body
 

(* Example usage *)
let example_module_1 = {
  types = [FuncType {params = [NumType I32; NumType I32]; results = [NumType I32]}];
  funcs = [{
    name = "test";
    ftype = {params = [NumType I32]; results = [NumType I32]};
    locals = [NumType I32];
    body = [LocalGet 0; Const (I32, 42l); Add I32; Return];
  }];
  tables = [];
  mems = [];
  globals = [];
  exports = [{name = "add"; desc = FuncExport 0}];
}

let example_module_2 = {
  types = [FuncType {params = [NumType I32; NumType I32]; results = [NumType I32]}];
  funcs = [{
    name = "test";
    ftype = {params = [NumType I32; NumType I32]; results = [NumType I32]};
    locals = [NumType I32];
    body = [
      Block [
        If (
          [Const (I32, 42l); Add I32],
          [Const (I32, 1l); Sub I32]
        );
        Loop [
          BrIf 0;
          Br 1
        ]
      ];
      Return
    ];
  }];
  tables = [];
  mems = [];
  globals = [];
  exports = [{name = "add"; desc = FuncExport 0}];
}

let () =
  let wat = string_of_module example_module_2 in
  print_endline wat;
  let wat = string_of_module example_module_1 in
  print_endline wat