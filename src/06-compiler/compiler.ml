module W =
struct
  module Wasm = Wasm
  include Wasm
  include Wasm.Ast
  include Wasm.Types
  include Wasm.Values
  include Wasm.Operators
  type region = Wasm.Source.region
end

(*helper functions*)
let (@@) = W.Source.(@@)
let i32 = W.I32.of_int_s
let (+%) = Int32.add
let (/%) = Int32.div

(*compilation context entities*)

type 'a entities = {mutable list : 'a option ref list; mutable cnt : int32}

let make_entities () = {list = []; cnt = 0l}
let get_entities ents = List.rev (List.map (fun r -> Option.get !r) ents.list)

let alloc_entity ents : int32 * 'a option ref =
  let idx = ents.cnt in
  let r = ref None in
  ents.cnt <- idx +% 1l;
  ents.list <- r :: ents.list;
  idx, r

let define_entity r ent =
  r := Some ent

let emit_entity ents ent : int32 =
  let idx, r = alloc_entity ents in
  define_entity r ent;
  idx

let implicit_entity ents : int32 =
  assert (ents.list = []);
  let idx = ents.cnt in
  ents.cnt <- idx +% 1l;
  idx

let compile _ = print_endline "wasm" 

(* Compilation context *)

module DefTypes = Map.Make(struct type t = W.sub_type let compare = compare end)
module Refs = Set.Make(Int32)
module Intrinsics = Map.Make(String)

type internal =
  { types : W.sub_type W.Source.phrase entities;
    globals : W.global entities;
    funcs : W.func entities;
    memories : W.memory entities;
    datas : W.data_segment entities;
    imports : W.import entities;
    exports : W.export entities;
    locals : W.local entities;
    instrs : W.instr entities;
    refs : Refs.t ref;
    data_offset : int32 ref;
    start : W.idx option ref;
    deftypes : int32 DefTypes.t ref;
    intrinsics : int32 Intrinsics.t ref;
  }

type 'a ctxt = {ext : 'a; int : internal}

let make_internal () =
  { types = make_entities ();
    globals = make_entities ();
    funcs = make_entities ();
    memories = make_entities ();
    datas = make_entities ();
    imports = make_entities ();
    exports = make_entities ();
    locals = make_entities ();
    instrs = make_entities ();
    refs = ref Refs.empty;
    data_offset = ref 0l;
    start = ref None;
    deftypes = ref DefTypes.empty;
    intrinsics = ref Intrinsics.empty;
  }

let make_ctxt ext = {ext; int = make_internal ()}