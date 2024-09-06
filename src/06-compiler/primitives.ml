module Ast = Language.Ast
module Const = Language.Const
module Primitives = Language.Primitives
module Emit = Emit
module Types = Wasm.Types
module Wasm = Wasm

let primitve_name_list = List.map Primitives.primitive_name Primitives.primitives

let binary_primitive_func ctxt instr t= 
  let fieldt = Types.FieldT (Cons, ValStorageT t) in
  let sub =  Emit.emit_type ctxt (Types.SubT (NoFinal, [], (DefStructT (StructT [fieldt; fieldt])))) in
  let input_ty = Types.RefT (NoNull, VarHT (StatX sub)) in 
  Emit.emit_func ctxt [input_ty] [t] (fun ctxt _ ->
      let src = Emit.emit_param ctxt in
      List.iter (Emit.emit_instr ctxt) [
        LocalGet src;
        StructGet (sub, 0, None); 
        LocalGet src;
        StructGet (sub, 1, None); 
        instr;
      ]
    )

let comparison_func ctxt instr= 
  let block bt es = Wasm.Ast.Block (bt, es) in
  let fieldt = Types.FieldT (Cons, ValStorageT (RefT (NoNull, EqHT))) in
  let sub =  Emit.emit_type ctxt (Types.SubT (NoFinal, [], (DefStructT (StructT [fieldt; fieldt])))) in
  let input_ty = Types.RefT (NoNull, VarHT (StatX sub)) in 
  Emit.emit_func ctxt [input_ty; NumT I32T] [NumT I32T] (fun ctxt _ ->
      let str = Emit.emit_param ctxt in
      let oper = Emit.emit_param ctxt in
      let res = Emit.emit_local ctxt { ltype = NumT I32T} in
      List.iter (Emit.emit_instr ctxt) [
          block (Types.ValBlockType None) (List.map (fun e -> e) Wasm.[
            block (Types.ValBlockType None) (List.map (fun e -> e) Wasm.[
                Ast.LocalGet oper;
                BrTable ([0;1], 0); 
                LocalGet str; 
                StructGet (sub, 0, None);
                LocalGet str; 
                StructGet (sub, 1, None);
                instr Types.I32T;
                LocalSet res;
                Br 1;
            ]); 
              LocalGet str; 
              StructGet (sub, 0, None);
              StructGet (sub, 1, None);
              instr Types.F64T;
              LocalSet res;
              Br 0;
          ]);
          LocalGet (res);
        ] 
    )

let unray_primitive_func ctxt instr t= 
  Emit.emit_func ctxt [t] [t] (fun ctxt _ ->
      let src = Emit.emit_param ctxt in
      List.iter (Emit.emit_instr ctxt) [
        LocalGet src;
        instr;
      ]
    )

let unray_primitive_neg ctxt = 
  Emit.emit_func ctxt [NumT I32T] [NumT I32T] (fun ctxt _ ->
      let src = Emit.emit_param ctxt in
      List.iter (Emit.emit_instr ctxt) [
        IntConst (I32T, 0);
        LocalGet src;
        Sub I32T;
      ]
    )

let simple_primitive_function ctxt prim : (int  * int) option= 
  match prim with 
  | Primitives.CompareEq -> Some (comparison_func ctxt (fun x -> Eqz x), 2)
  | Primitives.CompareLt -> Some (comparison_func ctxt (fun x -> Lt x), 2)
  | Primitives.CompareGt -> Some (comparison_func ctxt (fun x -> Gt x), 2)
  | Primitives.CompareLe -> Some (comparison_func ctxt (fun x -> Le x), 2)
  | Primitives.CompareGe -> Some (comparison_func ctxt (fun x -> Ge x), 2)
  | Primitives.CompareNe -> Some (comparison_func ctxt (fun x -> Ne x), 2)
  | Primitives.IntegerAdd -> Some (binary_primitive_func ctxt (Wasm.Ast.Add I32T) (NumT I32T), 1)
  | Primitives.IntegerMul -> Some (binary_primitive_func ctxt (Wasm.Ast.Mul I32T) (NumT I32T), 1)
  | Primitives.IntegerSub -> Some (binary_primitive_func ctxt (Wasm.Ast.Sub I32T) (NumT I32T), 1)
  | Primitives.IntegerDiv -> Some (binary_primitive_func ctxt (Wasm.Ast.DivS I32T) (NumT I32T), 1)
  | Primitives.IntegerMod -> Some (binary_primitive_func ctxt (Wasm.Ast.Rem I32T) (NumT I32T), 1)
  | Primitives.IntegerNeg -> Some (unray_primitive_neg ctxt, 1)
  | Primitives.FloatAdd -> Some (binary_primitive_func ctxt (Wasm.Ast.Add F64T) (NumT F64T), 1)
  | Primitives.FloatMul -> Some (binary_primitive_func ctxt (Wasm.Ast.Mul F64T) (NumT F64T), 1)
  | Primitives.FloatSub -> Some (binary_primitive_func ctxt (Wasm.Ast.Sub F64T) (NumT F64T), 1)
  | Primitives.FloatDiv -> Some (binary_primitive_func ctxt (Wasm.Ast.Div F64T) (NumT F64T), 1)
  | Primitives.FloatPow -> None
  | Primitives.FloatNeg -> Some (unray_primitive_func ctxt (Wasm.Ast.Neg F64T) (NumT F64T), 1)
  | Primitives.ToString -> None