open Utils
open Binaryen
module Ast = Language.Ast
module Const = Language.Const
module Primitives = Language.Primitives

let binary_function f = function
  | Ast.Tuple [ expr1; expr2 ] -> f expr1 expr2
  | expr -> Error.runtime "Pair expected but got %t" (Ast.print_expression expr)

let get_int wasm_mod = function
  | Ast.Const (Const.Integer n) -> Expression.Const.make wasm_mod (Literal.int32 (Int32.of_int n))
  | expr ->
      Error.runtime "Integer expected but got %t" (Ast.print_expression expr)

let get_float wasm_mod = function
  | Ast.Const (Const.Float n) -> Expression.Const.make wasm_mod (Literal.float32 n)
  | expr ->
      Error.runtime "Float expected but got %t" (Ast.print_expression expr)

let int_to f expr =
  let n = get_int expr in
  f n

let int_int_to f expr =
  binary_function
    (fun expr1 expr2 ->
      let n1 = get_int expr1 in
      let n2 = get_int expr2 in
      f n1 n2)
    expr

let float_to f expr =
  let n = get_float expr in
  f n

let float_float_to f expr =
  binary_function
    (fun expr1 expr2 ->
      let n1 = get_float expr1 in
      let n2 = get_float expr2 in
      f n1 n2)
    expr

let int_to_int f =
  int_to (fun n -> Ast.Return (Ast.Const (Const.Integer (f n))))

let int_int_to_int f =
  int_int_to (fun n1 n2 -> Ast.Return (Ast.Const (Const.Integer (f n1 n2))))

let float_to_float f =
  float_to (fun n -> Ast.Return (Ast.Const (Const.Float (f n))))

let float_float_to_float f =
  float_float_to (fun n1 n2 -> Ast.Return (Ast.Const (Const.Float (f n1 n2))))

let rec comparable_expression = function
  | Ast.Var _ -> true
  | Const _ -> true
  | Annotated (e, _) -> comparable_expression e
  | Tuple es -> List.for_all comparable_expression es
  | Variant (_, e) -> Option.fold ~none:true ~some:comparable_expression e
  | Lambda _ -> false
  | RecLambda _ -> false

let comparison f =
  binary_function (fun e1 e2 ->
      if not (comparable_expression e1) then
        Error.runtime "Incomparable expression %t"
          (Ast.print_expression ~max_level:0 e1)
      else if not (comparable_expression e2) then
        Error.runtime "Incomparable expression %t"
          (Ast.print_expression ~max_level:0 e2)
      else Ast.Return (Ast.Const (Const.Boolean (f e1 e2))))

let primitive_function wasm_mod = function
  | Primitives.CompareEq -> Expression.Binary.make wasm_mod Op.eq_float32
  | Primitives.CompareLt -> Expression.Binary.make wasm_mod Op.lt_float32
  | Primitives.CompareGt -> Expression.Binary.make wasm_mod Op.gt_float32
  | Primitives.CompareLe -> Expression.Binary.make wasm_mod Op.le_float32
  | Primitives.CompareGe -> Expression.Binary.make wasm_mod Op.ge_float32
  | Primitives.CompareNe -> Expression.Binary.make wasm_mod Op.ne_float32
  | Primitives.IntegerAdd -> Expression.Binary.make wasm_mod Op.add_float32
  | Primitives.IntegerMul -> Expression.Binary.make wasm_mod Op.mul_float32
  | Primitives.IntegerSub -> Expression.Binary.make wasm_mod Op.sub_float32
  | Primitives.IntegerDiv -> (fun x y -> Expression.Unary.make wasm_mod Op.floor_float32 (Expression.Binary.make wasm_mod Op.div_float32 x y))
  | Primitives.IntegerMod -> (fun x y -> Expression.Binary.make wasm_mod Op.sub_float32 x (Expression.Binary.make wasm_mod Op.mul_float32 (Expression.Unary.make wasm_mod Op.floor_float32 (Expression.Binary.make wasm_mod Op.div_float32 x y)) y))
  | Primitives.IntegerNeg -> Expression.Binary.make wasm_mod Op.neg_float32
  | Primitives.FloatAdd -> Expression.Binary.make wasm_mod Op.add_float32
  | Primitives.FloatMul -> Expression.Binary.make wasm_mod Op.mul_float32
  | Primitives.FloatSub -> Expression.Binary.make wasm_mod Op.sub_float32
  | Primitives.FloatDiv -> Expression.Binary.make wasm_mod Op.div_float32
  | Primitives.FloatPow -> Error.runtime "power not implemented yet"
  | Primitives.FloatNeg -> Expression.Binary.make wasm_mod Op.neg_float32
  | Primitives.ToString -> Error.runtime "tostring not implemented yet"
