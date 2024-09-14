type primitive =
  | CompareIntEq
  | CompareIntLt
  | CompareIntGt
  | CompareIntLe
  | CompareIntGe
  | CompareIntNe
  | CompareFloatEq
  | CompareFloatLt
  | CompareFloatGt
  | CompareFloatLe
  | CompareFloatGe
  | CompareFloatNe
  | IntegerAdd
  | IntegerMul
  | IntegerSub
  | IntegerDiv
  | IntegerMod
  | IntegerNeg
  | FloatAdd
  | FloatMul
  | FloatSub
  | FloatDiv
  | FloatPow
  | FloatNeg
  | ToString

(* Keep this list up to date with the type above, otherwise the missing primitives will not be loaded *)
let primitives =
  [
    CompareIntEq;
    CompareIntLt;
    CompareIntGt;
    CompareIntLe;
    CompareIntGe;
    CompareIntNe;
    CompareFloatEq;
    CompareFloatLt;
    CompareFloatGt;
    CompareFloatLe;
    CompareFloatGe;
    CompareFloatNe;
    IntegerAdd;
    IntegerMul;
    IntegerSub;
    IntegerDiv;
    IntegerMod;
    IntegerNeg;
    FloatAdd;
    FloatMul;
    FloatSub;
    FloatDiv;
    FloatPow;
    FloatNeg;
    ToString;
  ]

let primitive_name = function
  | CompareIntEq -> "__compare_int_eq__"
  | CompareIntLt -> "__compare_int_lt__"
  | CompareIntGt -> "__compare_int_gt__"
  | CompareIntLe -> "__compare_int_le__"
  | CompareIntGe -> "__compare_int_ge__"
  | CompareIntNe -> "__compare_int_ne__"
  | CompareFloatEq -> "__compare_float_eq__"
  | CompareFloatLt -> "__compare_float_lt__"
  | CompareFloatGt -> "__compare_float_gt__"
  | CompareFloatLe -> "__compare_float_le__"
  | CompareFloatGe -> "__compare_float_ge__"
  | CompareFloatNe -> "__compare_float_ne__"
  | IntegerAdd -> "__integer_add__"
  | IntegerMul -> "__integer_mul__"
  | IntegerSub -> "__integer_sub__"
  | IntegerDiv -> "__integer_div__"
  | IntegerMod -> "__integer_mod__"
  | IntegerNeg -> "__integer_neg__"
  | FloatAdd -> "__float_add__"
  | FloatMul -> "__float_mul__"
  | FloatSub -> "__float_sub__"
  | FloatDiv -> "__float_div__"
  | FloatPow -> "__float_pow__"
  | FloatNeg -> "__float_neg__"
  | ToString -> "to_string"
