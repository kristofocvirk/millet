(module
  (func $fact (param $x i32) (result i32)
    (local.get $x)
    (i32.const 1)

    (if (result i32) (i32.le_s)
      (then
        (local.get $x)
      )
      (else
        (local.get $x)
        (i32.const 1)
        (i32.sub)

        (call $fact)
        (local.get $x)
        (i32.mul)
      )
    )
  )
  (export "factorial" (func $fact))
)