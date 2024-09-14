(module
  (func $is_prime (export "is_prime") (param $n i32) (result i32)
    (local $i i32)

    ;; Handle special cases
    (if (i32.le_s (local.get $n) (i32.const 1))
      (then
        (return (i32.const 0))  ;; Not prime
      )
    )
    (if (i32.eq (local.get $n) (i32.const 2))
      (then
        (return (i32.const 1))  ;; Prime
      )
    )
    (if (i32.eqz (i32.rem_u (local.get $n) (i32.const 2)))
      (then
        (return (i32.const 0))  ;; Not prime (even number > 2)
      )
    )

    ;; Check odd numbers up to sqrt(n)
    (local.set $i (i32.const 3))
    (loop $loop
      (br_if $loop
        (i32.le_s
          (i32.mul (local.get $i) (local.get $i))
          (local.get $n)
        )
      )

      (if (i32.eqz (i32.rem_u (local.get $n) (local.get $i)))
        (then
          (return (i32.const 0))  ;; Not prime
        )
      )

      (local.set $i (i32.add (local.get $i) (i32.const 2)))
    )

    (i32.const 1)  ;; Prime
  )
)