(module
  (func $fib2 (param $n i32) (param $a i32) (param $b i32) (result i32)
    (if (result i32)
        (i32.eqz (local.get $n))
        (then (local.get $a))
        (else (call $fib2 (i32.sub (local.get $n)
                                   (i32.const 1))
                          (local.get $b)
                          (i32.add (local.get $a)
                                   (local.get $b))))))

  (func $fib (param i32) (result i32)
    (call $fib2 (local.get 0)
                (i32.const 0)   ;; seed value $a
                (i32.const 1))) ;; seed value $b

  (export "fib" (func $fib)))