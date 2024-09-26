(module
  ;; Factorial function
  (func $0 (param $x i32) (result i32)
    (local.get 0)
    (i32.const 1)

    (if (result i32) (i32.le_s)
      (then
        (local.get 0)
      )
      (else
        (local.get 0)
        (i32.const 1)
        (i32.sub)

        (call 0) ;; recursive call to factorial
        (local.get 0)
        (i32.mul)
      )
    )
  )
  ;; New function to call factorial 1000 times
  (func $call_factorial_1000_times (param $x i32) (result i32)
    (local $i i32)
    (local $result i32)
    
    (i32.const 1)
    (local.set $result)
    
    (i32.const 0)
    (local.set $i)
    
    (loop $loop
      (local.get $x)
      (call $0)
      
      (local.set $result)
      
      (local.get $i)
      (i32.const 1)
      (i32.add)
      (local.set $i)
      
      (local.get $i)
      (i32.const 1000)
      (i32.lt_s)
      (br_if $loop)
    )
    
    (local.get $result)
  )

  (export "call_factorial_1000_times" (func $call_factorial_1000_times))
  (export "factorial" (func 0))
)