(module
  (type $0 (func (param i32 i32 i32) (result i32)))
  (type $1 (func (param i32) (result i32)))

  ;; Recursive Fibonacci function
  (func $aux
    (type $0)
    (local.get 0)
    (i32.eqz)
    (if
      (result i32)
      (then (local.get 1))
      (else
        (local.get 0)
        (i32.const 1)
        (i32.sub)
        (local.get 2)
        (local.get 1)
        (local.get 2)
        (i32.add)
        (call $aux)
      )
    )
  )

  ;; Main Fibonacci function entry point
  (func $fib (type $1) 
    (local.get 0) 
    (i32.const 0) 
    (i32.const 1) 
    (call $aux)
  )

  (func $fact (param $x i32) (result i32)
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

        (call $fact) ;; recursive call to factorial
        (local.get 0)
        (i32.mul)
      )
    )
  )
  ;; GCD function
  (func $gcd (param i32 i32) (result i32)
    (local i32)
    (block  
      (block  
        local.get 0
        br_if 0 
        local.get 1
        local.set 2
        br 1 
      )
      (loop  
        (local.get 1)
        (local.get 0)
        (local.tee 2)
        (i32.rem_u)
        (local.set 0)
        (local.get 2)
        (local.set 1)
        (local.get 0)
        (br_if 0)
      )
    ) 
    local.get 2
  )

  ;; New function to call GCD 1000 times
  (func $call_gcd_1000_times (result i32)
    (local $i i32)
    (local $result i32)

    ;; Initialize result
    (i32.const 0)
    (local.set $result)

    ;; Initialize loop counter
    (i32.const 0)
    (local.set $i)

    ;; Loop to call GCD function 1000 times
    (loop $loop
      ;; Call GCD function
      (i32.const 10)
      (call $fib)
      (i32.const 10)
      (call $fact)
      (call $gcd)
      
      ;; Update result (stores the result of the last GCD calculation)
      (local.set $result)

      ;; Increment loop counter
      (local.get $i)
      (i32.const 1)
      (i32.add)
      (local.set $i)

      ;; Check if we've reached 1000 iterations
      (local.get $i)
      (i32.const 1000)
      (i32.lt_s)
      (br_if $loop)
    )

    ;; Return the result of the last GCD call
    (local.get $result)
  )

  ;; Export the GCD function
  (export "gcd" (func $gcd))
  (export "fib" (func $fib))
  (export "fact" (func $fact))

  ;; Export the new function
  (export "call_gcd_1000_times" (func $call_gcd_1000_times))
)