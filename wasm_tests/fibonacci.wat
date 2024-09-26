(module
  (type $0 (func (param i32 i32 i32) (result i32)))
  (type $1 (func (param i32) (result i32)))

  ;; Recursive Fibonacci function
  (func $0
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
        (call 0)
      )
    )
  )

  ;; Main Fibonacci function entry point
  (func $1 (type $1) 
    (local.get 0) 
    (i32.const 0) 
    (i32.const 1) 
    (call 0)
  )

  ;; New function to call Fibonacci function 1000 times
  (func $call_fib_1000_times (param $x i32) (result i32)
    (local $i i32)
    (local $result i32)

    ;; Initialize result
    (i32.const 0)
    (local.set $result)

    ;; Initialize loop counter
    (i32.const 0)
    (local.set $i)

    ;; Loop to call Fibonacci function 1000 times
    (loop $loop
      ;; Call Fibonacci function
      (local.get $x)
      (call $1)
      
      ;; Update result (stores the result of the last Fibonacci calculation)
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

    ;; Return the result of the last Fibonacci call
    (local.get $result)
  )

  ;; Export the original Fibonacci function
  (export "fib" (func $1))

  ;; Export the new function
  (export "call_fib_1000_times" (func $call_fib_1000_times))
)
