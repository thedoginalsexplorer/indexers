(module
  (import "env" "alkane_sender" (func $s (param i32) (result i32)))
  (import "env" "return_data" (func $ret (param i32 i32)))
  (memory (export "memory") 1)
  (func (export "__dalk_execute") (param i32 i32) (result i32)
    (i32.store (i32.const 0) (call $s (i32.const 100)))
    (call $ret (i32.const 0) (i32.const 4))
    (i32.const 0)))
