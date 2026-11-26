;; Source: dogex src/alkanes/runtime.rs, test staticcall_height_from_oracle_like (child, deployed at 9:1)
(module
  (import "env" "alkane_block" (func $blk (result i64)))
  (import "env" "return_data" (func $ret (param i32 i32)))
  (memory (export "memory") 1)
  (func (export "__dalk_execute") (param i32 i32) (result i32)
    (i64.store (i32.const 0) (call $blk))
    (call $ret (i32.const 0) (i32.const 8))
    (i32.const 0)))
