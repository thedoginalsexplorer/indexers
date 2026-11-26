;; Source: dogex src/alkanes/runtime.rs, test alkane_value_and_incoming_host
;; Note: on-chain calls always have an empty incoming list in v0.1 (spec section 6.5).
;; This case uses the simulation override to exercise incoming_get's 32-byte layout.
(module
  (import "env" "alkane_value" (func $v (result i64)))
  (import "env" "incoming_count" (func $c (result i32)))
  (import "env" "incoming_get" (func $g (param i32 i32) (result i32)))
  (import "env" "return_data" (func $ret (param i32 i32)))
  (memory (export "memory") 1)
  (func (export "__dalk_execute") (param i32 i32) (result i32)
    (i64.store (i32.const 0) (call $v))
    (i32.store (i32.const 8) (call $c))
    (drop (call $g (i32.const 0) (i32.const 16)))
    (call $ret (i32.const 0) (i32.const 48))
    (i32.const 0)))
