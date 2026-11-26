;; Child at 9:2 for the nested-rollback cases: bumps its counter "k", mints 5 of itself
;; to account "A", returns the 8-byte counter, then exits 1.
(module
  (import "env" "storage_get" (func $get (param i32 i32 i32 i32) (result i32)))
  (import "env" "storage_set" (func $set (param i32 i32 i32 i32)))
  (import "env" "ledger_mint" (func $mint (param i64 i64 i32 i32 i64 i64) (result i32)))
  (import "env" "return_data" (func $ret (param i32 i32)))
  (memory (export "memory") 1)
  (data (i32.const 0) "kA")
  (func (export "__dalk_execute") (param i32 i32) (result i32)
    (i64.store (i32.const 16) (i64.const 0))
    (drop (call $get (i32.const 0) (i32.const 1) (i32.const 16) (i32.const 8)))
    (i64.store (i32.const 16) (i64.add (i64.load (i32.const 16)) (i64.const 1)))
    (call $set (i32.const 0) (i32.const 1) (i32.const 16) (i32.const 8))
    (drop (call $mint (i64.const 9) (i64.const 2) (i32.const 1) (i32.const 1)
      (i64.const 5) (i64.const 0)))
    (call $ret (i32.const 16) (i32.const 8))
    (i32.const 1)))
