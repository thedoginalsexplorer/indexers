;; Parent at 1:0: stages its own k=0xee, then     ;; child at 9:2 fails: call returns -1
;; (if (i32.ne (call $call (i64.const 9) (i64.const 2) (i32.const 0) (i32.const 0)
;; (i32.const 100) (i32.const 8) (i64.const 200000)) (i32.const -1))
;; (then (i32.const 21) (return))), then returns 0.
(module
  (import "env" "storage_set" (func $set (param i32 i32 i32 i32)))
  (import "env" "call" (func $call (param i64 i64 i32 i32 i32 i32 i64) (result i32)))
  (memory (export "memory") 1)
  (data (i32.const 0) "k")
  (data (i32.const 1) "\ee")
  (func (export "__dalk_execute") (param i32 i32) (result i32)
    (call $set (i32.const 0) (i32.const 1) (i32.const 1) (i32.const 1))
    ;; child at 9:2 fails: call returns -1
    (if (i32.ne (call $call (i64.const 9) (i64.const 2) (i32.const 0) (i32.const 0)
         (i32.const 100) (i32.const 8) (i64.const 200000)) (i32.const -1))
      (then (i32.const 21) (return)))
    (i32.const 0)))
