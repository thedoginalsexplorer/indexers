;; Start function never returns: instantiation runs out of fuel.
(module (memory (export "memory") 1)
  (func $s (loop $l (br $l))) (start $s)
  (func (export "__dalk_execute") (param i32 i32) (result i32) (i32.const 0)))
