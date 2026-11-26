;; Burns every unit of fuel it is granted (infinite loop, traps out of fuel).
(module (memory (export "memory") 1)
  (func (export "__dalk_execute") (param i32 i32) (result i32)
    (loop $l (br $l)) (i32.const 0)))
