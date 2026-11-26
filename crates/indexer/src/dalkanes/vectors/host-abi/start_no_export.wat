;; Start function burns some fuel; the module has no __dalk_execute export.
(module (memory (export "memory") 1)
  (func $s (local i32)
    (loop $l (local.set 0 (i32.add (local.get 0) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get 0) (i32.const 1000)))))
  (start $s))
