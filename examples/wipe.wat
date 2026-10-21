(module
  (memory 1)
  (func (param i32 i32)
    (loop
      (local.get 1)
      (if
        (then
          (local.get 0)
          (i32.const 0)
          (i32.store8)
          (local.get 0)
          (i32.const 1)
          (i32.add)
          (local.set 0)
          (local.get 1)
          (i32.const 1)
          (i32.sub)
          (local.set 1)
          (br 1)
        )
      )
    )
  )
)
