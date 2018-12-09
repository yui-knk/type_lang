(letrec plus : {x:Nat, y:Nat}->Nat =
  -> r:{x:Nat, y:Nat} {
      if iszero r.y
      then r.x
      else plus.({x=succ r.x, y=pred r.y})
  }
  in
  (letrec times : {x:Nat, y:Nat}->Nat =
    -> r:{x:Nat, y:Nat} {
        if iszero (pred r.y)
        then r.x
        else plus.({x=r.x, y=times.({x=r.x, y=pred r.y})})
    }
    in
    (letrec factorial : Nat->Nat =
      -> x:Nat {
          if iszero (pred x)
          then x
          else times.({x=x, y=factorial.(pred x)})
      }
      in
      factorial.(5)
    )
  )
)
