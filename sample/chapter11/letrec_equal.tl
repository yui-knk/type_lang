(letrec eq : {x:Nat, y:Nat}->Bool =
  -> r:{x:Nat, y:Nat} {
    if iszero r.x
    then iszero r.y
    else
      if iszero r.y
      then iszero r.x
      else eq.({x=pred r.x, y=pred r.y})
  }
  in
  eq.({x=2, y=1})
)
