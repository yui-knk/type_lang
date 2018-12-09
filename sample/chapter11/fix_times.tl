let plus = (fix -> plus:{x:Nat, y:Nat}->Nat {
  -> r:{x:Nat, y:Nat} {
      if iszero r.y
      then r.x
      else plus.({x=succ r.x, y=pred r.y})
  }
})

in

(fix -> times:{x:Nat, y:Nat}->Nat {
    -> r:{x:Nat, y:Nat} {
        if iszero (pred r.y)
        then r.x
        else plus.({x=r.x, y=times.({x=r.x, y=pred r.y})})
    }
}).({x=3, y=11})
