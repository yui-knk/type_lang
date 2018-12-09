(fix -> plus:{x:Nat, y:Nat}->Nat {
  -> r:{x:Nat, y:Nat} {
      if iszero r.y
      then r.x
      else plus.({x=succ r.x, y=pred r.y})
  }
}).({x=2, y=10})
