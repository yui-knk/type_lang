let ieio = (fix -> ieio:{iseven:Nat->Bool, isodd:Nat->Bool} {
  {
    iseven = -> x:Nat {
      if iszero x
      then true
      else ieio.isodd.(pred x)
    },
    isodd = -> x:Nat {
      if iszero x
      then false
      else ieio.iseven.(pred x)
    }
  }
})

in

ieio.iseven.(6)
