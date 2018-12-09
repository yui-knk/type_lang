let diverge = -> u:Unit {
  fix -> x:Nat {
    x
  }
}

in

diverge.(unit)
