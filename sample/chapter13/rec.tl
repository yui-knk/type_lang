let a = ref (-> x:Unit {
  x
})

in

(
  a := (-> y:Unit {
    (!a)(y)
  });

  (!a)(unit)
)
