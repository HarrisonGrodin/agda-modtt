signature POINTED =
  sig
    type t
    val x : t
  end

structure BoolPointed :> POINTED where type t = bool =
  struct
    type t = bool
    val x = false
  end

val true = not BoolPointed.x
