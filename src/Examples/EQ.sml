exception Error

signature EQ =
  sig
    type t
    val eq : t -> t -> bool
  end

structure BoolEq :> EQ where type t = bool =
  struct
    type t = bool
    val eq = fn b1 => fn b2 => if b1 then b2 else not b2
  end

structure BoolEqSealed :> EQ = BoolEq

(* structure BoolEqError1 = error *)

structure BoolEqError2 :> EQ where type t = bool =
  struct
    type t = bool
    val eq = fn b1 => raise Error
  end

val false = BoolEq.eq true false
