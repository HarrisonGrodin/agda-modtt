{-# OPTIONS --rewriting #-}

module Examples.POINTED where

open import ModTT
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

POINTED : Sig
POINTED = Σ type λ t → ⟨| t |⟩

-- POINTED where type t = t
POINTED' : Val type → Sig
POINTED' t =
  Ext POINTED λ lock →
    t , trivially (conn/dyn {t = t}) lock

BoolPointed : Cmd (POINTED' bool)
BoolPointed =
  ret (
    (bool , ff) ,
    λ lock → Eq.cong (bool ,_) (trivially-eq (conn/dyn {t = bool}) lock)
  )

private
  ex : Cmd ⟨| bool |⟩
  ex =
    bind BoolPointed λ ((t , x) , h) →
      let
        where-clause : ◯ (t ≡ bool)
        where-clause u = Eq.cong proj₁ (h u)
      in
      ret (not (x via where-clause))
    where
      not : Val ⟨| bool |⟩ → Val ⟨| bool |⟩
      not b = if {⟨| bool |⟩} b ff tt

  _ : ex ≡ ret tt
  _ = refl
