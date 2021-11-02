{-# OPTIONS --rewriting #-}

module Examples.EQ where

open import ModTT
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

EQ : Sig
EQ = Σ type λ t → ⟨| t ⇀ t ⇀ bool |⟩

-- EQ where type t = t
EQ' : Val type → Sig
EQ' t =
  Ext EQ λ lock →
    t , trivially (conn/dyn {t = t ⇀ t ⇀ bool}) lock

BoolEq : Cmd (EQ' bool)
BoolEq =
  ret (
    (bool , λ b₁ → ret (λ b₂ → ret (if {⟨| bool |⟩} b₁ b₂ (not b₂)))) ,
    λ lock → Eq.cong (bool ,_) (trivially-eq (conn/dyn {t = bool ⇀ bool ⇀ bool}) lock)
  )
  where
    not : Val ⟨| bool |⟩ → Val ⟨| bool |⟩
    not b = if {⟨| bool |⟩} b ff tt

BoolEqSealed : Cmd EQ
BoolEqSealed = bind BoolEq λ (X , _) → ret X

BoolEqError₁ : Cmd (EQ' bool)
BoolEqError₁ = error

BoolEqError₂ : Cmd (EQ' bool)
BoolEqError₂ =
  ret (
    (bool , λ b₁ → error) ,
    λ lock → Eq.cong (bool ,_) (trivially-eq (conn/dyn {t = bool ⇀ bool ⇀ bool}) lock)
  )

_<*>_ : Cmd ⟨| t₁ ⇀ t₂ |⟩ → Cmd ⟨| t₁ |⟩ → Cmd ⟨| t₂ |⟩
f' <*> x' =
  bind f' λ f →
    bind x' λ x →
      f x

private
  ex : Cmd ⟨| bool |⟩
  ex =
    bind BoolEq λ ((t , eq) , h) →
      let
        where-clause : ◯ (bool ≡ t)
        where-clause u = Eq.sym (Eq.cong proj₁ (h u))
      in
      eq (tt via where-clause) <*> ret (ff via where-clause)

  _ : ex ≡ ret ff
  _ = refl
