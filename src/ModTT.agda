{-# OPTIONS --rewriting #-}

module ModTT where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Data.Product as Product using (_,_; proj₁; proj₂) public

Jdg = Set

postulate
  φ-static : Jdg
  φ-static/uni : {lock₁ lock₂ : φ-static} → lock₁ ≡ lock₂

◯_ : Jdg → Jdg
◯_ A = (lock : φ-static) → A

postulate
  Sig : Jdg
  Val : Sig → Jdg

variable
  σ σ₁ σ₂ σ₃ : Sig
  τ : Val σ → Sig

postulate
  law/static-typechecking : ◯ (σ₁ ≡ σ₂) → Val σ₁ → Val σ₂
  law/static-typechecking/refl : (h : ◯ (σ ≡ σ)) (M : Val σ) → law/static-typechecking h M ≡ M
  {-# REWRITE law/static-typechecking/refl #-}

postulate
  type : Sig
  ⟨|_|⟩ : Val type → Sig
  Π Σ : (σ : Sig) → (Val σ → Sig) → Sig
  Ext : (σ : Sig) → ◯ Val σ → Sig
  ◇ : Sig → Sig

Cmd : Sig → Jdg
Cmd σ = Val (◇ σ)

variable
  t t₁ t₂ : Val type

_via_ : Val ⟨| t₂ |⟩ → ◯ (t₁ ≡ t₂) → Val ⟨| t₁ |⟩
_via_ M h = law/static-typechecking (λ u → Eq.sym (Eq.cong ⟨|_|⟩ (h u))) M

postulate
  Π/val : Val (Π σ τ) ≡ ((x : Val σ) → Val (τ x))
  Σ/val : Val (Σ σ τ) ≡ Product.Σ (Val σ) λ x → Val (τ x)
  Ext/val : {V : ◯ Val σ} → Val (Ext σ V) ≡ Product.Σ (Val σ) λ U → (lock : φ-static) → U ≡ V lock
  {-# REWRITE Π/val Σ/val Ext/val #-}

  Trivial : Sig → Jdg
  trivially : Trivial σ → ◯ Val σ
  trivially-eq : Trivial σ → {M₁ M₂ : Val σ} → ◯ (M₁ ≡ M₂)
  conn/dyn : Trivial ⟨| t |⟩
  conn/cmp : Trivial (◇ σ)

  ret : Val σ → Cmd σ
  bind : Cmd σ₁ → (Val σ₁ → Cmd σ₂) → Cmd σ₂
  bind/ret : {V : Val σ₁} {F : Val σ₁ → Cmd σ₂} →
    bind {σ₁} (ret V) F ≡ F V
  bind/assoc : {M : Cmd σ₁} {F : Val σ₁ → Cmd σ₂} {G : Val σ₂ → Cmd σ₃} →
    bind (bind M F) G ≡ bind M λ x → bind (F x) G
  {-# REWRITE bind/ret bind/assoc #-}

infixr 1 _⇀_
postulate
  _⇀_ : Val type → Val type → Val type
  ⇀/val : Val ⟨| t₁ ⇀ t₂ |⟩ ≡ (Val ⟨| t₁ |⟩ → Cmd ⟨| t₂ |⟩)
  {-# REWRITE ⇀/val #-}

  bool : Val type
  tt ff : Val ⟨| bool |⟩
  if : Val ⟨| bool |⟩ → Val σ → Val σ → Val σ
  if/tt : {M₁ M₀ : Val σ} → if {σ} tt M₁ M₀ ≡ M₁
  if/ff : {M₁ M₀ : Val σ} → if {σ} ff M₁ M₀ ≡ M₀
  {-# REWRITE if/tt if/ff #-}

  error : Val (◇ σ)
  bind/error : {F : Val σ₁ → Cmd σ₂} → bind {σ₁} error F ≡ error
  {-# REWRITE bind/error #-}
