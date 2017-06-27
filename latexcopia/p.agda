module p where

open import Data.Nat

Atom = ℕ

data Λ : Set where
  v    : Atom → Λ 
  _·_  : Λ → Λ → Λ 
  ƛ    : (Atom → Λ) → Λ 
