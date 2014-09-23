open import Data.Nat using (ℕ)
module uCoreMinus.Unsafe (width : ℕ) where

import Data.BitVector as BV
open BV using (BitVector)

Word = BitVector width

open import Data.List
open import Data.List.Any public using (module Membership-≡; here; there)
open Membership-≡ public using (_∈_)

data Ty : Set where
  unit word ptr : Ty
  _=>_ : Ty → Ty → Ty
  _+T_ : Ty → Ty → Ty
  _*T_ : Ty → Ty → Ty

Cxt : Set
Cxt = List Ty

bool = unit +T unit

data Term (Γ : Cxt) : Ty → Set where
  -- unit
  ∅ : Term Γ unit
  -- Word literals
  lit : Word → Term Γ word
  -- STLC
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _∙_ : ∀ {σ τ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ => τ)
  -- sums
  inl : ∀ {σ} τ → Term Γ σ → Term Γ (σ +T τ)
  inr : ∀ σ {τ} → Term Γ τ → Term Γ (σ +T τ)
  case : ∀ {σ τ ρ} → Term Γ (σ +T τ) → Term (σ ∷ Γ) ρ → Term (τ ∷ Γ) ρ → Term Γ ρ
  -- products
  _,_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ *T τ)
  fst : ∀ {σ τ} → Term Γ (σ *T τ) → Term Γ σ
  snd : ∀ {σ τ} → Term Γ (σ *T τ) → Term Γ τ
  -- Word arithmetics
  _+_ : Term Γ word → Term Γ word → Term Γ word
  _-_ : Term Γ word → Term Γ word → Term Γ word
  _*_ : Term Γ word → Term Γ word → Term Γ word
  _/_ : Term Γ word → (d : Term Γ word) → Term Γ word -- unsafe!!
  -- bitwise Word operations
  _b&_ : Term Γ word → Term Γ word → Term Γ word
  _b|_ : Term Γ word → Term Γ word → Term Γ word
  _b^_ : Term Γ word → Term Γ word → Term Γ word
  b~_ : Term Γ word → Term Γ word
  -- test operations
  _≟0 : (t : Term Γ word) → Term Γ bool
  _<?_ : (s t : Term Γ word) → Term Γ bool
  -- pointers
  peek : Term Γ ptr → Term Γ word
  pcast : (t : Term Γ word) → Term Γ ptr -- unsafe!!
