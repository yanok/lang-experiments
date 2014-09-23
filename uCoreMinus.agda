import Data.BitVector as BV
open BV using (BitVector)
import Data.Nat as Nat
open Nat using (ℕ)
module uCoreMinus (width : ℕ)
                  (top : BitVector width)
                  (bottom : BitVector width) where

Word = BitVector width

open import Data.List
open import Data.List.Any
open Membership-≡

mutual
  data Ty : Set where
    unit word ptr : Ty
    _=>_ : Ty → Ty → Ty
    _+T_ : Ty → Ty → Ty
    _*T_ : Ty → Ty → Ty
    [|_≠0|] : ∀ {Γ} → Term Γ word → Ty
    [|_=0|] : ∀ {Γ} → Term Γ word → Ty
    [|_<_|] : ∀ {Γ} → Term Γ word → Term Γ word → Ty
    [|_≤_|] : ∀ {Γ} → Term Γ word → Term Γ word → Ty

  infixl 1 [|_<_|] [|_≤_|] [|_=0|] [|_≠0|]

  Cxt : Set
  Cxt = List Ty

  data Term (Γ : Cxt) : Ty → Set where
    ∅ : Term Γ unit
    lit : Word → Term Γ word
    var : ∀ {τ} → τ ∈ Γ → Term Γ τ
    _∙_ : ∀ {σ τ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
    lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ => τ)
    inl : ∀ {σ} τ → Term Γ σ → Term Γ (σ +T τ)
    inr : ∀ σ {τ} → Term Γ τ → Term Γ (σ +T τ)
    case : ∀ {σ τ ρ} → Term Γ (σ +T τ) → Term (σ ∷ Γ) ρ → Term (τ ∷ Γ) ρ → Term Γ ρ
    _,_ : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ *T τ)
    fst : ∀ {σ τ} → Term Γ (σ *T τ) → Term Γ σ
    snd : ∀ {σ τ} → Term Γ (σ *T τ) → Term Γ τ
    _+_ : Term Γ word → Term Γ word → Term Γ word
    _-_ : Term Γ word → Term Γ word → Term Γ word
    _*_ : Term Γ word → Term Γ word → Term Γ word
    _/_<_> : Term Γ word → (d : Term Γ word) → Term Γ [| d ≠0|] → Term Γ word -- taking additional proof argument
    _b&_ : Term Γ word → Term Γ word → Term Γ word
    _b|_ : Term Γ word → Term Γ word → Term Γ word
    _b^_ : Term Γ word → Term Γ word → Term Γ word
    b~_ : Term Γ word → Term Γ word
    _≟0 : (t : Term Γ word) → Term Γ ([| t =0|] +T [| t ≠0|])
    _<?_ : (s t : Term Γ word) → Term Γ ([| s < t |] +T [| t ≤ s |])
    peek : Term Γ ptr → Term Γ word
    pcast : (t : Term Γ word) →
            Term Γ ([| lit bottom < t |] *T [| t < lit top |]) → -- proof
            Term Γ ptr

