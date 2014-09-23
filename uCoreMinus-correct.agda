import Data.BitVector as BV
open BV using (BitVector)
import Data.Nat as Nat
open Nat using (ℕ)
module uCoreMinus-correct (width : ℕ)
                          (top : BitVector width)
                          (bottom : BitVector width) where

Word = BitVector width

mutual
  data Cxt : Set where
    [] : Cxt
    _<:_ : (Γ : Cxt) → Ty Γ → Cxt

  data Ty : Cxt →  Set where
    weaken : ∀ {Γ τ} → Ty Γ → Ty (Γ <: τ)
    unit word ptr : ∀ {Γ} → Ty Γ
    _=>_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
    _+T_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
    _*T_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
    [|_≠0|] : ∀ {Γ} → Term Γ word → Ty Γ
    [|_=0|] : ∀ {Γ} → Term Γ word → Ty Γ
    [|_<_|] : ∀ {Γ} → Term Γ word → Term Γ word → Ty Γ
    [|_≤_|] : ∀ {Γ} → Term Γ word → Term Γ word → Ty Γ

  infixl 1 [|_<_|] [|_≤_|] [|_=0|] [|_≠0|]

  infix 1 _∈_
  data _∈_ {Γ′ : Cxt}(τ : Ty Γ′) : Cxt → Set where
    here : τ ∈ Γ′ <: τ
    there : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ <: σ

  data Term (Γ : Cxt) : Ty Γ → Set where
    ∅ : Term Γ unit
    lit : Word → Term Γ word
    var : ∀ {τ} → τ ∈ Γ → Term Γ τ
    _∙_ : ∀ {σ} {τ : Ty Γ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
    lam : ∀ σ {τ} → Term (Γ <: σ) (weaken τ) → Term Γ (σ => τ)
    inl : ∀ {σ} τ → Term Γ σ → Term Γ (σ +T τ)
    inr : ∀ σ {τ} → Term Γ τ → Term Γ (σ +T τ)
    case : ∀ {σ τ ρ} → Term Γ (σ +T τ) → Term (Γ <: σ) (weaken ρ) → Term (Γ <: τ) (weaken ρ) → Term Γ ρ
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

