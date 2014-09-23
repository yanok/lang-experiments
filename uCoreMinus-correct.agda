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

module ProofErasure where
  import uCoreMinus.Unsafe width as U
  open U hiding (Ty; Term; Cxt; _∈_)
  open import Data.List
  open import Data.List.Any
  open import Relation.Binary.PropositionalEquality

  eraseType : ∀ {Γ} → Ty Γ → U.Ty
  eraseType (weaken τ) = eraseType τ
  eraseType unit = unit
  eraseType word = word
  eraseType ptr = ptr
  eraseType (τ => τ₁) = eraseType τ => eraseType τ₁
  eraseType (τ +T τ₁) = eraseType τ +T eraseType τ₁
  eraseType (τ *T τ₁) = eraseType τ *T eraseType τ₁
  eraseType [| x ≠0|] = unit
  eraseType [| x =0|] = unit
  eraseType [| x < x₁ |] = unit
  eraseType [| x ≤ x₁ |] = unit

  eraseCxt : Cxt → U.Cxt
  eraseCxt [] = []
  eraseCxt (Γ <: τ) = eraseType τ ∷ eraseCxt Γ

  convertIdx : ∀ {Γ Γ′}{τ : Ty Γ′} → τ ∈ Γ → eraseType τ U.∈ eraseCxt Γ
  convertIdx here = here refl
  convertIdx (there i) = there (convertIdx i)

  erase : ∀ {Γ τ} → Term Γ τ → U.Term (eraseCxt Γ) (eraseType τ)
  erase ∅ = ∅
  erase (lit x) = lit x
  erase (var x) = var (convertIdx x)
  erase (t ∙ t₁) = erase t ∙ erase t₁
  erase (lam σ t) = lam (eraseType σ) (erase t)
  erase (inl τ t) = inl (eraseType τ) (erase t)
  erase (inr σ t) = inr (eraseType σ) (erase t)
  erase (case t t₁ t₂) = case (erase t) (erase t₁) (erase t₂)
  erase (t , t₁) = erase t , erase t₁
  erase (fst t) = fst (erase t)
  erase (snd t) = snd (erase t)
  erase (t + t₁) = erase t + erase t₁
  erase (t - t₁) = erase t - erase t₁
  erase (t * t₁) = erase t * erase t₁
  erase (t / t₁ < t₂ >) = erase t / erase t₁
  erase (t b& t₁) = erase t b& erase t₁
  erase (t b| t₁) = erase t b| erase t₁
  erase (t b^ t₁) = erase t b^ erase t₁
  erase (b~ t) = b~ erase t
  erase (t ≟0) = erase t ≟0
  erase (t <? t₁) = erase t <? erase t₁
  erase (peek t) = peek (erase t)
  erase (pcast t t₁) = pcast (erase t)
