open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary using (Decidable)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
open import Constructor

module Reduction (C⁺ C⁻ : Set) (cs : Constructors C⁺ C⁻)
    (_≟⁺_ : Decidable {A = C⁺} _≡_) (_≟⁻_ : Decidable {A = C⁻} _≡_) where

private
    first-just : ∀ {ℓ} {A : Set ℓ} -> List (Maybe A) -> Maybe A
    first-just [] = nothing
    first-just (just a ∷ as) = just a
    first-just (nothing ∷ as) = first-just as

open import Pattern C⁺ C⁻ cs _≟⁺_ _≟⁻_
open import Syntax C⁺ C⁻ cs _≟⁺_ _≟⁻_
open Constructors

-- Small step semantics.
infix 6 _↘_ _~>₁_ _~>_

-- First some convenient ways to create substitutions.
push-σ : ∀ {Γ h} -> Γ ⊢ is h -> Γ ⊢̅ Γ ʻ h
push-σ term 𝕫 = term
push-σ term (𝕤 i) = var i

push-σₚ : ∀ {Γ h} {p : Pattern h} -> Γ ⊢ₚ p -> Γ ⊢̅ Γ ʻₚ p
push-σₚ terms (𝕫ₚ α) = terms α
push-σₚ terms (𝕤ₚ i) = var i

weaken-σ : ∀ {Γ Γ' h} -> Γ ⊢̅ Γ' -> Γ ʻ h ⊢̅ Γ'
weaken-σ σ p = {!   !}

_c⟦_⟧ : ∀ {Γ Γ' h j} -> Γ ⊢̂ h ʻ j -> Γ' ⊢̅ Γ -> Γ' ⊢̂ h ʻ j
[] c⟦ σ ⟧ = []
((pat , body) ∷ clause) c⟦ σ ⟧ = (pat , {!   !}) ∷ (clause c⟦ σ ⟧)

data _↘_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- a single reduction
    loop : ∀ {Γ} -> Ω ↘ Ω {Γ = Γ}
    -- no rule for abort (℧)
    σ-var : ∀ {Γ Γ' h} {v : Γ ∋ h} {σ : Γ' ⊢̅ Γ}
        -> var v ⟦ σ ⟧ ↘ σ v
    -- Congruence rules for substitution
    σ-cons⁺ : ∀ {Γ Γ' c args} {σ : Γ' ⊢̅ Γ}
        -> (cons⁺ c args) ⟦ σ ⟧ ↘ cons⁺ c \ i -> (args i) ⟦ σ ⟧
    σ-cons⁻ : ∀ {Γ Γ' c args} {σ : Γ' ⊢̅ Γ}
        -> (cons⁻ c args) ⟦ σ ⟧ ↘ cons⁻ c \ i -> (args i) ⟦ σ ⟧
    σ-cmd⁺ : ∀ {Γ Γ' c t} {σ : Γ' ⊢̅ Γ}
        -> ⟨ c ∥⁺ t ⟩ ⟦ σ ⟧ ↘ ⟨ c ⟦ σ ⟧ ∥⁺ t ⟦ σ ⟧ ⟩
    σ-cmd⁻ : ∀ {Γ Γ' c t} {σ : Γ' ⊢̅ Γ}
        -> ⟨ c ⁻∥ t ⟩ ⟦ σ ⟧ ↘ ⟨ c ⟦ σ ⟧ ⁻∥ t ⟦ σ ⟧ ⟩
    σ-¬⁺ : ∀ {Γ Γ' c} {σ : Γ' ⊢̅ Γ}
        -> (¬⁺ c) ⟦ σ ⟧ ↘ ¬⁺ (c ⟦ {!   !} ⟧)
    σ-¬⁻ : ∀ {Γ Γ' c} {σ : Γ' ⊢̅ Γ}
        -> (¬⁻ c) ⟦ σ ⟧ ↘ ¬⁻ (c ⟦ {!   !} ⟧)
    σ-case : ∀ {Γ Γ' h j} {term : Γ ⊢ is h} {clauses : Γ ⊢̂ h ʻ j} {σ : Γ' ⊢̅ Γ}
        -> (case term of clauses) ⟦ σ ⟧ ↘ case (term ⟦ σ ⟧) of (clauses c⟦ σ ⟧)
    -- Casejumps
    casejump : ∀ {Γ h' j} {clauses : Γ ⊢̂ h' ʻ j} {term : Γ ⊢ is h'}
        {p : Pattern h'} {bindings : Γ ⊢ₚ p} {body : Γ ʻₚ p ⊢ j}
        -> Match clauses term p bindings body
        -> case term of clauses ↘ body ⟦ push-σₚ bindings ⟧
    -- Command reduction
    E⁺ : ∀ {Γ cont} {term : Γ ⊢ is ○ ⁺}
        -> ⟨ ¬⁺ cont ∥⁺ term ⟩ ↘ cont ⟦ push-σ term ⟧
    E⁻ : ∀ {Γ term} {cont : Γ ⊢ is ● ⁻}
        -> ⟨ cont ⁻∥ ¬⁻ term ⟩ ↘ term ⟦ push-σ cont ⟧

data _~>₁_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- the congruent closure
data _~>_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- the transitive closure
    ~>₀ : ∀ {Γ j} -> (t : Γ ⊢ j) -> t ~> t
    ~>₊ : ∀ {Γ j} -> (t s r : Γ ⊢ j) -> t ~> s -> s ~>₁ r -> t ~> r

-- Defines normal forms.

-- Defines a non-terminating function that executes a program.
