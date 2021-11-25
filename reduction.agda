open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary using (Decidable)
open import Data.Maybe using (Maybe; just; nothing)
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

data _↘_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- a single reduction
    loop : ∀ {Γ} -> Ω ↘ Ω {Γ = Γ}
    -- no rule for abort (℧)
    σ-var : ∀ {Γ Γ' h} {v : Γ ∋ h} {σ : Γ' ⊢̅ Γ}
        -> var v ⟦ σ ⟧ ↘ σ v
    σ-cons⁺ : ∀ {Γ Γ' c args} {σ : Γ' ⊢̅ Γ}
        -> (cons⁺ c args) ⟦ σ ⟧ ↘ cons⁺ c \ i -> (args i) ⟦ σ ⟧
    σ-cons⁻ : ∀ {Γ Γ' c args} {σ : Γ' ⊢̅ Γ}
        -> (cons⁻ c args) ⟦ σ ⟧ ↘ cons⁻ c \ i -> (args i) ⟦ σ ⟧
    -- Congruence rules for substitution
    -- Casejumps
    -- Command reduction

data _~>₁_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- the congruent closure
data _~>_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- the transitive closure
    ~>₀ : ∀ {Γ j} -> (t : Γ ⊢ j) -> t ~> t
    ~>₊ : ∀ {Γ j} -> (t s r : Γ ⊢ j) -> t ~> s -> s ~>₁ r -> t ~> r

-- Defines normal forms.

-- Defines a non-terminating function that executes a program.
