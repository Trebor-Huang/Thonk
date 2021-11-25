open import Constructor
open import Data.Fin.Base as Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary using (Decidable)

module Pattern (C⁺ C⁻ : Set) (cs : Constructors C⁺ C⁻)
    (_≟⁺_ : Decidable {A = C⁺} _≡_) (_≟⁻_ : Decidable {A = C⁻} _≡_) where
open Constructors

data Pattern : Hypothesis -> Set where
    $ : ∀ h -> Pattern h
    _⁺⦅_⦆ : (c⁺ : C⁺)
        -> (let record { args = args } = ℂ⁺ cs c⁺ in
            ∀ i -> Pattern (args i))
        -> Pattern (○ ⁺)
    _⁻⦅_⦆ : (c⁻ : C⁻)
        -> (let record { args = args } = ℂ⁻ cs c⁻ in
            ∀ i -> Pattern (args i))
        -> Pattern (● ⁻)

data _∋ₚ_ : ∀ {h} -> Pattern h -> Hypothesis -> Set where
    ∂ : ∀ h -> ($ h) ∋ₚ h
    _≪⁺_ : ∀ {c f h} i -> (f i) ∋ₚ h -> (c ⁺⦅ f ⦆) ∋ₚ h
    _≪⁻_ : ∀ {c f h} i -> (f i) ∋ₚ h -> (c ⁻⦅ f ⦆) ∋ₚ h

infixr 10 _≪⁺_ _≪⁻_

data Context : Set where
    ε : Context
    _ʻₚ_ : ∀ {h} -> Context -> Pattern h -> Context
    _ʻ_ : Context -> Hypothesis -> Context

infixl 9 _ʻₚ_ _ʻ_
infix 8 _∋_

data _∋_ : Context -> Hypothesis -> Set where
    𝕫ₚ : ∀ {Γ h h'} {p : Pattern h'} -> p ∋ₚ h -> Γ ʻₚ p ∋ h
    𝕫 : ∀ {Γ h} -> Γ ʻ h ∋ h
    𝕤ₚ : ∀ {Γ h h'} {p : Pattern h'} -> Γ ∋ h -> Γ ʻₚ p ∋ h
    𝕤 : ∀ {Γ h h'} -> Γ ∋ h -> Γ ʻ h' ∋ h
