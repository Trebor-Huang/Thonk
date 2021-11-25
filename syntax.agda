open import Agda.Builtin.Nat
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe
open import Data.Product
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (yes; no)

open import Constructor

module Syntax (C⁺ C⁻ : Set) (cs : Constructors C⁺ C⁻)
    (_≟⁺_ : Decidable {A = C⁺} _≡_) (_≟⁻_ : Decidable {A = C⁻} _≡_) where

private
    join-Fin : ∀ {n} {A : Fin n -> Set}
        -> ((i : Fin n) -> Maybe (A i))
        -> Maybe ((i : Fin n) -> A i)
    join-Fin {zero} f = just \ ()
    join-Fin {suc n} f with f fzero
    ... | nothing = nothing
    ... | just f0 with join-Fin (\i -> f (fsuc i))
    ... | just fs = just
        \{ fzero -> f0 ;
        (fsuc i) -> fs i }
    ... | nothing = nothing

open import Pattern C⁺ C⁻ cs _≟⁺_ _≟⁻_
open Constructors

infix 8  _⊢_ _⊢ₚ_ _⊢̅_

data _⊢_ : Context -> Judgement -> Set where
    var : ∀ {Γ h} -> Γ ∋ h -> Γ ⊢ is h
    cons⁺ : ∀ {Γ} (c : C⁺)
        -> (let record { args = args }
                    = ℂ⁺ cs c in
            ∀ i -> Γ ⊢ is (args i))
        -> Γ ⊢ is ○ ⁺
    cons⁻ : ∀ {Γ} (c : C⁻)
        -> (let record { args = args }
                    = ℂ⁻ cs c in
            ∀ i -> Γ ⊢ is (args i))
        -> Γ ⊢ is ● ⁻
    ⟨_∥⁺_⟩ : ∀ {Γ} -> Γ ⊢ is ● ⁺ -> Γ ⊢ is ○ ⁺ -> Γ ⊢ #
    ⟨_⁻∥_⟩ : ∀ {Γ} -> Γ ⊢ is ○ ⁻ -> Γ ⊢ is ● ⁻ -> Γ ⊢ #
    ¬⁺_ : ∀ {Γ} -> Γ ʻ ○ ⁺ ⊢ # -> Γ ⊢ is ● ⁺
    ¬⁻_ : ∀ {Γ} -> Γ ʻ ● ⁻ ⊢ # -> Γ ⊢ is ○ ⁻
    _⟦_⟧ : ∀ {Γ Γ' h} -> Γ' ⊢ h -> (∀ {h'} -> Γ' ∋ h' -> Γ ⊢ is h') -> Γ ⊢ h
    case_of_ : ∀ {Γ h h'} -> Γ ⊢ is h'
        -> List (Σ[ pat ∈ Pattern h' ] (Γ ʻₚ pat ⊢ h)) -> Γ ⊢ h
    ℧ : ∀ {Γ} -> Γ ⊢ #
    Ω : ∀ {Γ} -> Γ ⊢ #

infix 9 ¬⁺_ ¬⁻_
infixl 9 _⟦_⟧
infix 9 case_of_

_⊢ₚ_ : ∀ {h} -> Context -> Pattern h -> Set
Γ ⊢ₚ p = ∀ {h'} -> p ∋ₚ h' -> Γ ⊢ is h'

_⊢̅_ : Context -> Context -> Set
Γ ⊢̅ Γ' = ∀ {h'} -> Γ' ∋ h' -> Γ ⊢ is h'

match : ∀ {Γ h} -> (p : Pattern h) -> Γ ⊢ is h -> Maybe (Γ ⊢ₚ p)
match ($ _) t = just \ { (∂ _) -> t }
match {Γ} (c ⁺⦅ args ⦆) (cons⁺ c' args') with c ≟⁺ c'
... | yes c≡c' = submatch
    where
        match-argument : ∀ i -> Maybe (Γ ⊢ₚ args i)
        match-argument i rewrite c≡c' = match (args i) (args' i)

        submatch : Maybe (Γ ⊢ₚ c ⁺⦅ args ⦆)
        submatch with join-Fin match-argument
        ... | nothing = nothing
        ... | just m = just \ { (i ≪⁺ α) -> m i α }
... | no _ = nothing
match {Γ} (c ⁻⦅ args ⦆) (cons⁻ c' args') with c ≟⁻ c'
... | yes c≡c' = submatch
    where
        match-argument : ∀ i -> Maybe (Γ ⊢ₚ args i)
        match-argument i rewrite c≡c' = match (args i) (args' i)

        submatch : Maybe (∀ {h'} -> (c ⁻⦅ args ⦆) ∋ₚ h' -> (Γ ⊢ is h'))
        submatch with join-Fin match-argument
        ... | nothing = nothing
        ... | just m = just \ { (i ≪⁻ α) -> m i α }
... | no _ = nothing
match _ _ = nothing
