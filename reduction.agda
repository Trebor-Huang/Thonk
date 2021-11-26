open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary using (Decidable)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
open import Constructor
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
import Pattern
import Syntax

module Reduction (C⁺ C⁻ : Set) (cs : Constructors C⁺ C⁻)
    (_≟⁺_ : Decidable {A = C⁺} _≡_) (_≟⁻_ : Decidable {A = C⁻} _≡_)
    (B : Set) (builtin : B -> Pattern.Context C⁺ C⁻ cs _≟⁺_ _≟⁻_)
    (N : Set) (native : N -> Pattern.Context C⁺ C⁻ cs _≟⁺_ _≟⁻_)where

private
    first-just : ∀ {ℓ} {A : Set ℓ} -> List (Maybe A) -> Maybe A
    first-just [] = nothing
    first-just (just a ∷ as) = just a
    first-just (nothing ∷ as) = first-just as

open Pattern C⁺ C⁻ cs _≟⁺_ _≟⁻_
open import Syntax C⁺ C⁻ cs _≟⁺_ _≟⁻_ B builtin N native
open Constructors

-- Small step semantics.
{-
infix 6 _↘_ _~>₁_ _~>_

_c⟦_⟧ : ∀ {Γ Γ' h j} -> Γ ⊢̂ h ʻ j -> Γ' ⊢̅ Γ -> Γ' ⊢̂ h ʻ j
[] c⟦ σ ⟧ = []
((pat , body) ∷ clause) c⟦ σ ⟧ = (pat , body ⟦ extend-σₚ σ ⟧) ∷ (clause c⟦ σ ⟧)

data _↘_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- a single reduction
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
        -> (¬⁺ c) ⟦ σ ⟧ ↘ ¬⁺ (c ⟦ extend-σ σ ⟧)
    σ-¬⁻ : ∀ {Γ Γ' c} {σ : Γ' ⊢̅ Γ}
        -> (¬⁻ c) ⟦ σ ⟧ ↘ ¬⁻ (c ⟦ extend-σ σ ⟧)
    σ-case : ∀ {Γ Γ' h j} {term : Γ ⊢ is h} {clauses : Γ ⊢̂ h ʻ j} {σ : Γ' ⊢̅ Γ}
        -> (case term of clauses) ⟦ σ ⟧ ↘ case (term ⟦ σ ⟧) of (clauses c⟦ σ ⟧)
    -- TODO congruence for builtins
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
    -- TODO reduction for builtins

data _~>₁_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- the congruent closure
data _~>_ : ∀ {Γ j} -> Γ ⊢ j -> Γ ⊢ j -> Set where  -- the transitive closure
    ~>₀ : ∀ {Γ j} -> (t : Γ ⊢ j) -> t ~> t
    ~>₊ : ∀ {Γ j} -> (t s r : Γ ⊢ j) -> t ~> s -> s ~>₁ r -> t ~> r

-- Defines normal forms.
-}

-- Defines a non-terminating function that executes a program.

{-# NON_TERMINATING #-}
normalize : ∀ {Γ j}
    -> (implement-native : ∀ {Γ} (n : N) -> Γ ⊢̅ native n -> Γ ⊢ is ○ ⁺)
    -> Γ ⊢ j -> Γ ⊢ j
normalize implement-native (var x) = var x
normalize implement-native (cons⁺ c args) = cons⁺ c \ i -> normalize implement-native (args i)
normalize implement-native (cons⁻ c args) = cons⁻ c \ i -> normalize implement-native (args i)
normalize implement-native ⟨ c ∥⁺ t ⟩ with normalize implement-native t | normalize implement-native c
... | nft | ¬⁺ hole = hole ⟦ push-σ nft ⟧
... | nft | nfc = ⟨ nfc ∥⁺ nft ⟩
normalize implement-native ⟨ c ⁻∥ t ⟩ with normalize implement-native c | normalize implement-native t
... | nfc | ¬⁻ hole = hole ⟦ push-σ nfc ⟧
... | nfc | nft = ⟨ nfc ⁻∥ nft ⟩
normalize implement-native (¬⁺ t) = ¬⁺ t  -- Holes are lazy.
normalize implement-native (¬⁻ t) = ¬⁻ t
normalize implement-native (t ⟦ σ ⟧) = substitute σ t
normalize implement-native (case t of clauses) with normalize implement-native t
... | nf with first-match clauses nf
... | just (p , (bindings , body)) = body ⟦ push-σₚ bindings ⟧
... | nothing = case t of clauses  -- Stuck
normalize implement-native (b# b args) = b# b \ i -> normalize implement-native (args i)
normalize implement-native (n! n args) = implement-native n \ i -> normalize implement-native (args i)

-- Proves some properties about strong bisimulation
