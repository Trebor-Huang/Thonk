open import Agda.Builtin.Nat
open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.List using (List; []; _∷_)
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

infix 8 _⊢_ _⊢ₚ_ _⊢̅_ _⊢̂_ʻ_

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
    ⟨_⁻∥_⟩ : ∀ {Γ} -> Γ ⊢ is ● ⁻ -> Γ ⊢ is ○ ⁻ -> Γ ⊢ #
    ¬⁺_ : ∀ {Γ} -> Γ ʻ ○ ⁺ ⊢ # -> Γ ⊢ is ● ⁺
    ¬⁻_ : ∀ {Γ} -> Γ ʻ ● ⁻ ⊢ # -> Γ ⊢ is ○ ⁻
    _⟦_⟧ : ∀ {Γ Γ' h} -> Γ' ⊢ h -> (∀ {h'} -> Γ' ∋ h' -> Γ ⊢ is h') -> Γ ⊢ h
    case_of_ : ∀ {Γ h h'} -> Γ ⊢ is h'
        -> List (Σ[ pat ∈ Pattern h' ] (Γ ʻₚ pat ⊢ h)) -> Γ ⊢ h
    ℧ : ∀ {Γ} -> Γ ⊢ #
    print : ∀ {Γ} -> Γ ⊢ is ○ ⁺ -> Γ ⊢ # -> Γ ⊢ #

infix 9 ¬⁺_ ¬⁻_
infixl 9 _⟦_⟧
infix 9 case_of_

_⊢ₚ_ : ∀ {h} -> Context -> Pattern h -> Set
Γ ⊢ₚ p = ∀ {h'} -> p ∋ₚ h' -> Γ ⊢ is h'

_⊢̅_ : Context -> Context -> Set
Γ ⊢̅ Γ' = ∀ {h'} -> Γ' ∋ h' -> Γ ⊢ is h'

_⊢̂_ʻ_ : ∀ Γ h' j -> Set
Γ ⊢̂ h' ʻ j = List (Σ[ pat ∈ Pattern h' ] (Γ ʻₚ pat ⊢ j))

-- Some convenient ways to create substitutions.
-- This follows the pattern; we write the boilerplate to avoid too much higher order fidgeting.
extend-ρ : ∀ {Γ Γ' h'}
    -> (∀ {h} -> Γ ∋ h -> Γ' ∋ h)
    -> (∀ {h} -> Γ ʻ h' ∋ h -> Γ' ʻ h' ∋ h)
extend-ρ ρ 𝕫 = 𝕫
extend-ρ ρ (𝕤 i) = 𝕤 (ρ i)

extend-ρₚ : ∀ {Γ Γ' h'} {p : Pattern h'}
    -> (∀ {h} -> Γ ∋ h -> Γ' ∋ h)
    -> (∀ {h} -> Γ ʻₚ p ∋ h -> Γ' ʻₚ p ∋ h)
extend-ρₚ ρ (𝕫ₚ x) = 𝕫ₚ x
extend-ρₚ ρ (𝕤ₚ x) = 𝕤ₚ (ρ x)

rename : ∀ {Γ Γ'}
    -> (∀ {h} -> Γ ∋ h -> Γ' ∋ h)
    -> (∀ {j} -> Γ ⊢ j -> Γ' ⊢ j)
rename ρ (var x) = var (ρ x)
rename ρ (cons⁺ c x) = cons⁺ c \ i -> rename ρ (x i)
rename ρ (cons⁻ c x) = cons⁻ c \ i -> rename ρ (x i)
rename ρ (¬⁺ t) = ¬⁺ (rename (extend-ρ ρ) t)
rename ρ (¬⁻ t) = ¬⁻ (rename (extend-ρ ρ) t)
rename ρ (t ⟦ σ ⟧) = t ⟦ (\ i -> rename ρ (σ i)) ⟧
rename ρ (case t of clauses) = case rename ρ t of map-rename-ρ clauses
    where
        map-rename-ρ : _ -> _
        map-rename-ρ [] = []
        map-rename-ρ ((pat , clause) ∷ l) =
            (pat , rename (extend-ρₚ ρ) clause) ∷ map-rename-ρ l
rename ρ ⟨ c ∥⁺ t ⟩ = ⟨ rename ρ c ∥⁺ rename ρ t ⟩
rename ρ ⟨ c ⁻∥ t ⟩ = ⟨ rename ρ c ⁻∥ rename ρ t ⟩
rename ρ ℧ = ℧
rename ρ (print n c) = print (rename ρ n) (rename ρ c)

push-σ : ∀ {Γ h} -> Γ ⊢ is h -> Γ ⊢̅ Γ ʻ h
push-σ term 𝕫 = term
push-σ term (𝕤 i) = var i

push-σₚ : ∀ {Γ h} {p : Pattern h} -> Γ ⊢ₚ p -> Γ ⊢̅ Γ ʻₚ p
push-σₚ terms (𝕫ₚ α) = terms α
push-σₚ terms (𝕤ₚ i) = var i

extend-σ : ∀ {Γ Γ' h} -> Γ ⊢̅ Γ' -> Γ ʻ h ⊢̅ Γ' ʻ h
extend-σ σ 𝕫 = var 𝕫
extend-σ σ (𝕤 p) = rename 𝕤 (σ p)

extend-σₚ : ∀ {Γ Γ' h} {p : Pattern h} -> Γ ⊢̅ Γ' -> Γ ʻₚ p ⊢̅ Γ' ʻₚ p
extend-σₚ σ (𝕫ₚ α) = var (𝕫ₚ α)
extend-σₚ σ (𝕤ₚ i) = rename 𝕤ₚ (σ i)

substitute : ∀ {Γ Γ'} -> Γ ⊢̅ Γ' -> (∀ {j} -> Γ' ⊢ j -> Γ ⊢ j)
substitute σ (var x) = σ x
substitute σ (cons⁺ c x) = cons⁺ c \ i -> substitute σ (x i)
substitute σ (cons⁻ c x) = cons⁻ c \ i -> substitute σ (x i)
substitute σ (¬⁺ t) = ¬⁺ (substitute (extend-σ σ) t)
substitute σ (¬⁻ t) = ¬⁻ (substitute (extend-σ σ) t)
substitute σ (t ⟦ σ' ⟧) = t ⟦ (\ i -> substitute σ (σ' i)) ⟧
substitute σ (case t of clauses) = case substitute σ t of map-substitute-σ clauses
    where
        map-substitute-σ : _ -> _
        map-substitute-σ [] = []
        map-substitute-σ ((pat , clause) ∷ l) =
            (pat , substitute (extend-σₚ σ) clause) ∷ map-substitute-σ l
substitute σ ⟨ c ∥⁺ t ⟩ = ⟨ substitute σ c ∥⁺ substitute σ t ⟩
substitute σ ⟨ c ⁻∥ t ⟩ = ⟨ substitute σ c ⁻∥ substitute σ t ⟩
substitute σ ℧ = ℧
substitute σ (print n c) = print (substitute σ n) (substitute σ c)

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

first-match : ∀ {Γ h' j} -> Γ ⊢̂ h' ʻ j -> Γ ⊢ is h' -> Maybe (Σ[ p ∈ Pattern h' ] Γ ⊢ₚ p × Γ ʻₚ p ⊢ j)
first-match [] term = nothing
first-match ((p , body) ∷ clauses) term with match p term
... | just bindings = just (p , (bindings , body))
... | nothing = nothing

record Match {Γ h' j} (clauses : Γ ⊢̂ h' ʻ j) (term : Γ ⊢ is h')
    (p : Pattern h') (bindings : Γ ⊢ₚ p) (body : Γ ʻₚ p ⊢ j) : Set where
    field
        evidence : first-match clauses term ≡ just (p , (bindings , body))

pattern Match! {e} = record {evidence = e}
