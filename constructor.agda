open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Vec.Functional

module Constructor where

data Polarity : Set where
    ⁻ : Polarity
    ⁺ : Polarity

data Hypothesis : Set where
    ○_ : Polarity -> Hypothesis
    ●_ : Polarity -> Hypothesis

infixr 20 ○_ ●_

data Judgement : Set where
    is_ : Hypothesis -> Judgement
    # : Judgement

infixr 19 is_

record ConstructorSort : Set where
    constructor 𝕔
    field
        arity : ℕ
        args : Vector Hypothesis arity

open ConstructorSort

record Constructors (C⁺ C⁻ : Set) : Set where
    field
        ℂ⁺ : C⁺ -> ConstructorSort
        ℂ⁻ : C⁻ -> ConstructorSort


