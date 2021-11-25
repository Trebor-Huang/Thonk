open import Data.Vec.Functional using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (yes; no)

module Thonk where
open import Constructor

-- Defines the constructors. 🤔
data Ç⁺ : Set where
    unit : Ç⁺
    pair : Ç⁺
    inl : Ç⁺
    inr : Ç⁺
    flat : Ç⁺
    mu⁺ : Ç⁺  -- TODO functions

_≟⁺_ : Decidable {A = Ç⁺} _≡_
unit ≟⁺ unit = yes refl
pair ≟⁺ pair = yes refl
inl ≟⁺ inl = yes refl
inr ≟⁺ inr = yes refl
flat ≟⁺ flat = yes refl
mu⁺ ≟⁺ mu⁺ = yes refl
unit ≟⁺ pair = no \ ()
unit ≟⁺ inl = no \ ()
unit ≟⁺ inr = no \ ()
unit ≟⁺ flat = no \ ()
unit ≟⁺ mu⁺ = no \ ()
pair ≟⁺ unit = no \ ()
pair ≟⁺ inl = no \ ()
pair ≟⁺ inr = no \ ()
pair ≟⁺ flat = no \ ()
pair ≟⁺ mu⁺ = no \ ()
inl ≟⁺ unit = no \ ()
inl ≟⁺ pair = no \ ()
inl ≟⁺ inr = no \ ()
inl ≟⁺ flat = no \ ()
inl ≟⁺ mu⁺ = no \ ()
inr ≟⁺ unit = no \ ()
inr ≟⁺ pair = no \ ()
inr ≟⁺ inl = no \ ()
inr ≟⁺ flat = no \ ()
inr ≟⁺ mu⁺ = no \ ()
flat ≟⁺ unit = no \ ()
flat ≟⁺ pair = no \ ()
flat ≟⁺ inl = no \ ()
flat ≟⁺ inr = no \ ()
flat ≟⁺ mu⁺ = no \ ()
mu⁺ ≟⁺ unit = no \ ()
mu⁺ ≟⁺ pair = no \ ()
mu⁺ ≟⁺ inl = no \ ()
mu⁺ ≟⁺ inr = no \ ()
mu⁺ ≟⁺ flat = no \ ()

data Ç⁻ : Set where
    counit : Ç⁻
    copair : Ç⁻
    projl : Ç⁻
    projr : Ç⁻
    sharp : Ç⁻
    mu⁻ : Ç⁻

_≟⁻_ : Decidable {A = Ç⁻} _≡_
counit ≟⁻ counit = yes refl
copair ≟⁻ copair = yes refl
projl ≟⁻ projl = yes refl
projr ≟⁻ projr = yes refl
sharp ≟⁻ sharp = yes refl
mu⁻ ≟⁻ mu⁻ = yes refl
counit ≟⁻ copair = no \ ()
counit ≟⁻ projl = no \ ()
counit ≟⁻ projr = no \ ()
counit ≟⁻ sharp = no \ ()
counit ≟⁻ mu⁻ = no \ ()
copair ≟⁻ counit = no \ ()
copair ≟⁻ projl = no \ ()
copair ≟⁻ projr = no \ ()
copair ≟⁻ sharp = no \ ()
copair ≟⁻ mu⁻ = no \ ()
projl ≟⁻ counit = no \ ()
projl ≟⁻ copair = no \ ()
projl ≟⁻ projr = no \ ()
projl ≟⁻ sharp = no \ ()
projl ≟⁻ mu⁻ = no \ ()
projr ≟⁻ counit = no \ ()
projr ≟⁻ copair = no \ ()
projr ≟⁻ projl = no \ ()
projr ≟⁻ sharp = no \ ()
projr ≟⁻ mu⁻ = no \ ()
sharp ≟⁻ counit = no \ ()
sharp ≟⁻ copair = no \ ()
sharp ≟⁻ projl = no \ ()
sharp ≟⁻ projr = no \ ()
sharp ≟⁻ mu⁻ = no \ ()
mu⁻ ≟⁻ counit = no \ ()
mu⁻ ≟⁻ copair = no \ ()
mu⁻ ≟⁻ projl = no \ ()
mu⁻ ≟⁻ projr = no \ ()
mu⁻ ≟⁻ sharp = no \ ()

open Constructors

ç : Constructors Ç⁺ Ç⁻
ℂ⁺ ç unit = 𝕔 0 []
ℂ⁺ ç pair = 𝕔 2 (○ ⁺ ∷ ○ ⁺ ∷ [])
ℂ⁺ ç inl = 𝕔 1 (○ ⁺ ∷ [])
ℂ⁺ ç inr = 𝕔 1 (○ ⁺ ∷ [])
ℂ⁺ ç flat = 𝕔 1 (○ ⁻ ∷ [])
ℂ⁺ ç mu⁺ = 𝕔 1 (● ⁺ ∷ [])
ℂ⁻ ç counit = 𝕔 0 []
ℂ⁻ ç copair = 𝕔 2 (● ⁻ ∷ ● ⁻ ∷ [])
ℂ⁻ ç projl = 𝕔 1 (● ⁻ ∷ [])
ℂ⁻ ç projr = 𝕔 1 (● ⁻ ∷ [])
ℂ⁻ ç sharp = 𝕔 1 (● ⁺ ∷ [])
ℂ⁻ ç mu⁻ = 𝕔 1 (○ ⁻ ∷ [])

import Pattern
import Syntax
open Pattern Ç⁺ Ç⁻ ç _≟⁺_ _≟⁻_ public
open Syntax Ç⁺ Ç⁻ ç _≟⁺_ _≟⁻_ public


