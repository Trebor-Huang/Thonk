module Tests where

open import thonk

2+3 : ε ⊢ is ○ ⁺
2+3 = n! add \
    { 𝕫 -> cons⁺ (nat 2) \()
    ; (𝕤 𝕫) -> cons⁺ (nat 3) \()
    }

print-2+3 : ε ⊢ #
print-2+3 = b# print \
    { 𝕫 -> 2+3
    ; (𝕤 𝕫) -> ¬⁻ b# ℧ \ () }

main : _
main = interpret print-2+3
