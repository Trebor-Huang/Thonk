module Tests where

open import thonk

print-1 : ε ⊢ #
print-1 = print (cons⁺ (nat 1) \ ()) ℧

print-1-10 

main : _
main = interpret print-1
