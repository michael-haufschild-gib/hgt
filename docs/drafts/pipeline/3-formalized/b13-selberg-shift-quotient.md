# A nonnegative Euler logarithm with nonreal exceptional zeros

- **Stage:** 3-formalized
- **Result:** A meromorphic function with a nonnegative Euler logarithm and an exact Selberg reflection formula has a finite nonempty set of off-line zeros in the strip, all nonreal.

Take the Selberg zeta function Z of a compact surface whose exceptional real zeros form a finite nonempty set A. For h > 0 take F(s) = Z(s+ih)Z(s−ih)/Z(s)². At primitive length ℓ, the nth local logarithmic coefficient is 2(1−cos(nhℓ))/n for n ≥ 1. The convergent Euler product follows by dividing the three Selberg products on Re s > 1. The reflection multiplier is the same quotient of the three Selberg multipliers.

The off-line zeros in the open strip are exactly (A + ih) ∪ (A − ih). The off-line poles are exactly A. At each x ∈ A both shifted factors are nonzero, so the denominator gives a genuine pole. The model answers the meromorphic version of B13-T8. The version requiring holomorphy throughout the open strip remains open.

**Lean.** [TheSymmetricShiftOfTheSelbergEulerProduct.lean](../../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/TheSymmetricShiftOfTheSelbergEulerProduct.lean) proves `shiftLogCoeff_nonneg` and `exists_shifted_selberg_positive_euler_model`. Both axiom audits give `propext`, `Classical.choice`, `Quot.sound`.
