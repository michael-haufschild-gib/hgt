# The reciprocal logarithmic factor has its positive measure

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `s>0`, the actual Poisson factor satisfies `κ(s)⁻¹=R/(s+b)+∫₁∞ρ(t)/(s+t)dt`, and the integral is finite. Here `b=√(1-exp(-2))`, `R=κ(b)(1-b²)/b>0`, and `ρ(t)=2κ(t)/((2+log(t²-1))²+π²)>0`.

## Proof

Let `H(z)=1/κ(z)-R/(z+b)`, with its analytic value at the removed pole,
and `G(z)=(H(z)-H(-i))/(z+i)`, with its analytic value at `-i`.
Boundedness of `H` gives `G(z)=O(1/|z|)` on both nonreal half-planes.
Apply the upper Cauchy formula to `G(z+iε)` and the lower vanishing formula
to the reflected quotient `G(-z-iε)/(-z-w)`.

For `0<ε<1/2`, a common `C_w/(1+x²)` majorant controls both boundary
integrands. Their limits are the upper cut representative and its conjugate.
Subtracting the two integrals and inserting the exact jump `-2πiρ(t)` gives

`H(w)-H(-i)=∫₁∞ρ(t)(1/(t+w)-1/(t-i))dt`, `Im w>0`.

The bounded density gives an integrable majorant as `w` approaches a positive
real number. Subtract the resulting identities at `s` and `S>s`:

`H(s)-H(S)=∫₁∞ρ(t)(1/(t+s)-1/(t+S))dt`.

As `S→∞`, the nonnegative integrands increase to `ρ(t)/(t+s)` and
`H(S)→0`. Fatou's lemma proves integrability from the finite limiting
integrals. Bochner monotone convergence identifies their limit with `H(s)`.
Adding the pole term proves the exact formula.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheReciprocalLogarithmicFactorHasItsPositiveMeasure.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `regularLogReferenceReciprocal_subtracted_cauchy`
- `regularLogReferenceReciprocal_subtracted_stieltjes_ofReal`
- `logarithmic_stieltjes_difference`
- `logarithmic_stieltjes_integral`
- `logReferenceFactor_reciprocal_stieltjes`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
The causal inverse and Green identity remain on the
[half-line kernel card](the-half-line-logarithmic-green-kernel.md).
