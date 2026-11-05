# Fifth even integrated tail

- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Statement:** The complete matrix
  `T₅(r) = [∫_(s>r) thetaCuspNativeSignedJet (s/2) (2(i+j)) ds]`
  is positive definite for every `r ≥ 0`.

The complete native fifth tail is now positive from `q=πexp(r)≥3`.
`FifthCompleteTail.nativeTailMatrix_posDef` proves the stated theorem.
The aperture transfer and rank-nine parity assembly remain unverified.

Write `E(q)=q^(3/2)exp(−2q)`, `A=M(0,1)>0`, and
`c(q)=3/(32q²)−3/(128q³)`.

The [first-atom tail](../3-formalized/first-atom-fifth-even-tail.md) and
[leading-pair tail](../3-formalized/leading-pair-fifth-even-tail.md) are
positive definite for `q≥3`. The leading tail retains ordered pairs
`(1,1)`, `(1,2)`, `(2,1)` and stays positive definite after subtracting
`E(q)(3/(8q)+c(q))A`. The half-mass model, cubic gamma bound, and literal
reserve identity are formalized in `FifthMixedTailReserve`.

The [pair `(1,3)` payment](../3-formalized/third-pair-fifth-even-tail.md)
is formalized for every `q≥3`:

`R₁₃(q)+E(q)·3/(8q)·A > 0`.

The exact rate-ten gamma enclosure and
`exp(−8q)≤3²⁴/(20⁸q²⁴)` reduce both endpoint matrices to positive
coefficient matrices in `q/3−1`. All 23 required fixed matrices, the exact
expansion, convex interpolation, and literal integral identification are
formalized with standard axioms.

The complete radial remainder beyond four atoms also satisfies

`|vᵀR_{>4}(q)v| ≤ E(q)c(q)vᵀAv/2`, for every `q≥3`.

The Cauchy estimate retains the rate `431/25` through radial integration;
`A > 10^(−11) diag(1000^(2i))` supplies the fixed-coordinate comparison.
`FifthTailRemainder.errorForm_bound` and
`errorMatrix_add_reserve_posSemidef` are formalized with standard axioms.

Every pure-atom tail has the exact scaling
`R_pure(c,q)=(c/c^(3/2))R₁₁(cq)` for `c,q>0`, and is positive definite
for `c≥1`, `q≥3`. `FifthPureTail.pureRadialTailMatrix_eq` and
`pureRadialTailMatrix_posDef` are formalized; the remaining pure atoms
correspond to `c=4,9,16`.

Each other doubled unequal pair `(1,4)`, `(2,3)`, `(2,4)`, `(3,4)`
satisfies `R_mn(q)+E(q)c(q)A/8>0` for `q≥3`. Their relative rates are
`15,11,18,23`, and their radial polynomials have degree at most 18.
All 92 fixed coefficient matrices, four uniform model comparisons, and
literal integral identities are formalized in `FifthOtherTail`.
Together with the remainder bound these payments consume exactly the
cubic reserve. The exact complete-source decomposition and reserve
cancellation are formalized in `FifthCompleteTail`; all seven capstones
use only `propext`, `Classical.choice`, and `Quot.sound`.

A smaller allocation is excluded: at `q=3`, the lower-gamma `(1,3)` model
paid by half the cubic reserve has negative fourth principal minor. This
auxiliary obstruction does not decide the complete-tail sign.
