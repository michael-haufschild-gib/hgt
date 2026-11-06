# Fixed theta heads cannot carry a positive all-rank Gaussian margin

- **Stage:** 3-formalized
- **Type:** THEOREM; Lean formalized
- **Wall:** Σ6

Let `J_M(a,b)` be the ordinary-pair current head, `0≤a<1/2`, and
`dν_τ(b)=exp(−τb²)db`, `τ>0`. For every fixed `M` and every `c>0`,
some finite rank and coefficient vector satisfy

`vᵀH_τ[J_M]v < c vᵀH_τ[1]v`.

Thus no fixed ordinary-pair head supplies a positive Gaussian margin
simultaneously at every rank. This does not assert that a head is negative.
For `a>0`, the established explicit error `E_M(a)` is strictly positive,
so the same conclusion applies with `c=E_M(a)`: no fixed head pays that
uniform error at every rank.

## Proof

The exact pair-tail formula is a bounded cosine times a constant times
`F(b/2,πnm exp r)`. The density `F` is the real Fourier transform of the
already established first-atom radial Schwartz profile. Each pair tail
is therefore continuous in frequency and tends to zero as `b→+∞`.
Its frequency-uniform bound is `C_nm exp(−3r)`. After multiplication by
the exact aperture weight this is integrable, so dominated convergence
gives continuity and decay for every aperture pair and every finite head.

For any bounded continuous density `f`, Gaussian Hankel completeness
applied to `f−c` gives the exact margin classification

`∀N,v: vᵀH_τ[f]v ≥ c vᵀH_τ[1]v` iff `∀b: f(b)≥c`.

The head is bounded by the actual bounded current plus the established
uniform error. Its decay rules out the right side whenever `c>0`.
Strict positivity of `E_M(a)` follows from its formula: the cost constant
is positive because it majorizes a strictly positive Bessel-tail density,
and all remaining factors are positive on `0<a<1/2`.

## Surviving control

For `M=1` and `a>0`, every finite Gaussian Hankel section is strictly
positive definite: the head is twice the strictly positive diagonal
aperture pair. A nonzero polynomial has only finitely many roots, so its
square integral against this continuous positive density is positive.
Thus strict positivity at all finite ranks coexists with the absence of
every positive rank-uniform Gaussian margin.

The [rank-uniform remainder](../3-formalized/full-theta-gaussian-rank-uniform-remainder.md)
still compares the complete and finite-head forms in this exact Gaussian
reference norm. A positive fixed margin cannot absorb that error at all
ranks. A proof of the full current's sign must retain cancellation or
use truncations adapted to frequency or polynomial direction; no such
sign estimate is established here.

## Lean

[ThetaPairGaussianCoercivityBoundary.lean](../../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ThetaPairGaussianCoercivityBoundary.lean):

- `thetaPairApertureCurrentHead_continuous_and_decay`: continuity and high-frequency decay.
- `thetaPairApertureCurrentHead_gaussian_floor_iff`: exact lower-margin classification.
- `thetaPairApertureCurrentHead_no_uniform_gaussian_floor`: every positive margin fails at some finite rank.
- `thetaPairCurrentRemainderBound_pos`: the explicit error is positive at positive aperture.
- `thetaPairApertureCurrentHead_cannot_pay_uniform_remainder`: the fixed-head error-absorption obstruction.
- `thetaPairApertureCurrentHead_one_gaussian_posDef`: strict positivity of every first-atom Gaussian section.

Direct source check passes. Capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
