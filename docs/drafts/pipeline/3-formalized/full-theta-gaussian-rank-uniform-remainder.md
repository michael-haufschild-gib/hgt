# Rank-uniform Gaussian remainder for the full theta current

- **Stage:** 3-formalized
- **Type:** THEOREM; Lean formalized
- **Wall:** Σ6

Fix `τ>0`, `0≤a<1/2`, and `M≥0`. Write
`J_M(a,b)=2Σ_(1≤n,m≤M)P_nm(a,b)`, `δ_M=J−J_M`, and
`E_M(a)=288a C(0)exp(−π(M+1))/((9−a²)²(1−exp(−π))²)`.
Let `dν_τ(b)=exp(−τb²)db`.
For every real polynomial `p`,

`|∫ p(b)²δ_M(a,b)dν_τ(b)| ≤ E_M(a)∫ p(b)²dν_τ(b)`.

Writing `H_τ[J]_(i,j)=∫ b^(i+j)J(b)dν_τ(b)`, at every finite rank,

`|vᵀ(H_τ[J]−H_τ[J_M])v| ≤ E_M(a) vᵀH_τ[1]v`.

The constant is independent of rank, polynomial degree, and coefficients. A fixed positive Gaussian window is complete for the
actual current's all-rank sign criterion; this is an equivalent complete
formulation, not a fixed-rank truncation of the target.

## Proof

The [actual-current bound](../3-formalized/full-theta-aperture-current.md)
gives `|δ_M(a,b)|≤E_M(a)` at every frequency. The ordinary-pair aperture
spectra are measurable in frequency: use fixed-domain translations for
the moving tail cutoff, then parameter integration of the continuous
atom kernel. Thus `δ_M` is bounded and measurable. Gaussian polynomial
moments are integrable, so all square/error integrals are absolutely
integrable. Also `J_M=J−δ_M` is bounded and measurable, so moment
linearity identifies the error matrix with the difference of the actual
and truncated moment matrices. Multiply the pointwise bound by `p(b)²≥0`,
integrate, and apply the integral triangle inequality. Expanding a finite coefficient
polynomial identifies the two square integrals with the stated Hankel
quadratic forms.

This controls the remainder uniformly over every polynomial direction
in a complete Gaussian formulation. It does not establish positivity of
the finite pair heads or of the full signed current; that sign remains
open.

## Lean

[ThetaPairGaussianRemainder.lean](../../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ThetaPairGaussianRemainder.lean):

- `thetaPairCurrent_gaussian_polynomial_remainder_le`: every polynomial square.
- `thetaPairCurrent_gaussian_hankel_remainder_le`: every finite rank and coefficient vector.
- `thetaPairCurrentRemainderBound`: explicit error constant, independent of rank.

Gaussian completeness is the existing
`RHTower.hedenmalmGaussianHankelCone_iff_fourierNonnegative` in
[HedenmalmGaussianHankelRH.lean](../../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmGaussianHankelRH.lean).
Direct source check passes. Capstone and completeness axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
