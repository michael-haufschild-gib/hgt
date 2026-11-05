# Rank-uniform Gaussian remainder for the full theta current

- **Stage:** 2-fully-proven
- **Type:** THEOREM; Lean pending
- **Wall:** Σ6

Fix `τ>0`, `0≤a<1/2`, and `M≥0`. Write
`J_M(a,b)=2Σ_(1≤n,m≤M)P_nm(a,b)`, `δ_M=J−J_M`, and
`E_M(a)=288a C(0)exp(−π(M+1))/((9−a²)²(1−exp(−π))²)`.
Let `dν_τ(b)=exp(−τb²)db`.
For every real polynomial `p`,

`|∫ p(b)²δ_M(a,b)dν_τ(b)| ≤ E_M(a)∫ p(b)²dν_τ(b)`.

Equivalently, at every finite rank, the Gaussian moment Hankel form of
the error lies between `−E_M(a)` and `E_M(a)` times the ordinary Gaussian
moment form. The constant is independent of rank, polynomial degree,
and coefficients. A fixed positive Gaussian window is complete for the
actual current's all-rank sign criterion; this is an equivalent complete
formulation, not a fixed-rank truncation of the target.

## Proof

The [actual-current bound](../3-formalized/full-theta-aperture-current.md)
gives `|δ_M(a,b)|≤E_M(a)` at every frequency. The ordinary-pair aperture
spectra are measurable in frequency: use fixed-domain translations for
the moving tail cutoff, then parameter integration of the continuous
atom kernel. Thus `δ_M` is bounded and measurable. Gaussian polynomial
moments are integrable, so all square/error integrals are absolutely
integrable. Multiply the pointwise bound by `p(b)²≥0`, integrate, and
apply the integral triangle inequality. Expanding a finite coefficient
polynomial identifies the two square integrals with the stated Hankel
quadratic forms.

This controls the remainder uniformly over every polynomial direction
in a complete Gaussian formulation. It does not establish positivity of
the finite pair heads or of the full signed current; that sign remains
open.
