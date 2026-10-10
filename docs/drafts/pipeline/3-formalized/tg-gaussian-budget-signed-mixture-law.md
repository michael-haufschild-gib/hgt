# TG — Signed mixtures of Gaussian budgets: the smallest weighted shift decides

- **ID:** TG-MIX-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional) — strengthens TG-MIX-1 to arbitrary real weights
- **Statement:** Distinct shifts σ_j > 0, real weights c_j, smallest shift σ₀ = σ_{j₀} with c_{j₀} ≠ 0.
  If Σ_j c_j (P_{σ_j} − C_{σ_j})(y) ≤ B on (0,1], then ξ ≠ 0 on Re z > σ₀ (any signs).
  Corollary: for ½ < σ < 2, RH ⟺ (P_½ − C_½) − (P_σ − C_σ) ≤ B on (0,1]: the central budget of the
  quotient Euler product ζ(s)/ζ(s+σ−½), with nonnegative tempered coefficients Λ(n)(1 − n^{½−σ}).

## Proof
Landau on the deficit carrier: Σ_j c_j ξ'/ξ(σ_j+2w) = K(w) for Re w > 3 with K holomorphic on Re w > 0.
Clear denominators: R = K·Q, Q = Π_j ξ(σ_j+2w), R = Σ_j c_j ξ'(σ_j+2w)Π_{i≠j}ξ(σ_i+2w); identity theorem
on Re w > 0. Given a zero z with Re z > σ₀, take z* maximizing Re on the compact set of zeros with
Im = Im z, Re z ≤ Re ≤ 1. At w* = (z*−σ₀)/2 the points σ_j + 2w* = z* + σ_j − σ₀ (j ≠ j₀) lie further right
on the same line, hence are not zeros. Residues: (w−w*)Σ c_j ξ'/ξ(σ_j+2w) → c_{j₀} ord(z*)/2 ≠ 0, while
(w−w*)K(w) → 0. Contradiction.

## Lean
`RHTower/GaussianBudgetSignedMixtureLaw.lean` (489 lines), wired after GaussianBudgetShiftMixtureLaw.
`integral_gaussianSignedMixtureDeficit_mul_cexp`, `tendsto_sub_mul_logDeriv_xi_affine` (residue of
ξ'/ξ(a+2w)), `xi_affine_eventually_ne_zero`, `xi_ne_zero_of_gaussianSignedMixtureBudget`,
`riemannHypothesis_iff_gaussianDifferenceBudget`. Axioms [propext, Classical.choice, Quot.sound].

## Reading
The "maximal zero on a horizontal line" device turns any finite linear relation between shifted
log-derivatives into a triangular system: the top zero is seen only by the smallest shift. Hence no
finite linear combination of Gaussian budgets (differencing in σ, quotients ζ(s)/ζ(s+a), Eisenstein
products) changes the RH content; a TG producer cannot come from shift-algebra of ζ alone.
