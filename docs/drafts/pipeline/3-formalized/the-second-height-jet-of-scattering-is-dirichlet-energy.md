# The second height jet of scattering is Dirichlet energy

- **ID:** the-second-height-jet-of-scattering-is-dirichlet-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: differential energy intrinsic to the geometric Weil diagonal.
- **Contribution:** One exact second-height law, including its maximal finite domain and its raw geometric normalization.

## Theorem

Let `ω(t)=exp(−t/2)/(1−exp(−2t))`, `n=N+1`, and `U_t` denote physical
translation. For every complex physical L² state, including infinite energy,

`T_n(f) := n² ∫₀∞ exp(−nt) ω(t) ‖U_t f−f‖² dt`
`→ ½ D(f)`,

where `D(f)=∫ℝ (2πξ)² |Fourier(f)(ξ)|² dξ`. Finiteness of `D(f)` is
exactly membership in the existing Fourier H¹ domain.

For a complete Weil-form vector `u`, write `f=Ju`, `E_n(f)` for the finite
scattering energy, `b_n` for its exact Robin mass coefficient, and
`b∞=2 gammaHardyPhaseRate(0)`, with `P_k=ccmPrimeTransportOperator a k`. The actual geometric defect satisfies

`n² [Re W(u,u) − E_n(f) + (b_n−b∞)‖f‖²]`
`= T_n(f) − Σ_{2≤k≤exp(2a)} n² k^(−n) Λ(k) Re⟨P_k f,f⟩`.

The finite arithmetic sum tends to zero. Consequently:

- The geometric defect has a finite real limit **iff** `f∈H¹`.
- Its finite limit is `D(f)/2`.
- On every complete Weil state outside H¹ it tends to `+∞`.
- For a smooth interior source, `E_n` is the literal `RawGeometry.energy`
  and the limit is `½∫ℝ|u′(x)|²dx`.

## Proof

The finite jump kernel is `(1−exp(−nt))ω(t)`. Subtracting it from the
critical jump energy and removing the exact Robin mass drift leaves
`T_n` and the displayed finite-prime remainder. Its coefficients decay
exponentially, so multiplication by `n²` does not change their zero limit.

Plancherel gives the multiplier `n²∫₀∞exp(−nt)ω(t)(2−2cos(τt))dt`.
Changing variables `x=nt` rewrites it as

`φ_n(τ)=∫₀∞exp(−x)[(x/n)ω(x/n)]τ²x sinc²(τx/(2n))dx`.

The corpus's global bounds give

`½+t/4−t²/16−t³/32 ≤ tω(t) ≤ ½+t/4`.

Thus the integrand converges to `exp(−x)τ²x/2`, and is bounded by
`τ²exp(−x)(x/2+x²/4)`. The latter integrates to `τ²`. Hence
`0≤φ_n(τ)≤τ²` and `φ_n(τ)→τ²/2`. Tonelli transfers the exact multiplier
identity to every L² state. Dominated convergence proves the finite-energy
limit; Fatou forces divergence when the Dirichlet energy is infinite.
The Fourier derivative identity and Plancherel give the smooth physical
normalization.

## Lean

Module: `GaloisForLFunctions.HyperbolicArakelovTheory.TheSecondHeightJetOfScatteringIsDirichletEnergy`.
Namespace: `GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower`.

- `scatteringSecondHeightEnergy_eq_fourier`
- `tendsto_scatteringSecondHeightEnergy`
- `scatteringDirichletEnergy_ne_top_iff`
- `scatteringSecondHeightDefect_eq`
- `tendsto_scatteringSecondHeightDefect_finite`
- `tendsto_scatteringSecondHeightDefect_atTop`
- `finite_scatteringSecondHeightDefect_limit_iff`
- `scatteringDirichletEnergy_smooth`
- `tendsto_rawScattering_secondHeight`

Verification: plain `lake --old env lean` on the production module; eight
main dependency audits give only `[propext, Classical.choice, Quot.sound]`.
Imported by `HyperbolicArakelovTheory.lean`.

This identifies regularity of the existing geometric diagonal. It does not
require an invariant glued carrier or positivity of the unshifted Weil form.
