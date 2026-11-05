# Joint periodic window coercivity

- **ID:** joint-periodic-window-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0511 §2.1, A3.

## Theorem

For finitely many smooth windows `gᵢ` and mean-zero periodic twists `χᵢ`,
possibly of different periods, the complete tilted-spline Weil Gram matrix
is eventually positive definite at every positive critical multiple if and
only if the joint functions `(y,n) ↦ gᵢ(y)χᵢ(n)` are linearly independent.
Its normalized quadratic form then dominates `ηΣᵢ|vᵢ|²` for some `η>0`,
uniformly in complex coefficients. Nonprincipal characters of arbitrary
nonzero moduli are included, without a parity or primitivity restriction.

## Proof

The low-frequency and pole transforms of a coefficient vector `v` are bounded
by `C‖v‖₁/N` after Riemann normalization. Their possible negative contribution
to the normalized form is at most `C′‖v‖₂²/N²`. Above the fixed archimedean
horizon the complete symbol is nonnegative. On `[512N,1024N]`, the mean-value
theorem gives

`∫|Dₓ|² ≥ 256N Σxₙ²`,

since its error is `208Σn xₙ²≤208NΣxₙ²`. The tilted-spline lower bound then
pays `a(log N)/c⁸` times the mass, for `a>0`. The mass matrices converge to
the Gram matrix obtained by averaging over residues and integrating over
the window. Joint independence gives a positive lower eigenvalue `μ`.
Thus the normalized form dominates `(aμ/K−o(1))‖v‖₂²` along
`c_N=max(1,(K log N)^(1/8))`. Real and imaginary coefficient parts give
the same conclusion on the full complex coefficient space. Different
periods pass to their product without changing the actual twists.

Conversely, every relation among the joint functions gives a zero atomic
test at every resolution, so no positive-definite Gram matrix can exist.
Thus joint independence is necessary and sufficient for eventual positivity.

Same-parity character cross spectra are already computed by
`crossSpectralSum_charTwist`. Single-family polarization alone does not
determine mixed terms when both the twist and the spatial window vary.

## Lean

Owner: `ArithmeticHodgeTheoryOfDegenerations`.

- `JointPeriodicWindowMass.lean`: `MeanZeroTwist.of_dvd`,
  `tendsto_sum_jointTwistedWeights_mul`, `jointPeriodicMassGram_posDef`,
  `eventually_jointPeriodic_mass_coercive`.
- `JointPeriodicWindowsInheritThePolarization.lean`:
  `jointPeriodic_windows_coercive_at_criticalCurve`,
  `jointPeriodic_Gram_coercive_at_criticalCurve`,
  `joint_periodic_windows_inherit_at_every_multiple`,
  `joint_character_windows_inherit_at_every_multiple`,
  `jointTwistedGram_posDef_implies_joint_independent`,
  `joint_periodic_windows_eventually_posDef_iff`.
- Existing `TheCharacterWindowsAreGradedByParity.lean`:
  `crossPower_charTwist`, `crossPower_charTwist_eq_zero`,
  `crossSpectralSum_charTwist`. Equal parity couples through both
  `L(s,ψ̄₁ψ₂)` and `L(s,ψ̄₁ψ̄₂)`; opposite parity decouples.

All three direct source checks passed. Thirteen transitive axiom audits
use only `propext`, `Classical.choice`, and `Quot.sound`. Both new leaves
have acyclic import closures and owning-umbrella imports.

The family is fixed and finite. Uniform positivity through all conductors
and frequencies, the separate B6 obligation, is not asserted.
