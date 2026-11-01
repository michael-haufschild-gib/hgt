# Fourth-order synthesis for the tilted spline

- **ID:** tilted-spline-fourth-order-synthesis
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, §2.1 A1
- **Statement:** The tilted cubic spline has synthesis error
  `O((k/n₀)^4 + 1/k)`. Its full-space and pole-hyperplane receivers have growth
  order eight; positivity at every fixed multiple of `(log N)^(1/8)` is equivalent to RH.

## Exact results

The normalized profile `φ = recentredProfile tiltedUnitSpline` has smooth
uniform approximations with derivative `L¹` bounds `A_q`, independent of the
approximation accuracy, for `q ≤ 4`.
For a smooth test `F` supported in `[-R,R]`, with derivative bounds `M_q`,
the Euler–Maclaurin atomic synthesis equals a translate of `F + D`, where
`D` is `C²`, supported in `[-R-1,R+1]`, and

- `|D| ≤ emConst M A 1 · (k/n₀)^4 + M₁ A₀/k`;
- `Lip(D) ≤ emLip M A k n₀`.

If `κ_N → ∞` and `(κ_N/N)^8 log κ_N → 0`, RH is equivalent to eventual
nonnegativity on all normalized spline atomic tests. The same equivalence holds
for the Markov form on tests whose negative exponential moment vanishes.
In particular, complete Weil matrices at overlap `2(log N)^α`, `α > 1/8`,
are eventually positive semidefinite exactly when RH holds.

At the endpoint, RH is equivalent to
`∀ K > 0, ∀ sufficiently large N, completeWeilEnergy(2K(log N)^(1/8),N) ≥ 0`
on every coefficient vector. The horizon threshold may depend on `K`.
The corresponding pole-hyperplane criterion holds for the normalized atoms.
Positivity at every multiple remains the RH-equivalent input.

## Proof

Convolve a smooth probability density with four unit boxes. Differentiating
replaces a box by half the difference of its endpoint masses, so the first
four derivative `L¹` norms are at most one. A fixed smooth cutoff equal to
`exp` on the common support transfers these bounds to the tilted spline by
Leibniz's rule. Scalar multiplication and dilation give the normalized profile.
This retains the fourth-derivative knot masses of the original `C²` spline.

Finite sums pass to the uniform limit, and dominated convergence passes the
convolution integrals. Smooth Euler–Maclaurin estimates therefore give the
fourth-order quadrature bound and a uniform synthesis Lipschitz bound.
Subtracting `F` gives the compactly supported `C²` perturbation above.
Its Lévy error tends to zero under eighth-order overlap growth. Existing Weil
continuity and pole correction then transfer smooth negative tests to the atoms.

For the endpoint, diagonal selection chooses multiples `K_N → ∞` slowly enough
to retain eventual positivity and ensure `κ_N ≥ K_N`. With `log N ≥ 1`,
`(κ_N/N)^8 log κ_N ≤ K_N^(-8) → 0`. The growth-order-eight receivers apply.

## Lean declarations

All modules lie in `formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/`.

| Module | Main declarations |
|---|---|
| `TheSplineHasUniformFourthDerivativeRegularizations.lean` | `exists_cubicSpline_regularization`, `exists_splineProbe_regularization_bounds` |
| `TheTiltedSplineHasFourthOrderSynthesis.lean` | `exists_recentred_tiltedUnitSpline_regularization_bounds`, `fourthOrderSynthesis_of_uniform_regularizations`, `exists_fourthOrderSynthesis` |
| `TheTiltedSplineReceivesAtTheEighthRoot.lean` | `riemannHypothesis_iff_tiltedSpline_atomicFamilies_nonneg_of_growthEight`, `riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_log_eighth`, `riemannHypothesis_iff_tiltedSpline_poleHyperplane_nonneg_of_growthEight` |
| `EveryEighthRootMultipleReceivesTheTiltedSpline.lean` | `riemannHypothesis_iff_tiltedSpline_nonneg_every_eighthRoot_multiple`, `riemannHypothesis_iff_tiltedSpline_pole_nonneg_every_eighthRoot_multiple`, `riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_every_eighthRoot_multiple` |

## Audit

All four leaves passed direct `lake --old env lean <file>` checks.
Every listed transitive axiom audit contains only
`[propext, Classical.choice, Quot.sound]`.
All four modules are imported by the programme umbrella.
