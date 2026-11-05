# The completed Weil Riesz vectors are bounded

- **ID:** weil-riesz-boundedness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every Fourier-evaluation Riesz vector before contact has a bounded measurable physical representative, zero outside its exact closed aperture.

## Proof

The real CCM form domain equals the supported maximal inverse-Doob graph domain.
Thus `T_t(F)=(F-t)₊` is admissible for `t≥0`. Every edge product
`(F(x)-F(y))(T_t(F)(x)-T_t(F)(y))` is nonnegative, including every prime-power edge.

For `μ=θ(x)cosh(x/2)dx`, the cutoff archimedean kernel is

`kδ(x,y)=1_{|x-y|≥δ}ω(|x-y|)/(cosh(x/2)cosh(y/2))`.

It is bounded by `Cδ=(1-exp(-2δ))⁻¹` and `μ(ℝ)=1/2`. Its off-diagonal action
satisfies `|KδF(x)|≤Cδ‖F‖₂`. On every fixed aperture its row mass `mδ(x)` tends
uniformly to infinity: a positive compact lower bound on `θ(x+t)/cosh(x/2)`
reduces this to divergence of `∫δ¹ω(t)dt`.

The completed cutoff energy is exactly
`Eδ(F,G)=∫G(mδF-KδF)dμ`. Fubini is justified by the bounded cutoff kernel,
finite mass, and the two L² norms. For positive truncations, `Eδ(F,G)≤E(F,G)`.

Split the actual Fourier Riesz vector into two completed real graph coordinates.
Polarization identifies their Weil pairings with the real and imaginary Fourier
forcing. For nonnegative `G`, its absolute value is at most
`exp(a|Im z|)∫Gdμ`. The two polar terms contribute at most
`2(|⟨F,1⟩|+|⟨F,tanh⟩|)∫Gdμ`.

Choose `δ` with `mδ>2`, let `B` be the combined forcing bound, and put
`t=Cδ‖F‖₂+B`. Testing with `G=T_t(F)` gives `∫FG≤t∫G`.
Since `FG=G²+tG`, the truncation vanishes in L². Apply this to both signs of
both real coordinates. Boundedness of theta transfers the result to the physical
complex source. An indicator removes the exceptional null set while retaining
exact aperture support and measurability.

The Riesz identity against the entire completed form domain also places the
physical vector in the restricted Weil operator domain. Its operator image is
`1_{[-a,a]}(x) exp(-i conj(z)x)`, bounded by `exp(a|Im z|)`.
This follows from the Friedrichs representation theorem, with no boundary
regularity assumption.

## Lean endpoints

Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact`.
Module `TheCompletedWeilRieszVectorsAreBounded.lean`:

- `evalVector_bounded_real_graph_coordinates`
- `evalVector_physical_essentially_bounded`
- `evalVector_has_bounded_physical_representative`

The production module passed `lake --old env lean`. Each endpoint's transitive
axioms are exactly `[propext, Classical.choice, Quot.sound]`. The umbrella imports it.
The forcing and cutoff identity are proved in `TheWeilRieszEquationHasBoundedForcing`
and `TheCutoffArchimedeanEnergyHasItsLiteralKernel`.

`TheWeilRieszVectorsSolveTheLiteralOperatorEquation.lean` proves
`evalVector_operator_domain_and_apply`, `evaluationForcing_coeFn`, and
`evaluationForcing_bounded`. Its production plain audit and all three transitive
axiom checks also pass with exactly the standard three axioms above.

## Remaining boundary problem

This theorem supplies bounded actual Riesz sources. Normalized boundary traces,
aperture differentiation, and the Krein reflection function remain unproved; see
[normalized boundary traces](../1-in-progress/normalized-boundary-traces-of-weil-riesz-vectors.md).
