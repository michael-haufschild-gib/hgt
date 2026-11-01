# Fourth-order synthesis for the tilted spline

- **ID:** tilted-spline-fourth-order-synthesis
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, §2.1 A1
- **Statement:** The tilted cubic spline admits log-lattice synthesis error
  `O((k/n₀)^4 + 1/k)`, giving the full-space receiver above exponent `1/8`
  and at every multiple of the endpoint scale.

## Mathematical gap

`TheEulerMaclaurinSynthesis.abs_emSynth_dilate_sub_le` assumes a smooth profile.
`tiltedUnitSpline` is only `C²`; its third derivative has jumps. Applying the
smooth theorem directly does not prove the required estimate. The fourth
derivative must include the finite knot masses, or a smooth approximation must
retain a uniform fourth-derivative `L¹` bound.

## Proved component

For every `ε > 0`, the cubic spline `B` has a smooth approximation `G`, supported
in `[-5,5]`, with `sup |G-B| ≤ ε` and `∫ |G⁽q⁾| ≤ 1` for `q ≤ 4`. For the tilt
`U(x)=exp(x)B(x)`, there are finite constants `A_q`, independent of `ε`, with
the same approximation property and `∫ |G⁽q⁾| ≤ A_q` for `q ≤ 4`.

Lean: `exists_cubicSpline_regularization` and
`exists_splineProbe_regularization_bounds` in
`SpacingScaleHarmonicAnalysis/TheSplineHasUniformFourthDerivativeRegularizations.lean`.
Direct leaf check passed; both transitive axiom lists are
`[propext, Classical.choice, Quot.sound]`.

## Proof route

Regularize the spline by convolving a smooth probability density with four
unit boxes. Differentiation replaces a box by half the difference of its
endpoint masses; thus the first four derivative `L¹` norms are at most one,
uniformly in the smoothing density. Transfer through the exponential tilt and
dilation, apply smooth Euler–Maclaurin, then pass to the spline limit. A fixed
smooth cutoff equal to `exp` on `[-5,5]` bounds all tilt derivatives uniformly;
the existing Leibniz estimate then suffices. Uniform approximation gives
pointwise convergence of the finite atomic sums; dominated convergence handles
the convolution integrals. The same limit transfers the synthesis Lipschitz
bound, without requiring convergence of derivatives.
The synthesis perturbation must also extend to `C²` profiles:
`exists_emSynthesis_of` itself still assumes smoothness. At the
endpoint, positivity for every fixed multiple permits diagonal selection of
slowly increasing multiples. Choose each horizon threshold to ensure both
positivity and increasing dilation; the eighth-power overlap error is bounded
by the inverse eighth power of the selected multiple. This reduces the endpoint
to the growth-order-eight receiver. The existing
`RenormalizedArithmeticPotentialTheory.exists_schedule_of_forall_eventually`
provides this diagonal selection. Prove the corresponding corrected
pole-hyperplane receiver.

## Gates

- [x] Concrete target and existing synthesis interface identified.
- [x] Uniform smooth regularizations through the fourth derivative, including the tilt.
- [ ] Fourth-order spline quadrature with all analytic inputs proved.
- [ ] Full-space and pole-hyperplane receivers.
- [ ] Leaf compilation, umbrella import, and transitive axiom audit.

## Remaining scope

The requested sequence is A1–A28. A1 is active; A2–A28 remain unaudited.
Numerical items must respect the user's prohibition on computations.
