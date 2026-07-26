# Deninger Gaussian Lefschetz heat-contour universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `deningerResolventLefschetzTrace`, which identifies the centered Deninger divisor resolvent
  trace with the independently defined continued prime–archimedean source trace at every
  admissible point;
- `exists_admissible_rectangle_containing_xiZeroCopy_finset`, which selects cofinal rectangles
  and exposes admissibility on all four edges;
- the Gaussian spectral-rectangle residue theorem, which converts the source contour into the
  enclosed multiplicity-exact Xi Gaussian sum;
- complex-time Xi heat summability and the RH vertical bound.

The corpus contains a resolvent Lefschetz formula and Gaussian source contours separately, but no
theorem performs Gaussian functional calculus directly on the Deninger resolvent trace or gives
its complex-time vertical bound.

## Universal law

Let

`L(z) = Tr((Theta-1/2)^(-1) - (Theta-1/2-z)^(-1))`

be the multiplicity-exact centered Deninger divisor resolvent trace. Under RH, for every complex
heat time `tau` with `Re tau>0` and every `epsilon>0`, there is an admissible rectangle `R` such
that

`C_R(tau) = (2*pi*i)^(-1) ∮_(∂R) exp(-tau*z^2) L(z) dz`

satisfies

`dist(C_R(tau), sum_rho exp(-tau*alpha_rho^2)) < epsilon`

and

`|C_R(tau)| < HeatTrace(Re tau) + epsilon`.

Thus cofinal contour functional calculus of the Deninger resolvent converges to the full
complex-time Xi heat trace, with RH forcing the same vertical norm domination as the spectral
heat semigroup.

## Dependency-closed paper proof

1. RH and `Re tau>0` make
   `q ↦ exp(-tau*alpha_q^2)` absolutely summable over multiplicity copies. Choose a finite packet
   whose partial sum is within `epsilon` of the full heat trace.
2. Cofinal rectangle selection places that packet inside a positively oriented rectangle and
   proves every point of every edge is `XiExplicitAdmissible`.
3. On each edge, `deningerResolventLefschetzTrace` gives
   `L(z)=continuedPrimeArchSourceRelativeTrace(z)`. Contour congruence therefore replaces the
   Deninger integrand by the arithmetic source integrand.
4. The Gaussian spectral-rectangle theorem evaluates the latter contour exactly as
   `2*pi*i` times the enclosed multiplicity-exact Gaussian sum.
5. The rectangle contains the selected finite packet, so directed partial-sum convergence gives
   the required approximation to the full complex heat trace.
6. Triangle inequality plus the existing RH vertical bound
   `|HeatTrace(tau)|≤HeatTrace(Re tau)` gives the asserted norm inequality.

No trace-class operator completion, unproved Hodge metric, numerical computation, or
interchange of an infinite sum with a contour integral enters.

## Formal targets

- `rectIntegral_deningerResolventLefschetzTrace_eq_xiZeroCopyClosedRectangleSum`
- `exists_admissible_deningerGaussianContour_approximates_heatTraceC_of_rh`
- `deninger_gaussianLefschetz_heatContourUniversality`

## Novelty audit

Primary-source search after the dependency-closed proof found:

- Deninger's cohomological program for arithmetic zeta functions
  ([arXiv:math/0605724](https://arxiv.org/abs/math/0605724));
- Connes's trace-formula interpretation of the explicit formulas
  ([arXiv:math/9811068](https://arxiv.org/abs/math/9811068));
- generic zeta/heat-kernel contour technology
  ([arXiv:1010.5872](https://arxiv.org/abs/1010.5872)).

None states the exact combination proved here: Gaussian contour functional calculus of the
centered Deninger divisor resolvent trace, multiplicity-exact Xi packet convergence, and the RH
complex-time vertical bound. Exact literature novelty remains **[NOVELTY UNVERIFIED]**.

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/DeningerGaussianLefschetzHeatContourUniversalityLaw.lean`

and imported by:

`formal/GaloisForLFunctions/RHTower.lean`.

The declarations are:

- `rectIntegral_deningerResolventLefschetzTrace_eq_xiZeroCopyClosedRectangleSum`;
- `exists_admissible_deningerGaussianContour_approximates_heatTraceC_of_rh`;
- `deninger_gaussianLefschetz_heatContourUniversality`.

`lake env lean /private/tmp/law471_scratch.lean` passed after expanding the two unavailable cached
imports into their already verified source declarations. Direct module verification currently
stops before elaboration because `DeningerLefschetzTrace.olean` is absent. Per project discipline,
that dependency will be compiled only by the final targeted `lake build
GaloisForLFunctions.RHTower` audit.
