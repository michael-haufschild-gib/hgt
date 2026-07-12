# Claim trace audit

This file is internal verification metadata and is not part of the manuscript.
The manuscript may be promoted only while every substantive mathematical claim below remains
covered by the listed unconditional declaration.

## Window and divisor foundation

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| \(A_L(w)\neq0\) for \(L>0\), \(\Re w\neq0\) | rectangularWindowAmplitude_ne_zero |
| \(A_L(-w)=e^{Lw}A_L(w)\) | rectangularWindowAmplitude_neg |
| exact square/edge decomposition | rectangularTwoEdgeTransform_sq_decomposition |
| reciprocal-square strip majorant | norm_rectangularWindowAmplitude_le and xiRectangularTwoEdgeTransform_square_le |
| multiplicity-exact reciprocal-square summability | xiSpectralPoint_inv_sq_summable |
| full divisor polarization equals the square sum | xiWeilPolarization_rectangular_eq_tsum_sq |
| diagonal Xi-Weil values and the sampled rectangular coefficients are real | xiWeilPolarization_diagonal_im_eq_zero, xiRectangularWeilLogCoefficient_im_eq_zero |
| exact dominant/remainder split | xiWeilPolarization_rectangular_sub_dominant_eq_tsum_remainder |
| uniform remainder bound | norm_xiWeilPolarization_rectangular_sub_dominant_le |

## Dirichlet continuation and multiplicity

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| right coefficients are summable and nonzero | xiRectangularRightCoefficient_summable, xiRectangularRightCoefficient_ne_zero |
| logarithmic samples are exact \(n^w\) monomials | xiRectangularTwoEdgeDominant_logSample_of_right |
| L-series equals twice the shifted-zeta carrier on the initial half-plane | LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta |
| reciprocal-\(3/2\) Xi divisor summability | xiSpectralPoint_inv_three_halves_summable |
| vertical square-root zeta bound | norm_riemannZeta_le_sqrt_norm_add_two |
| local normal convergence of the cancelled carrier on \(\Re s>1\) | summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne |
| numerator order \(m-1\) at every shifted Xi zero | xiRectangularCancelledSeries_order |
| denominator order \(m\) | xi_shifted_half_order |
| base continuation is meromorphic on \(\Re s>1\) | meromorphicOn_xiRectangularRightDirichletContinuation_rightOne |
| its simple poles are exactly the shifted right Xi support | meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one_iff |
| ordinary coefficient L-series equals twice the continuation initially | LSeries_xiRectangularRightDirichletComplex_eq_continuation |

## Completeness and quantitative laws

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| false RH forces cofinal negative divergence of actual sampled Weil values | xiWeilPolarization_rectangular_logSample_cofinally_unbounded_below |
| RH iff sampled values are nonnegative | riemannHypothesis_iff_rectangular_logSample_weil_nonneg |
| RH iff sampled values are eventually bounded below | riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow |
| RH iff sampled norms are bounded | riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd |
| sharp power exponent is the supremal transverse displacement | xiRightTransverseSup_is_sharp_rectangular_power_exponent |
| under RH the fixed-width family is uniformly bounded | norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis |

## Observable tail tomography

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| actual tail minus dominant carrier is bounded after finite deletion | norm_xiRectangularWeilRemainderCoefficient_le |
| correction L-series is analytic on \(\Re s>1\) | analyticAt_LSeries_xiRectangularWeilRemainderCoefficient |
| actual tail L-series equals the canonical continuation initially | LSeries_xiRectangularWeilTailCoefficient_eq_continuation |
| actual continuation is meromorphic throughout \(\Re s>1\) | meromorphicOn_xiRectangularWeilTailContinuation_rightOne |
| actual continuation has simple poles exactly at shifted right Xi zeros | meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff |
| equality of the complete simple-pole set with the shifted-pole range | observableSimplePoleSupport_eq_range_xiRightShiftedPole |
| exact recovery of the right Xi zero support by \(s\mapsto s-\tfrac12\) | xiRightZeroSupport_eq_image_observableSimplePoleSupport |
| RH iff the actual continuation is analytic at every point of \(\Re s>1\) | riemannHypothesis_iff_observableTailContinuation_analytic_rightOne |

## Screw coordinate

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| screw divisor series is absolutely summable | xiScrewDivisorTerm_summable |
| screw profile is real | star_xiScrewDivisor |
| exact fixed-width second-difference identity | xiWeilPolarization_rectangular_eq_screwCurvature |
| screw nonnegativity and eventual-lower-bound RH criteria | riemannHypothesis_iff_xiScrewWindowCurvature_logSample_nonneg, riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow |

## Axiom and lint gate

- Exact build target: GaloisForLFunctions.RHTower.CCMUnconditionalFoundation.
- Allowed foundational dependencies in the checked capstones:
  [propext, Classical.choice, Quot.sound].
- Repository lint must report no active sorry, admit, axiom, opaque, or unsafe declaration.
