# Retaining Suzuki's endpoint roots makes the strict-interior Gamma carrier boundary-log regular, formalized

- **ID:** `suzuki-root-retained-exterior-dilation`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-root-retained-exterior-dilation.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/InverseSqrtBinomialSeries.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ResolventHalfPowerProfile.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ResolventVectorProfile.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PowerTailSquareIntegrable.lean`
  - `formal/GaloisForLFunctions/HTGeometry/LogChartEnergyTransfer.lean`
  - `formal/GaloisForLFunctions/HTGeometry/FourierFirstOrderWeight.lean`
  - `formal/GaloisForLFunctions/HTGeometry/NonstationaryPhaseIteration.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpMultiplierBounds.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpFourierMultiplier.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRootRetainedProjectedSource.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRootRetainedEnergyEstimate.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRootRetainedTerminalBlocks.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRootRetainedJumpSource.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)` the retained carrier equation | `RootRetainedCarrier` |
| `(2)` the half-log trace in `QX` | the annihilation datum `P β = 0` |
| `(3)` `P F ∈ H¹ ∩ L²` | `norm_proj_resolventVecProfile_le`, `lintegral_sq_powerTail_ne_top`, `lintegral_sq_add_ne_top` |
| `(4)` `Q F' ∈ L²` | `energy_estimate`, `energy_estimate_div` |
| `(5)`, `(27)` the exact projected source equation | `projected_carrier_equation`, `hasDerivAt_projected` |
| `(6)`, `(14)`, `(30)` every exterior-return word retained | `proj_resolventVecProfile_eq_tail`, `invSqrtTail_scaled_eq` |
| `(6a)` the `dr`/`dL` energy conversion, and the separation | `integral_sq_spatial_eq_integral_exp_weighted`, `hasDerivAt_logTransport`, `lintegral_exp_weighted_eq_top` |
| `(7)` the prime profile | `resolventVecProfile`, `resolventProfileG`, `resolventProfileG_eq` |
| `(8)` the projected profile | `proj_resolventVecProfile_eq_tail` |
| `(9)` the grade-one operator bound | `norm_invSqrtTail_le`, `norm_invSqrtTail_scaled_le` |
| `(10)` the `L^{-3/2}` rate | `norm_proj_resolventVecProfile_le` |
| `(11)` the `−3/2` derivative | `hasDerivAt_resolventProfile_gradeZero`, `hasDerivAt_resolventProfile_gradeZero_closedForm`, `resolventProfileG_gradeOne_eq` |
| `(12)` the `−5/2` second derivative | `hasDerivAt_resolventProfile_gradeOne`, `hasDerivAt_resolventProfile_gradeOne_closedForm`, `resolventProfileG_gradeTwo_eq` |
| `(13)` `H¹ ∩ L²` on a terminal ray | `norm_resolventProfileG_le`, `lintegral_sq_resolventProfileG_ne_top`, `integrableOn_sq_powerTail` |
| `(15)`, `(17)` the exact forced Gamma equation | `forced_difference_equation` |
| `(18)` the affine symbol bound | `abs_gammaJumpMultiplier_le`, `exists_gammaJumpMultiplier_log_bound` |
| `(19)` `R : H¹(ℝ;X) → L²(ℝ;X)` | `eLpNorm_gammaJumpMultiplier_smul_le`, `norm_gammaJumpNormalizedSymbol_le` |
| `(20)` the jump of the prime derivative is `L²` | `norm_freq_smul_fourier_eq`, `norm_firstOrder_smul_fourier_le`, `eLpNorm_firstOrder_fourier_ne_top`, `eLpNorm_gammaJump_fourier_ne_top` |
| `(21)` the unweighted endpoint is accretive | `re_inner_gammaJumpNormalizedMulCLM_nonneg`, `gammaJumpNormalizedSymbol_nonneg` |
| `(22)`, `(23)` the energy estimate above threshold | `energy_estimate`, `energy_estimate_div`, `adjacency_bound_of_opNorm` |
| `(24)` the terminal phase floor | `phase_floor` |
| `(25)` the block gain and its summation | `oscillatory_ibp`, `norm_oscillatory_iterate_le`, `summable_dyadicBlockBound` |
| `(26)` `F' ∈ L²` | `lintegral_sq_add_ne_top` |
| `(28)` the projected source is unweighted `L²` | `norm_projectedSource_le`, `lintegral_sq_projectedSource_ne_top` |
| `(29)` the exact interior Schur complement | `schur_complement_of_inverse` |
| `(31)` the low-frequency counterterms | `lintegral_weighted_sq_expGerm_ne_top` |

## What the card actually closes

**Projection splits only the adjacency.**  `P` commutes with multiplication by `L`, with the jump
multiplier and with differentiation, but not with `T`.  So applying `P` to the carrier equation
leaves the interior equation intact and produces exactly one new term, `P T Q (QF)'` — that is a
theorem about which operators commute, not a modelling choice, and it is why no compression inverse
and no nonlinear conjugation appear.

**The exterior source costs only an operator norm.**  `‖P T Q y‖ ≤ ‖P‖‖T‖‖Q‖‖y‖` pointwise, so an
`L²` exterior derivative gives an `L²` source with no weight.  The Schur complement is still exactly
available afterwards — recovered here from an inverse witness on the exterior block — but as a
coordinate elimination performed on an already-solved system.

**One differentiation family carries all three grades.**  Writing the terminal resolvent as its
binomial series with the scale factored out, differentiating in `L` shifts the exponent and inserts
the factor `−(k+a)`.  The family indexed by `(a, g)` is therefore closed under differentiation, and
starting from `(1/2, 1)` the weights `−(2k+1)/2` and `(2k+1)(2k+3)/4` are produced by the
differentiation itself — they are precisely the coefficients of `(1−s)^{-3/2}` and `(1−s)^{-5/2}`
against the central binomials.  No separate generalized binomial series has to be constructed, and
the `−3/2` and `−5/2` resolvent powers of `(11)` and `(12)` come out with their classical constants
`−1/2` and `3/4`.

**Projection deletes grade zero and no path.**  The vector profile is the path expansion
`Σ_k c_k 2^{-k} L^{-(k+a)} T^k β`, whose `k`-th term is the totality of length-`k` adjacency words
from `β`.  Annihilating the trace kills the constant term alone, so the projected profile begins at
`k = 1` and gains one full power of `L`: the rate `L^{-3/2}` of `(10)`, with the explicit constant
`‖P‖‖T‖‖β‖`, obtained from `ρ/(1−ρ) ≤ 2ρ` on the ray `L ≥ ‖T‖`.

**Square integrability is a threshold, and the spatial norm is a different threshold.**  A profile
bounded by `C L^{-p}` has finite squared mass on a terminal ray exactly through `p > 1/2`, so the
grade-one value and both derivatives qualify.  Under `r = e^{-L}` the spatial energy is the
boundary-log energy weighted by `e^{L}`, and the exponential defeats every polynomial rate: a
profile with a fixed power lower bound has infinite spatial energy.  Both halves of the card's
`H¹(dL)`-but-not-`H¹(dr)` statement are theorems, not conventions.

**The energy estimate spends the adjacency against the position gap.**  Pairing the equation with
the derivative it solves for, coercivity of the position term, accretivity of the jump term and
boundedness of the adjacency give `(2L₀ − τ)‖E'‖ ≤ ‖forcing‖`.  The jump term is discarded on the
correct side, so no sign hypothesis on the adjacency is needed, and the estimate is stated for the
three paired values — a cut-off equation simply contributes its residual to the forcing.

**The jump costs exactly one derivative.**  Its symbol is at most affine, so it is bounded from the
first-order weight to `L²`; and the first-order Fourier weight is the transform of the derivative,
`|ξ|‖𝓕v(ξ)‖ = (2π)⁻¹‖𝓕(v')(ξ)‖`.  Composing, a profile with square-integrable value and derivative
has square-integrable jump — which is `(20)` applied to the prime derivative, whose value and
derivative decay at `L^{-3/2}` and `L^{-5/2}`.

**Terminal smoothness is a gain-versus-price count.**  Against a phase `e^{iLη}` the antiderivative
of the phase is the phase over `iL`, so each integration by parts on an amplitude vanishing at the
block endpoints trades one derivative for one power of `|L|⁻¹`; `N` of them give `|L|^{-N}` against
the `N`-th derivative mass.  The resulting block bounds `2^{j(m+1/2−N)}(L+j)^{-N}` are geometric in
`j` exactly when `N > m + 1/2`, so every number of scale derivatives leaves a convergent sum.  The
phase never degenerates: with an accretive jump symbol the phase operator stays above `L − ‖T‖/2`.

## Hypotheses

Object data only: the projection and the adjacency as bounded operators, the jump as a linear map
commuting with the projection, the trace annihilation `Pβ = 0`, the terminal threshold `‖T‖ < 2L₀`,
and — for the Fourier statements — integrability and differentiability of the cut-off profile, which
the terminal decay supplies.  The Schur complement is stated from an explicit inverse witness on the
exterior block rather than from an unproved invertibility claim.  No `sorry`, `axiom`, `opaque` or
`unsafe`; every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Boundary of what is formalized

`(16)` — square integrability of the Gamma correction itself — is quoted from
`suzuki-gamma-prime-normal-corona-equivalence.md` and is that card's result, not this one's.

In `(25)` the two ingredients are separated: the gain mechanism (`N` integrations by parts give
`|L|^{-N}` against the `N`-th derivative mass) and the summation over blocks (a bound
`C 2^{j(m+1/2−N)}(L+j)^{-N}` sums when `N > m+1/2`) are both unconditional Lean.  What is not
formalized is the intermediate bookkeeping that reads the constant `C_{m,N}` off the explicit
nonstationary Gamma representation, since that representation is supplied by the open source-core
gate rather than constructed here.

## Open boundary

What stays open is what the card declares open, and all of it is research rather than missing Lean:
identification of every completed zero mode with a full root-retained Gamma normal family, the exact
global cutoff intertwining, the trace-zero weighted upgrade to an exponent above `1/2`, and two-port
root-trace return injectivity.  The gates this card claims — grade-one start, `H¹(dL) ∩ L²(dL)` for
the strict-interior component, the unweighted `L²` derivative of the Gamma correction, the exact
projected exterior source and its `L²` bound, full retention of exterior-return words, and
compatibility with the two low endpoint counterterms — are closed.
