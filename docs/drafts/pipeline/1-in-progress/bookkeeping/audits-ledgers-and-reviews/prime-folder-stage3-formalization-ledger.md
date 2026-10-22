# Prime folder — stage-2 → stage-3 formalization ledger

- **Scope:** every card in `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/prime`
  must have its proven theorems formalized unconditionally in Lean 4 and then move to
  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
- **Folder size at sweep start (2026-08-19):** 35 cards.

## Working rules

0. Search the Lean tree for the card's own content first:
   `scripts/formal_tools.py research "<theorem>"` **and** a plain `rg` on the symbol names.
1. No added hypotheses standing for analytic inputs; no axioms; no `sorry`.
2. Check with `lake env lean <file>` in the foreground, one process at a time.
   Build only the oleans actually needed. Wire finished modules into the area umbrella;
   never build the umbrella.
3. Audit axioms in a `/tmp` scratch file (`#print axioms`); expect only
   `propext`, `Classical.choice`, `Quot.sound`.

## Card inventory

| # | Card | State |
|---|---|---|
| 1 | `prime-arch-bernstein-half-order-pringsheim-singularity` | todo |
| 2 | `prime-arch-bernstein-legendre-double-source-kernel` | **stage 3** |
| 3 | `prime-arch-bernstein-mobius-pullback-gutzmer-law` | **stage 3** |
| 4 | `prime-arch-bernstein-pringsheim-collar-transfer` | **stage 3** |
| 5 | `prime-arch-explicit-circle-state-reflection-law` | todo |
| 6 | `prime-arch-moment-pole-residue-pinch-law` | **stage 3** |
| 7 | `prime-arch-shifted-sector-circle-valuation-cone` | todo |
| 8 | `prime-boundary-perturbative-jet-monodromy-escape` | todo |
| 9 | `prime-boundary-symmetric-dickman-zero-free-law` | todo |
| 10 | `prime-corona-constraint-opacity-law` | todo |
| 11 | `prime-coshift-eigenline-regularized-boundary-complex` | **stage 3** |
| 12 | `prime-coshift-row-boundary-trace-nonclosable` | **stage 3** |
| 13 | `prime-coshift-row-orthogonal-spectral-gap` | **stage 3** |
| 14 | `prime-cyclotomic-coefficient-field-escape` | todo |
| 15 | `prime-diagonal-singular-trace-dephasing` | todo |
| 16 | `prime-exponential-holomorphic-determining-source-image` | todo |
| 17 | `prime-fisher-superspace-unimodular-phase-blindness` | todo |
| 18 | `prime-grade-monodromy-divisor-mobius-equivalence` | todo |
| 19 | `prime-indexed-rvm-trace-class-hp-normal-form` | todo |
| 20 | `prime-laplace-gamma-clock-descent-anomaly` | todo |
| 21 | `prime-laplace-gamma-jet-incidence-phase-transition` | todo |
| 22 | `prime-log-action-condensation-normal-cone-law` | todo |
| 23 | `prime-poisson-superselection-screen` | todo |
| 24 | `prime-power-dirichlet-complex-jet-independence` | todo |
| 25 | `prime-quasi-inner-dixmier-residue` | todo |
| 26 | `prime-residue-krein-hamming-product-law` | todo |
| 27 | `prime-screen-bounded-observable-almost-periodicity` | todo |
| 28 | `prime-shift-residue-closability-criterion` | todo |
| 29 | `prime-sieve-boolean-first-trace-connection-curvature` | todo |
| 30 | `prime-square-deformed-reflection-line-superessential-fracture` | todo |
| 31 | `prime-square-mobius-fourier-complementary-record-law` | todo |
| 32 | `prime-superspace-wick-anisotropy-decompactification` | todo |
| 33 | `prime-support-ht-horizon-hodge-cofactor-law` | todo |
| 34 | `prime-tail-copoisson-essential-boundary-bockstein` | todo |
| 35 | `prime-trace-critical-energy-divisor-budget` | todo |

## Promotions

| Date | Card | Lean module(s) |
|---|---|---|
| 2026-08-19 | `prime-coshift-eigenline-regularized-boundary-complex` | `RHTower/PrimeCoShiftModel.lean`, `RHTower/PrimeCoShiftRowGraph.lean`, `RHTower/PrimeCoShiftBoundaryComplex.lean` |
| 2026-08-19 | `prime-coshift-row-boundary-trace-nonclosable` | `RHTower/PrimeCoShiftRowGraph.lean` |
| 2026-08-19 | `prime-arch-moment-pole-residue-pinch-law` | `RHTower/PrimeArchMomentPoleResidue.lean` |
| 2026-08-19 | `prime-arch-bernstein-pringsheim-collar-transfer` | `RHTower/PrimeArchBernsteinPringsheimCollar.lean`, `HTGeometry/VivantiPringsheim.lean`, `HTGeometry/SegmentAnalyticContinuation.lean` |
| 2026-08-19 | `prime-arch-bernstein-legendre-double-source-kernel` | `RHTower/BernsteinLegendreDoubleSourceKernel.lean` |
| 2026-08-19 | `prime-arch-bernstein-mobius-pullback-gutzmer-law` | `RHTower/PrimeArchBernsteinMobiusPullback.lean`, `RHTower/PrimeArchBernsteinMobiusPullbackSource.lean`, `HTGeometry/AntidiagonalRegrouping.lean`, `HTGeometry/GutzmerPowerSeries.lean` |
| 2026-08-19 | `prime-coshift-row-orthogonal-spectral-gap` | `RHTower/PrimeCoShiftKernelProjection.lean`, `RHTower/PrimeCoShiftSpectralGap.lean`, `HTGeometry/CommutingProjectionIntersectionEnergy.lean`, `HTGeometry/AdjointTransverseLowerBound.lean` |

## 2026-08-19 — co-shift cluster (cards 11, 12, 13)

New Lean modules (all `lake env lean` clean):

- `HTGeometry/CommutingProjectionIntersectionEnergy.lean` — product of two commuting orthogonal
  projections is the projection onto the intersection; finite `Finset` energy bound; antitone
  families of closed subspaces have strongly convergent projections (mathlib's monotone statement
  read through orthogonal complements); the commuting-family bound
  `dist(x, ⨅ M_i)² ≤ ∑ dist(x, M_i)²`.
- `RHTower/PrimeCoShiftModel.lean` — `H = ℓ²(ℕ≥1)`, `primeShift`/`primeCoShift` built on the
  pre-existing `RHTower.lpScalarInjection` / `lpCoordinatePullback`; `rowOp s p = V_p^* - p^{-s}`;
  `eigenSubmodule s = ⨅_p ker(rowOp s p)`; the coordinate law `x_n = n^{-s} x_1`; the ground state
  `Ψ_s`; **the common eigenline theorem** `eigenSubmodule s = ℂ ∙ Ψ_s` for `Re s > 1/2` and
  `= ⊥` for `Re s ≤ 1/2`.
- `RHTower/PrimeCoShiftRowGraph.lean` — `ω` double-counting (`tsum_prime_shift`),
  `coShiftEnergy = omegaEnergy`, prime-zeta energy finiteness, the two-sided comparison (5)/(6),
  the graph-norm equivalence (7), the exact graph domain, the prime-supported non-closability
  sequence (8)–(12), and the divergence (13).  Also `rowGraph` closed, `rowDomain` dense,
  and `ker = eigenSubmodule`.

Also landed: `HTGeometry/AdjointTransverseLowerBound.lean` (reduced minimum modulus from a
bounded-below adjoint), `RHTower/PrimeCoShiftKernelProjection.lean` (the closed-form kernel
projection `P_p = (1-|a|²) B_p E_p B_p^*` and its commutation at distinct primes), and
`RHTower/PrimeCoShiftSpectralGap.lean` / `RHTower/PrimeCoShiftBoundaryComplex.lean`.

**Cluster CLOSED**: cards 11, 12, 13 are at
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
All new modules are wired into `GaloisForLFunctions.RHTower` / `GaloisForLFunctions.HTGeometry`
and audit clean (`propext, Classical.choice, Quot.sound` only).

## 2026-08-19 — prime-screen almost periodicity (card 8)

New Lean modules (both `lake env lean` clean, wired into their umbrellas, axiom-clean):

- `HTGeometry/CompactGroupAlmostPeriodic.lean` — `IsBohrAlmostPeriodic`; the tube-lemma
  neighbourhood `exists_nhds_one_norm_translate_sub_le`; relative density of flow returns
  `exists_relatively_dense_mem` (no continuity of the flow needed, only the homomorphism law);
  `isBohrAlmostPeriodic_of_compact_flow`; `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero`
  (AP ∩ C₀ = {0}); and the measure layer `screenAverage`, `integrable_translate`,
  `continuous_screenAverage`, `isBohrAlmostPeriodic_screenExpectation`,
  `screenExpectation_eq_zero_of_tendsto_zero`, all for a general normed space of values.
- `RHTower/PrimeScreenAlmostPeriodicNoGo.lean` — `PrimeTorus = ∏_p S¹` with its compact
  commutative group / second-countable / Borel instances; the Kronecker flow `primeKronecker`
  with `primeKronecker_add` and `continuous_primeKronecker`; the critical-line decay
  `tendsto_XiC_ofReal_atTop` (from the corpus theorem `exists_norm_XiC_ofReal_le` at `δ = 1/2`);
  and the two no-gos `not_exists_primeScreen_symbol_eq_XiC`,
  `not_exists_primeScreen_observable_eq_XiC`.

Corpus leads that removed the expected hard work: `exists_norm_XiC_ofReal_le`
(`ThetaCuspComplexStrip`) already supplies exponential decay of ξ on the critical line, so no
Stirling asymptotics, no zeta convexity bound and no Phragmén–Lindelöf step was needed;
`XiC_zero_ne` (`XiHadamardFactorization`) supplies the nonvanishing.

Card `prime-screen-bounded-observable-almost-periodicity` promoted to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.  Stage-2 prime folder:
27 cards remaining.

## 2026-08-19 — prime-support flag-path Hodge cofactors (card 25)

New Lean modules (all `lake env lean` clean, wired into their umbrellas, axiom-clean):

- `HTGeometry/PathLaplacianRootedCofactor.lean` — the path incidence matrix, its root-normalized
  partial-sum potential (an explicit integral inverse of the root-reduced incidence matrix, so the
  reduced determinant is a unit of `ℤ`), the weighted Hodge Laplacian, **every rooted cofactor
  equals the product of the edge conductances**, the sum over roots, the Dirichlet energy identity,
  the constant radical, and the diagonal gauge that conjugates every twisted flag-path differential
  to the untwisted one (phase blindness of a chamber).
- `HTGeometry/CycleTwistedTorsion.lean` — the twisted cycle differential on `ZMod (n+1)`, the
  rigidity lemma that only the identity and the cyclic shift can contribute to the determinant,
  the torsion formula `det d_u = (-1)^{n+1} ∏w (Hol − 1)`, the Hodge determinant
  `∏ c · ‖1 − Hol‖²`, and the acyclicity criterion `det = 0 ↔ Hol = 1`.
- `RHTower/PrimeSupportFlagPathHodge.lean` — the marked deformation `M_n(t) = n(1−t)^{n−1}` as the
  sum of rooted cofactors, its order-`(n−1)` boundary derivative `n(−1)^{n−1}(n−1)!`, the positive
  prime monomial holonomy `exp(−i z log N_m)` with `N_m > 1` and its centred-critical-line
  localization, and the finite squarefree Euler product as source-apartment torsion together with
  its half-plane acyclicity.

Technique notes: the matrix-tree theorem is not needed — an explicit integer integrator gives the
unit determinant; `Fin n` has no `NatCast`/`CommRing` in this toolchain, so the cyclic index model
is `ZMod (n+1)` with the sign of the shift transferred from `sign_finRotate` through
`Equiv.Perm.sign_permCongr`; `(-1 : ℤˣ) ^ n` uses `Int.instUnitsPow`, which is defeq but not
syntactically the monoid power, so `Units.val_pow_eq_pow_val` must be applied by `exact`, not `rw`.

Card `prime-support-ht-horizon-hodge-cofactor-law` promoted to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`; its three remaining
unchecked gates are the open Quillen–Ward conjecture (14), explicitly not a proved theorem.
Stage-2 prime folder: 26 cards remaining.

## 2026-08-19 — prime–Laplace / Gamma-clock pair (cards 13, 14)

One new module closes both cards:
`RHTower/PrimeLaplaceGammaJetIncidence.lean` (`lake env lean` clean, wired into
`GaloisForLFunctions.RHTower`, axiom-clean).

Contents: the Gamma–Meixner weight `w_θ(p) = cosh(2 log p)^{-θ/2}` with its two-sided comparison to
`p^{-θ}`; the prime-supported Dirichlet coefficients and the sharp abscissa `(1-θ)/2` (AM–GM in
place of Cauchy–Schwarz); the raw jets as `LSeries` of the `(-log n)^j`-twisted coefficients;
Hilbert–Schmidt finiteness of every finite clock in the factorial metric; joint faithfulness (via
`analyticOrderAt = ⊤` ⇒ local vanishing ⇒ half-plane vanishing ⇒ Dirichlet uniqueness); the exact
coherent-jet Fock column norm `w_θ(p) p^{-2x₀} e^{(log p)²}` and its unboundedness (the colimit
no-go); the unit source translation `S a = p^{-1} a` with `F_{Sa}(z) = F_a(z+1)`; the Taylor descent
of shifted jets; the exact descent anomaly as the omitted factorial tail; the adjacent-resolution
Bianchi law; and the reflected time-one Euler seam vector with its translate identity.

Reusable inputs found by search: mathlib's `LSeries_iteratedDeriv`, `LSeries_analyticOnNhd`,
`LSeries_eventually_eq_zero_iff'`, `Complex.hasSum_taylorSeries_on_ball`, and the corpus lemma
`RHTower.summable_abs_log_natCast_pow_mul_rpow_neg`.

Cards `prime-laplace-gamma-jet-incidence-phase-transition` and
`prime-laplace-gamma-clock-descent-anomaly` promoted to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
Stage-2 prime folder: 24 cards remaining.

## 2026-08-19 — prime-square Fourier core landed (cards 22, 23 in progress)

`RHTower/PrimeSquareFourierStrata.lean` (`lake env lean` clean, wired into `GaloisForLFunctions.RHTower`,
axiom-clean) now carries the shared finite-Fourier interface both prime-square cards were waiting on:

- the `p` multiples of `p` in `ZMod (p^2)`, their cardinality, and the exact subgroup character sum
  `∑_{p ∣ x} e(kx) = p·[p ∣ k]` (proved from the geometric sum, no subgroup machinery);
- the strata indicators `1_U`, `1_M`, `δ₀`, their products and sums;
- the discrete Fourier transforms of all three (mathlib `ZMod.dft`), hence the unitary images
  `𝓕 1_U = p δ₀ − 1_M` and `𝓕 (1_M − δ₀) = 1_M − 1/p`;
- the four Fourier compression entries of the valuation plane
  (`0`, `−(p−1)`, `−(p−1)`, `(p−1)²/p`), i.e. the matrix `C_p` of the parent card;
- the deformed occupation line `q_{p,c}`, **the exact reflected-line coefficient**
  `α_p(c) = ((p−1)/p − (p^c + p^{−c}))/√((p+p^{2c})(p+p^{−2c}))`, the critical value
  `α_p(0) = −1/p`, the algebraic identity `N² − D² = p(p−1)x(x−2)`, and **the sharp criticality law
  `β_p(c) ≥ 1` with equality exactly at `c = 0`**.

Remaining for `prime-square-deformed-reflection-line-superessential-fracture`: the cofinal type
`log β_p(c)/log p → |c|` and its weighted Cesàro form `log B_x(c)/θ(x) → |c|`, plus the
Wold–Gamma scale comparison (needs Mertens `∏(1−1/p) ≍ 1/log x` and `θ(x) ~ x`, both in the corpus).

Remaining for `prime-square-mobius-fourier-complementary-record-law`: the eigen-decomposition and
leakage (its (8)–(11)), the involution `S_p` and the complementary amplitudes (17)–(21), the local
Möbius Fourier spectrum and Plancherel (23)–(26), the natural-cone Gram (29), CRT tensorization
(31)–(32), and the profinite tail-sector theorem (§6, which needs Haar measure on `Ẑ`,
independence, and Borel–Cantelli).

### 2026-08-19 (cont.) — deformed reflection type landed

`RHTower/PrimeSquareDeformedReflectionType.lean` (clean, wired, axiom-clean) adds the cofinal type
of the deformed card: the two-sided sandwich `p^c/4 ≤ β_p(c) ≤ 3 p^c`, the logarithmic type
`log β_p(c)/log p → |c|`, a reusable weighted Cesàro transfer over `Nat.primesBelow`
(`tendsto_weighted_prime_average`), the card's (12) `log B_N(c)/θ(N) → |c|`, and — via the corpus
PNT form `tendsto_sum_primesBelow_log_div` — the linear rate `log B_N(c)/N → |c|`, i.e. (17).

The only piece of `prime-square-deformed-reflection-line-superessential-fracture` still missing is
the §5 scale comparison (14)–(18): it needs `∏_{p<N}(1−1/p) ≍ 1/log N`, i.e. **Mertens' second
theorem in upper-bound form**.  The corpus already owns Mertens' first theorem
(`RHTower.mertens_first_prime`, `∑_{p≤N} log p/p = log N + O(1)`); the remaining step is Abel
summation from it.  Everything else in that card is formalized.

## 2026-08-19 — prime Fisher superspace blindness (card 10)

`RHTower/PrimeFisherSuperspaceBlindness.lean` (clean, wired, axiom-clean) completes the card on top
of the pre-existing `ProjectiveFisherBlindness.lean`: the concrete Dirichlet coherent state of a
completely multiplicative unimodular phase, its `ζ(2σ)` norm, its `n^{-2σ}/ζ(2σ)` Born law, Born
and Fisher blindness to the phases, the non-membership of the constant vector in `ℓ²`, the even
reality-symmetric quartet multiplier, and the two-dimensional conformal cancellation of the
massless Wheeler–DeWitt equation.

The decisive step no longer quotes the literature: the corpus's own formalization of Andersson's
Theorem 2 (`exists_continuable_phase_with_prescribed_multiplicities`) supplies a unimodular phase
whose Helson zeta continuation has a simple zero at any prescribed `0 < Re ρ < 1` while the
coherent state keeps exactly the untwisted Born and Fisher data.

Card `prime-fisher-superspace-unimodular-phase-blindness` promoted to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
Stage-2 prime folder: 23 cards remaining.

## 2026-08-19 — prime-square deformed reflection card CLOSED (card 22)

`RHTower/PrimeSquareSuperessentialScale.lean` supplies the last piece: the Wold boundary volume
`a_N = ∏_{p<N}(1−1/p)`, the polylogarithmic bound `1/a_N ≤ C (log N)²` (from `-log(1−1/p) ≤ 2/p`
and the corpus's **Mertens' second theorem** `tendsto_primeRecipSum_sub_logLog` — which does exist,
in `RHTower/MertensSecondPrimeRecipSum.lean`), the limit `(log N)²/N → 0`, and the superessential
separation `(1/a_N) / log B_N(c) → 0`.

Card `prime-square-deformed-reflection-line-superessential-fracture` promoted to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
Stage-2 prime folder: 22 cards remaining.

Note for the remaining analytic cards: Mertens' second theorem **with its constant** is available
(`RHTower.tendsto_primeRecipSum_sub_logLog`, `RHTower.mertensSecondConstant`), as is Mertens' first
(`RHTower.Mertens.mertens_first_prime`) and the PNT form `tendsto_sum_primesBelow_log_div`.

## Next steps (searched, not yet built)

Corpus search (`scripts/formal_tools.py research`) located these assets for the remaining cards, so
none of them should be rebuilt:

- PNT for `π` with the `exp(-c√log x)` error: `RHTower.Sieve.primeCounting_sub_logIntegral_isBigO`.
- Abel partial summation over prime windows: `RHTower.sum_primeWindow_eq_sub_sub_integral`,
  `RHTower.primeInvWindowSum_eq`, `RHTower.deningerAbelSummation`.
- Oscillatory integration by parts: `HTGeometry.norm_integral_oscillatory_le`,
  `PNTPlus.Fourier.norm_oscillatory_integral_le_integral_deriv_div`.
- Abelian limit of the prime zeta: `RHTower.tendsto_primeZeta_add_log_abelian`.
- Canonical Euler logarithm of zeta and its Dirichlet expansion:
  `RHTower.criticalPrimeTailEulerLogVerticalTrace_eq_canonicalEulerLogZeta`.
- Quantitative nonvanishing of `ζ` on the one line: `RHTower.Sieve.exists_pos_lower_bound_zeta_one_line`,
  `RHTower.Sieve.zetaResidueUnit_ne_zero_on_one_line`.

Planned order of work:
1. `∑_p (1 − cos(λ log p))/p = ∞` for `λ ≠ 0` by the cheap Abelian route (prime-zeta Abelian limit
   + `ζ(1+iλ) ≠ 0`), which is the input the Poisson-screen and superspace cards actually use.
2. Convergence of `∑_p p^{-1-iλ}` by Abel summation against
   `primeCounting_sub_logIntegral_isBigO` (needed for the sharp constants in the diagonal
   singular-trace and superspace cards).
3. `χ_N = ∑_{p≤N}(log p)²/p ∼ (log N)²/2` from Mertens' first theorem (superspace card §3).

### 2026-08-19 (cont.) — prime clock energy divergence landed

`RHTower/PrimeClockEnergyDivergence.lean` (clean, wired, axiom-clean):
`tendsto_primeClockEnergy_atTop` — for every nonzero frequency `τ`,
`∑_{p ≤ x} (1 − cos(τ log p))/p → ∞`.

Found entirely by corpus search: the deficit bound `RHTower.zetaLineDeficit_sub_le_primeClockEnergy`
(`RealTwistDeficitTransfer.lean`, resting on `abs_zeta_deficit_sub_primeClockEnergy_le` in
`ZetaOneLineDeficit.lean`) plus continuity and nonvanishing of `ζ` at `1 + iτ` give the divergence
in twenty lines; no prime number theorem or partial summation is needed.

This is the arithmetic input for the mutual singularity of distinct critical heights
(`prime-poisson-superselection-screen`, eqs. (8)–(9)) and for the clock decompactification
(`prime-superspace-wick-anisotropy-decompactification`, eq. (20) second half).

## 2026-08-19 — grade-monodromy inversion core (card 15, in progress)

`RHTower/GradeMonodromyInversion.lean` (clean, wired, axiom-clean) proves the card's exact
inversion law (5) in full generality: for a locally finite dilation datum `ν`,

`gradeMonodromyTransform ν n = -∑_r μ(r) ν(r n)/r`,
`gradeLambertTransform M n = -∑_k M(k n)/k`,
`gradeLambertTransform (gradeMonodromyTransform ν) n = ν n`,

with `sum_divisors_moebius_eq` (`∑_{d ∣ m} μ(d) = [m = 1]`) as the mechanism and mathlib's
`sigmaAntidiagonalEquivProd` for the pair regrouping.

Still to build for `prime-grade-monodromy-divisor-mobius-equivalence`:
(1) the Lambert decomposition `A(s) = ∑_k Q(ks)` on `Re s > 1` (corpus has the prime/higher-valuation
split `tsum_vonMangoldtLSeriesTerm_eq_primeLog_add_higherValuation` and the regrouping tool
`tsum_eq_tsum_primes_of_support_subset_prime_powers`); (2) the Möbius inversion `Q = ∑_r μ(r) A(r·)`;
(3)–(4) the residue law `Res_{s₀} Q = −∑_r μ(r) ν(r s₀)/r` from the continuation, using
`logDeriv_iteratedDeriv_residue_of_zero` (residue of a logarithmic derivative = analytic order);
(6) invariance under finite Euler-unit changes.

### 2026-08-19 (cont.) — Lambert decomposition landed; grade-monodromy analytic side already owned

`RHTower/GradeMonodromyInversion.lean` now also proves:

- `tsum_moebius_pair` — the general Möbius pair regrouping `∑_{(r,k)} μ(r) F(rk) = F(1)`;
- `primeGradeSource` and `summable_primeGradeSourceTerm`;
- `primeGradeFamily`, `summable_primeGradeFamily` (from the corpus two-scale bound
  `summable_primeLog_mul_inv_rpow_mul_add`);
- **`lSeries_vonMangoldt_eq_tsum_primeGradeSource`** — the card's Lambert decomposition (1),
  `A(s) = ∑_k Q((k+1)s)` on `Re s > 1`.

Corpus search then showed the card's analytic side (3)–(4) is largely **already formalized**:
`RHTower.xiPrimeLogDirichletContinuation` is the continued grade-one current on `Re s > 1/2`,
`xiPrimeLogDirichletCriticalContinuation_zero_residue` gives residue `−m` at critical-line zeros,
`neg_logDeriv_zeta_zero_residue` gives the residue of `−ζ'/ζ`, and
`xiPrimeLogHigherValuationCriticalContinuation_differentiableAt_zeta_zero` gives holomorphy of the
higher grades.  What remains for the card: the Möbius inversion (2) as a Dirichlet-series identity
(the summability estimate `|Q(ms)| ≤ C 2^{-(m-1)σ}` plus `tsum_moebius_pair`), the residue law (3)
in Möbius form, and the finite-Euler-unit invariance (6).

## 2026-08-19 — grade-monodromy card CLOSED (card 15)

`RHTower/GradeMonodromyInversion.lean` now carries the whole card: the Lambert decomposition (1),
the Möbius inversion (2), the residue law (3)–(4) (re-exported from the corpus's continued
prime-log current, with the new lemma that dilations `r ≥ 2` are holomorphic in the strip), the
exact mutual inversion (5) for an arbitrary locally finite datum, and finite Euler-unit invariance.

Card `prime-grade-monodromy-divisor-mobius-equivalence` promoted to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
Stage-2 prime folder: 21 cards remaining.

Search paid off again: `xiPrimeLogDirichletContinuation_zero_residue`
(`XiHeatCassiniWoldZetaPoleCarrier.lean`) already proved the card's (3)–(4) for every zero right of
the critical line, and `xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow` identified the corpus current
with the card's `Q`.

## 2026-08-19 — Krein–Hamming card CLOSED (card 16)

`HTGeometry/UniversalPrimeKreinHamming.lean` already carried the algebraic half (exact rectangular
inertia on canonical probes, Herglotz-iff-empty, rational-gauge same-field and Stanley–Reisner
matroid product, dephasing energy = Hamming). The missing analytic half is now
`HTGeometry/PrimeResiduePickInertia.lean`:

- `pickKernel`, its subtraction / real-scalar / finite-sum linearity;
- `pickKernel_cauchyAtom` — the one-atom rank-one identity for a real pole;
- `universalPrimeOrientedHerglotz_sub` — the ordered chamber pair differs by the finite signed
  divisor on `L \ J` and `J \ L` (the infinite common source cancels as an identity);
- `pickKernel_universalPrimeOrientedHerglotz_sub` — the relative Pick defect;
- `universalPrimeChamberRelativePickGram_eq` — sampling on the canonical unit-height probes gives
  literally the rectangular Krein form, so the corpus inertia theorems transport;
- `rectangularKreinForm_eq_featureCongruence` + `isUnit_universalPrimeChamberFeatureMatrix`
  ⇒ `isUnit_det_...` and `rank_... = primeChamberHammingDistance` (this is `κ₀ = 0`);
- `primeChamber_subset_iff_no_negative_pick_direction` — the analytic order law.

Technique note: the Pick kernel is only ℝ-linear in the function (conjugation on the second
argument), which is why the weights must be carried as real casts; `pickKernel_real_smul` is the
form that is actually usable.

Card `prime-residue-krein-hamming-product-law` promoted. Stage-2 prime folder: 20 cards remaining.

## 2026-08-19 — corona-opacity card CLOSED (card 17)

New module `HTGeometry/PrimeOrientationCoronaRank.lean` (all axiom-clean). It supplies the linear
(degree-one) rank layer that the corpus's Walsh machinery had only in the nonlinear
pattern-counting form:

- `differentialJet_signedPrimeShiftCarrier_mem_adjoin_of_tailCombination` — the reusable reduction:
  a sign column that agrees off a finite prime set with a ℂ-combination of other sign columns has
  all of its shifted jets inside the differential field generated by those columns. Rescale by
  `1 + ∑‖u_k‖` first: `boundedPrimeShiftCarrier` demands `‖column‖ ≤ 1`, and a linear combination
  of ±1 columns is not bounded by one.
- `exists_coronaBasis_index` — `exists_linearIndependent'` applied to the columns of the
  recurring-pattern sign matrix gives the corona basis; row/column rank equality
  (`Matrix.rank_transpose`) identifies its cardinality with `dim span(recurring sign vectors)`.
- `exists_corona_differentialBasis` — the card's formula (1) in basis form.
- `isClosed_anchoredSkeleton` — the skeleton is `{x | x anchor = false ∧ at most one true}`, an
  intersection of clopen cylinder conditions.
- `anchored_closedConstraint_opacity`, `anchored_opacity_interval_constant` — the opacity interval.

Reusable elsewhere: `orientationSignColumn`, `coronaRank`, `support_finite_of_vanishes_on_recurringPatterns`
(pattern-form annihilator law over an arbitrary infinite prime index), and the local
`IsScalarTower ℂ finitePrimeRationalCoefficientField arithmeticFunctionRationalCoordinateField`
instance — note it is `local` in `PrimeWalshDifferentialRank.lean`, so any new module in that lane
must re-declare it.

Card `prime-corona-constraint-opacity-law` promoted. Stage-2 prime folder: 19 cards remaining.

## 2026-08-19 — closability card CLOSED (card 18)

Two new modules:

`RHTower/PrimeCharacterTailIndependence.lean`
- `exists_prime_log_in_window` — prime logarithms are eventually δ-dense on the line, from
  `RHTower.Sieve.exists_threshold_routeT_prime_in_fixed_window` (the 71/100 Hoheisel window).
- `expSumOn`, `expSumLip`, `norm_expSumOn_sub_le` — Lipschitz bound for an exponential sum.
- `tendsto_expSumOn_atTop_zero_of_prime_log` — vanishing along prime logs ⇒ vanishing at infinity.
- `primeCharacter_coeff_eq_zero_of_eventually_vanishing` — **distinct prime characters `p^{-x}` are
  linearly independent modulo finite prime support**, for arbitrary complex exponents (no positivity
  needed). Reusable well beyond this card.

`RHTower/PrimeShiftResidueClosability.lean` — the residue graph, its domain, the functional, the
graph lemma, and `RiemannHypothesis ↔ IsClosableMarcinkiewicz residueDomain residueFunctional`.

Search notes (the user's standing instruction paid off three times here):
- `HTGeometry/ExpSumVanishing.lean` already had `eq_zero_of_expSum_tendsto_zero` — replaced ~110
  lines of a hand-rolled discrete Bohr mean.
- `RHTower/WeightedEulerCoefficientSpaces.lean` already had the card's actual spaces: `primeLogMass`,
  `marcinkiewiczLogQuotient`, `MemCriticalSummableLayer` (T₁), `MemMarcinkiewiczLogLayer` (M_log),
  `MemVanishingTailLayer` (M₀), `T₁ ⊆ M₀`, `primeLogMass_tail_anti`, and the Mertens corona
  exclusion `unitField_not_memVanishingTailLayer`. A first draft on an ad-hoc weighted-ℓ¹ seminorm
  was discarded and rebuilt on these, which is both faithful to the card and shorter.
- `HTGeometry/ZetaVerticalAlmostPeriodic.summable_log_pow_div_nat_rpow` gives the character
  summability immediately.

Card `prime-shift-residue-closability-criterion` promoted. Stage-2 prime folder: 18 cards remaining.

## 2026-08-19 — triage of the remaining 18 stage-2 prime cards

Read before choosing the next card.  Each entry names the genuinely missing mathematics, not the
bookkeeping.

**Reachable next (analytic input already in the corpus or newly built):**

1. `prime-power-dirichlet-complex-jet-independence` — the tail-span lemma is an exponential
   polynomial with *polynomial* coefficients vanishing along prime logs; the new
   `primeCharacter_coeff_eq_zero_of_eventually_vanishing` handles the pure-exponential case and the
   same two-layer induction (real part, then degree) extends it. Remaining: squarefree-coefficient
   extraction (elementary) and Chiang–Feng separation over Nagoshi's `F_s` — the corpus does have
   `HTGeometry/NevanlinnaEntireCharacteristic.lean`, `NevanlinnaCharacteristicLowerBound.lean`,
   `BorelGrowthLemma.lean`.
2. `prime-trace-critical-energy-divisor-budget` — needs (a) `∑_p log p · p^{-1-ε} = 1/ε + O(1)`
   (corpus `tendsto_LSeries_vonMangoldt_sub_pole`), (b) boundedness at `1+ε+iτ`, `τ ≠ 0`
   (corpus `zetaResidueUnit_ne_zero_on_one_line`), (c) Cauchy–Schwarz, (d) the local expansion of
   `P` from the divisor — the corpus's `RHTower/SelbergClass/` directory is the right home for the
   completed-Euler-product hypotheses.
3. `prime-square-mobius-fourier-complementary-record-law` §§1–5 — pure finite Fourier on
   `ZMod (p^2)`, already largely in `RHTower/PrimeSquareFourierStrata.lean`. Blocked only at §6:
   Möbius orthogonality to a fixed periodic sequence (needs PNT in APs) and the profinite
   Borel–Cantelli sector.

**Blocked on one shared analytic input** (`∑_p p^{-1-iλ}` convergence for `λ ≠ 0`):
`prime-diagonal-singular-trace-dephasing`, `prime-poisson-superselection-screen`,
`prime-superspace-wick-anisotropy-decompactification`.

**Large but self-contained builds:**
- `prime-boundary-symmetric-dickman-zero-free-law` — finite Wick core is done
  (`RHTower/PrimeBoundaryDickmanWick.lean`); needs the Poisson probability construction
  (mathlib has `poissonMeasure`, `mgf`, `iIndepFun.mgf_sum`, but not the Poisson mgf) and the
  scale-invariant Lévy limit.
- `prime-boundary-perturbative-jet-monodromy-escape` — the successor of the Dickman card.
- `prime-arch-bernstein-half-order-pringsheim-singularity` — exact finite-packet Puiseux
  decomposition; six formal parents exist.
- `prime-arch-explicit-circle-state-reflection-law`, `prime-arch-shifted-sector-circle-valuation-cone`
  — both list their formal reuse surface explicitly; the missing layer is an infinite absolutely
  summable Fourier-density wrapper plus the concrete `L²` reflection carrier.
- `prime-indexed-rvm-trace-class-hp-normal-form` — RVM two-term counting law plus a trace-class
  displacement estimate.
- `prime-tail-copoisson-essential-boundary-bockstein`, `prime-log-action-condensation-normal-cone-law`,
  `prime-sieve-boolean-first-trace-connection-curvature` (algebraic core already Lean-certified).

**Needs a mathematical layer the corpus does not have at all:**
- `prime-cyclotomic-coefficient-field-escape` — Mahler/Sibuya–Sperber coefficient recurrence and
  its normalization to an eventual forward recurrence.
- `prime-quasi-inner-dixmier-residue` — the weak trace ideal `L^{1,∞}`, Dixmier traces, Connes
  measurability.
- `prime-exponential-holomorphic-determining-source-image` — analytic functionals and
  Fréchet holomorphy on `O(D)` (Fourier–Borel duality).

## 2026-08-19 — trace-energy card CLOSED (card 19)

`RHTower/PrimeTraceCriticalEnergyBudget.lean` (626 lines, axiom-clean). The chain:

1. `tendsto_primeGradeSource_sub_pole` / `tendsto_primeGradeSource_shift` — the grade-one prime
   current has residue 1 at `s = 1` and a finite limit at `1 + iτ`, `τ ≠ 0`. Both are read off
   `xiPrimeLogDirichletContinuation = infinitePrimeFlux − xiPrimeLogHigherValuation`, so the higher
   prime powers never need a separate estimate.
2. `divisorTestEnergy_eq` — the test energy is the ordinate-pair sum of the current;
   `tendsto_mul_divisorTestEnergy` — its residue is `∑ m_j²` (only the diagonal survives, by
   injectivity of the ordinates).
3. `norm_primeDivisorCurrent_sq_le` — Cauchy–Schwarz with the split
   `f = |c| √(log p) p^{-(a+ε/2)}`, `g = √(log p) p^{-(1/2+ε/2)} |phase|`, using the corpus's
   `deningerTsum_mul_le_sqrt`.
4. `primeTraceCriticalEnergyBudget(_extended)` — the budget, with the divergent-energy case handled
   in `ℝ≥0∞`.

Technique note: `HTGeometry.cis` (from `ExpSumVanishing`) is the right normal form for the
unimodular factors — `natCast_cpow_neg_split` turns `p^{-(σ+iτ)}` into
`(p^{-σ} : ℝ) * cis (-τ) (log p)` once and for all, which is what makes the pair expansion and the
Cauchy–Schwarz split routine.

Card `prime-trace-critical-energy-divisor-budget` promoted. Stage-2 prime folder: 17 cards remaining.

## 2026-08-20 — dephasing card CLOSED (card 20), and the prime-zeta one-line asset

Three new modules:

`RHTower/PrimeDiagonalSingularValues.lean` — `primeDiagonalSum` (the sum over the first `N` primes)
identified with the corpus's `primeRecipSum` at `p_N` through a `Nat.nth` bijection; then
`n/p_n → 0`, `S_N/log N → 0`, `S_N/log log N → 1` from `PNTPlus.nth_prime_asymp`,
`log_nth_prime_asymp` and `tendsto_primeRecipSum_sub_logLog`.

`RHTower/OscillatoryLogIntegral.lean` — **new reusable analytic asset**:
`exists_tendsto_integral_oscLogKernel`, the convergence of `∫_2^∞ t^{-1-iλ}/log t dt` for `λ ≠ 0`,
by integration by parts against the phase; plus `integrableOn_logTailWeight`
(`∫_2^∞ dt/(t log²t) < ∞`) and `integrableOn_pntErrorWeight`
(`∫_2^∞ e^{-c√log t}/t dt < ∞`, via `e^{-c√u} ≤ 24/(c⁴u²)`).

`RHTower/PrimeZetaOneLineConvergence.lean` — **`∑_p p^{-1-iλ}` converges for every `λ ≠ 0`**
(`exists_tendsto_primeCpowSum`). Method: mathlib's `sum_mul_eq_sub_integral_mul₁` against the
Chebyshev `theta` datum (NOT against `π`), so the main term is the smooth `t` rather than the
logarithmic integral; `theta(t) = t + R(t)` with `RHTower.Sieve.chebyshevTheta_sub_id_isBigO`, the
main integral reduces to the oscillatory logarithmic integral plus an absolutely convergent tail,
and the error is dominated by `e^{-c√log t}/t`. The local integrability of the error uses mathlib's
`locallyIntegrableOn_mul_sum_Icc` from the same Abel-summation file.

This closes the shared blocker recorded in the earlier triage. `prime-poisson-superselection-screen`
and `prime-superspace-wick-anisotropy-decompactification` were listed as blocked on the same input;
check them next against `exists_tendsto_primeCpowSum`.

Card `prime-diagonal-singular-trace-dephasing` promoted. Stage-2 prime folder: 16 cards remaining.

## 2026-08-20 — superspace card CLOSED (card 21)

`RHTower/PrimeSuperspaceDecompactification.lean` (524 lines, axiom-clean). What made it cheap:

- the corpus already had the Mertens weak limit `tendsto_mertensPrimeWindow_div_log`
  (`RHTower/MertensPrimeWindowWeakConvergence.lean`) — equation (8) of the card — so the profile
  limits (9)–(10) are one `congr'` away once the test functions are shown continuous at the
  removable singularity (use `hasDerivAt_iff_tendsto_slope` at `0`, not a series estimate);
- `tendsto_primeClockSusceptibility_div_log_sq` (equation (5)) was already there;
- recurrence (13) is `HTGeometry.primeBooleanFusion_exists_large_return` plus
  `‖e^{iθ}−1‖² = 2(1−cos θ)`;
- the boundary sum (16) is the new `exists_tendsto_primePhaseSum`.

New here: `wickProfile` with `hasSum_wickProfile` (the `∑ z^{2k}/(k(2k)!)` series, via
`intervalIntegral.hasSum_integral_of_dominated_convergence`), `wickProfile_mul_I` (the Wick
relation from `Complex.cosh_mul_I`), the exact decomposition
`primeClockVerticalEnergy_eq_recipSum_sub`, and the sharp law / overlap / decompactification
theorems.

Card `prime-superspace-wick-anisotropy-decompactification` promoted. Stage-2 prime folder:
15 cards remaining.

## 2026-08-20 — updated triage of the remaining 15 cards

New assets available to all of them:
`exists_tendsto_primeCpowSum` (∑_p p^{-1-iλ} converges), `exists_tendsto_integral_oscLogKernel`,
`integrableOn_logTailWeight` / `integrableOn_pntErrorWeight`, `wickProfile` + `hasSum_wickProfile`,
`radialProfileTest` / `verticalProfileTest` with their Mertens-window limits,
`primeCharacter_coeff_eq_zero_of_eventually_vanishing`, `coronaRank`, `pickKernel`.

**Closest to done:**
1. `prime-boundary-symmetric-dickman-zero-free-law` — §§3–5 are now immediate:
   the Lévy limit (10) is `tendsto_mertensPrimeWindow_div_log` applied to `u ↦ f u / u`; the
   profiles (14)–(15) are `radialProfileTest`/`verticalProfileTest`; the cumulant tower (17)–(18)
   is `hasSum_wickProfile`; (16) as characteristic-function convergence is
   `primeBoundaryCharacteristic_eq_exp_neg_verticalEnergy` + `tendsto_primeClockVerticalEnergy_scaled`;
   (19)–(20) follow. **The only genuinely missing piece is the probability model (§1–§2, (5)–(6)):**
   mathlib has `poissonMeasure`, `integral_poissonMeasure` (no integrability side condition),
   `iIndepFun_pi` and `iIndepFun.mgf_sum`, but NOT the Poisson mgf `E e^{tK} = e^{r(e^t-1)}`;
   that is ~60 lines from `integral_poissonMeasure` plus the exponential series.
2. `prime-sieve-boolean-first-trace-connection-curvature` — (4), (7)–(9) are already Lean-certified;
   (6) is an elementary sieve telescope (`∑ a_{P_{n-1}}/p_n = 1`, needs `a_{P_n} → 0`, i.e. Mertens
   third, corpus `tendsto_mertensPrimeProduct_mul_log`); (10) is a Boolean evaluation.
   **Blocker: (5), the projective tensor norm `‖D_P‖_π = 1`** — mathlib only has
   `Analysis.NormedSpace.PiTensorProduct.ProjectiveSeminorm`.
3. `prime-power-dirichlet-complex-jet-independence` — the tail-span lemma is the polynomial-coefficient
   version of `primeCharacter_coeff_eq_zero_of_eventually_vanishing`; the same two-layer induction
   (real part, then polynomial degree) extends it. Blocker: Chiang–Feng separation over Nagoshi's
   `F_s` (the corpus does have `NevanlinnaEntireCharacteristic`, `NevanlinnaCharacteristicLowerBound`,
   `BorelGrowthLemma`).

**Still needing a mathematical layer the corpus lacks entirely:**
`prime-cyclotomic-coefficient-field-escape` (Mahler/Sibuya–Sperber recurrence),
`prime-quasi-inner-dixmier-residue` (Dixmier traces on `L^{1,∞}`),
`prime-exponential-holomorphic-determining-source-image` (analytic functionals, Fourier–Borel),
`prime-poisson-superselection-screen` (Kakutani dichotomy for infinite product measures on the
prime torus).

**Large but self-contained:** the three `prime-arch-*` cards (they list their reuse surfaces),
`prime-boundary-perturbative-jet-monodromy-escape`, `prime-indexed-rvm-trace-class-hp-normal-form`,
`prime-tail-copoisson-essential-boundary-bockstein`,
`prime-log-action-condensation-normal-cone-law`,
`prime-square-mobius-fourier-complementary-record-law` (§§1–5 nearly free from
`RHTower/PrimeSquareFourierStrata.lean`; §6 needs Möbius orthogonality to a fixed periodic sequence
and a profinite Borel–Cantelli sector).

## 2026-08-20 — card 8 promoted; roadmap for `prime-boundary-perturbative-jet-monodromy-escape`

`prime-boundary-symmetric-dickman-zero-free-law` is at stage 3 (see its own dated section).  New
module: `RHTower/PrimeBoundaryPoissonJumpField.lean`.

The successor card is a six-module project; module 1 is written and awaiting the corpus rebuild:

1. **`RHTower/PrimeHigherMertens.lean` (written).**  The higher-order Mertens theorem
   `∑_{p ≤ x}(log p)^k/p - (log x)^k/k → C_k` for every `k ≥ 1`, by Abel summation of the corpus
   `primeLogWeight` against `Chebyshev.theta`, splitting `θ(t) = t(1 + thetaError t)`, with the
   error integral controlled by the new device
   `exp_neg_sqrt_le_pow : exp(-c√u) ≤ (2m)!/(c^{2m} u^m)` and
   `integrableOn_logPow_pntErrorWeight : (log t)^m e^{-c√log t}/t ∈ L¹(2,∞)`.
   Also gives the card's `D_N(u^k)` form `(10)` as
   `tendsto_logPow_mul_primeLevyDefect_pow`.
2. **Rate form.**  `|A_k(x) - (log x)^k/k - C_k| = O((log x)^k e^{-(c/2)√log x})`, via the tail
   estimate `∫_{Ioi x} (log t)^m e^{-c√log t}/t ≤ e^{-(c/2)√log x} ∫_{Ioi 2} (log t)^m e^{-(c/2)√log t}/t`
   (split the exponential in half).  This is `(9)`, and gives `(10)` with its error term.
3. **The endpoint jet `(6)`--`(7)`.**  Abel weight `f(t) = r(log t/log x)/(t log t)`; integrate by
   parts to produce `∫_{log2/L}^1 r(u) du/u` as the main term; bound the four boundary terms and
   the `thetaError` integral by `O(L^{-M-1})` using module 1's devices.  Then Taylor
   (`taylor_mean_remainder_lagrange`) gives the jet expansion.  Stated for `r` differentiable on
   `(0,1]` with `|r| ≤ A u^{M+1}`, `|r'| ≤ A u^M` — the exact hypotheses the proof uses, and what
   the Taylor remainder of a `C^{M+1}` test function satisfies.
4. **The Wick expansion `(15)`--`(20)`.**
5. **Prime zeta continuation, germ `(4)`--`(5)`, monodromy `(21)`--`(22)`, escape `(24)`.**
6. **`(26)`--`(27)`: the archimedean weld, the Hurwitz obstruction, the RH restatement.**

Two other cards were triaged in passing: `prime-log-action-condensation-normal-cone-law` and
`prime-square-mobius-fourier-complementary-record-law` each have all their *theorem* gates proved
and only research gates (ending in RH) open, so stage 3 for them means formalizing the proved
gates only.

### 2026-08-20 (later) — jet card: modules 1–3 of 6 landed

Five new axiom-clean modules, all wired into `RHTower.lean`:

| module | content | card items |
|-|-|-|
| `RHTower/PrimeHigherMertens.lean` | `∑_{p≤x}(log p)^k/p - (log x)^k/k → C_k`; the devices `exp_neg_sqrt_le_pow`, `integrableOn_logPow_pntErrorWeight`, the Abel weight `(log t)^m/t` and its primitive | `(5)`, `(8)` |
| `RHTower/PrimeHigherMertensRate.lean` | the same with the de la Vallée Poussin rate; `exists_pntErrorEnvelope`; the half-exponential tail bound; the monomial defect `|D_x(u^{k}) - C_k/L^k| = O(L^{-M-1})` | `(9)`, `(10)` |
| `RHTower/PrimeEndpointJet.lean` | `primeBoundaryDefect`, its exact Abel decomposition, and the master remainder estimate `|D_x(r)| ≤ A·B/L^{M+1}` | `(13)`, `(14)` |
| `RHTower/PrimeEndpointJetExpansion.lean` | linearity of the defect and the jet expansion for "polynomial + remainder" test functions | `(6)`, `(7)` |
| `RHTower/PrimeEndpointJetTaylor.lean` | iterated integration, `jetTaylor`, the Taylor remainder bound, and `(6)` for any smooth test function vanishing at the endpoint | `(6)`, `(11)` |

Remaining for `prime-boundary-perturbative-jet-monodromy-escape`:

* §3 `(15)`--`(19)`: apply the jet theorem to `h_z(u) = 2(cosh(zu) - 1)`, giving the symmetric Wick
  expansion `K_N^bdry(z) = Φ(z) + ∑ 2α_{2m} z^{2m}/((2m)! L^{2m}) + O(L^{-2M-2})`, and the
  beyond-all-orders statement for test functions supported in `[δ,1]`.
* §4 `(20)`: finite truncations are zero-free (elementary, from `Complex.exp_ne_zero`).
* §5 `(21)`--`(25)`: prime zeta continuation `P(s) = ∑ μ(n)/n log ζ(ns)`, its logarithmic branch
  points, the monodromy charge `m_ρ`, and the escape `|L(ρ-1)| → ∞`.
* §6 `(26)`: the archimedean factor is holomorphic and zero-free on the strip, hence has zero
  monodromy.
* §7 `(27)`: RH as the support statement for prime-zeta monodromy, plus the two Hurwitz-type
  obstructions.

Note on faithfulness: the Lean form of `(6)` takes a derivative tower on `ℝ` (the honest Lean
rendering of `C^{M+1}`), and the remainder estimate takes the two bounds `|r| ≤ A u^{M+1}`,
`|r'| ≤ A u^M` on `(0,1]` — exactly what the proof uses and what the Taylor module supplies.

### 2026-08-20 (later still) — jet card §§3–7

Two more modules landed: `RHTower/PrimeBoundaryWickExpansion.lean` (the two-axis Wick expansion
`(17)`, the leading correction `(18)`, the beyond-all-orders statement `(19)` and the zero-freeness
of truncations `(20)`) and `RHTower/PrimeBoundaryMonodromyEscape.lean` (§5–§7).

**Corpus-search payoff.**  §5 of the card — the prime zeta continuation and its quantized
monodromy — was already formalized in the corpus, in the very module this session closed for the
first prime card:

* `RHTower/GradeMonodromyInversion.lean`: `primeGradeSource` (= `∑_p (log p) p^{-s}` = `-P'`),
  the Lambert decomposition, the Möbius inversion `primeGradeSource_eq_tsum_moebius_lSeries`
  (the derivative form of `P(s) = ∑ μ(n)/n log ζ(ns)`), `primeGradeMonodromy_zero_residue`
  (residue `-m_ρ` at every strip zero) and `differentiableAt_lSeries_vonMangoldt_dilate` (the
  higher grades are regular there);
* `RHTower/XiHeatCassiniWoldZetaPoleCarrier.lean`: `xiPrimeLogDirichletContinuation` and its
  residue theorem;
* `RHTower/ReflectionCocycleClass.lean`: `riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip`;
* `HTGeometry/ZeroDivisorCount.lean` and `HTGeometry/LogDerivUniformLimit.lean`: the argument
  principle and the convergence of contour integrals of logarithmic derivatives, which give the
  card's two zero-charge obstructions.

So §5–§7 became a thin wrapper instead of a 700-line project.  Search first.

## 2026-08-20 — card 9 promoted: `prime-boundary-perturbative-jet-monodromy-escape`

Stage 3.  Eight new modules (`PrimeHigherMertens`, `PrimeHigherMertensRate`, `PrimeEndpointJet`,
`PrimeEndpointJetExpansion`, `PrimeEndpointJetTaylor`, `PrimeBoundaryWickExpansion`,
`PrimeBoundaryMonodromyEscape`, plus `PrimeBoundaryPoissonJumpField` from the previous card), all
axiom-clean and wired.  Remaining stage-2 prime cards: 13.

### Working-mode corrections adopted mid-card

* **No full builds.**  `lake build <module>` in this project rebuilds the whole library and blocks
  `lake env lean` on the build lock for hours while other agents commit.  Replaced by:
  * scratch checking with `LEAN_PATH=<project + package olean dirs> lean <file>`;
  * `/tmp/scr/build_needed.py <file>`, which walks the transitive project imports of a scratch file
    and compiles *only* the missing oleans with `lean -o`;
  * `lean -o .lake/build/lib/lean/<Module path>.olean <source>` to publish one finished module.
  Umbrella wiring is still done (append the import) but never built as a whole.
* **Search the corpus before writing.**  Two near-duplications were caught this way; one was
  written before the check and deleted (`CentralBinomialGeneratingFunction`, superseded by
  `HTGeometry/CentralBinomialSeries.hasSum_centralBinom`).

### Bernstein card: what the corpus already owns

Checked with `scripts/formal_tools.py research` before writing anything:

* `HTGeometry/CentralBinomialSeries.lean` — `hasSum_centralBinom`, the analytic
  `∑ C(2n,n) x^n = (1-4x)^{-1/2}`;
* `HTGeometry/CentralBinomialDiagonalKernel.lean` —
  `hasSum_centralBinomialDiagonalKernelCoefficient`, i.e. the card's `(15)`
  `K(t;u,ū) = ((1-B²t)(1-B₋(u)²t))^{-1/2}`, and its positive-branch form;
* `HTGeometry/CentralBinomialConvolutionAsymptotic.lean` —
  `tendsto_sqrtNat_mul_centralBinomialDiagonalKernelCoefficient_div_pow`, the card's `(7)`;
* `HTGeometry/BernsteinRowDiagonalKernel.lean` and
  `RHTower/BernsteinAffineRowDiagonalAsymptotic.lean` — the row-square identity for one complex
  affine Bernstein row;
* `RHTower/BernsteinLegendreDoubleSourceKernel.lean` — the Legendre row identity and the bivariate
  moment functional;
* `RHTower/BernsteinEllipseRigidity.lean` — the distinct maximizing phases behind `(16)`.

So `prime-arch-bernstein-half-order-pringsheim-singularity` needs only the finite-packet assembly:
the maximal-coordinate grouping `(11)`, the `O(β^n)` non-maximal tail `(12)`, the pair expansion
`(14)`, the strict gap `(16)` for mixed-maximal pairs, and the resulting decomposition `(4)`--`(6)`
with the half-order radial law `(9)`.

### Bernstein card: precise remaining work (2026-08-20)

Already in the corpus (verified with the research tool):

* `(7)` the sharp coefficient asymptotic — `exists_positive_halfOrder_primeArchEndpointBernsteinPurity_of_not_rh`;
* `(9)` the half-order radial law — `exists_positive_halfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh`;
* `(4)` in real-variable form — `exists_exact_maximalDiagonalSquareRootDecomposition_of_not_rh`
  (exact finite diagonal square-root kernel plus a remainder that vanishes after multiplication by
  the boundary square root);
* `(15)` the diagonal kernel — `hasSum_centralBinomialDiagonalKernelCoefficient`;
* ellipse rigidity — `eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq`.

Missing for a faithful `(4)`: the *holomorphy* of the remainder past `R_A`.  Route:

1. `(21)`: for distinct maximal coordinates `u ≠ v`, `max_{|w|=1} |(1-u+uw)(1-v̄+v̄w⁻¹)| < B²`.
   Ellipse rigidity gives distinct alignment phases (the reflected complement `1 - conj u` is
   excluded by the quarter-disk bound); compactness of the circle turns that into a strict maximum.
2. The remainder coefficients are `O(γ^n)` with `γ = max(β², Bβ, mixed-maximal gap) < B²`, using the
   corpus complement-packet bounds and `(21)`.
3. Hence the remainder Abel susceptibility is a power series of radius `≥ 1/γ > R_A`, so it is
   holomorphic on a neighbourhood of `R_A`; `A(t) = ∑_u |C_u|²/√(1-B₋(u)²t)` is holomorphic there
   because `|B₋(u)| < B`.  That is `(4)`--`(6)`.

## 2026-08-20 — card 10 promoted: `prime-arch-bernstein-half-order-pringsheim-singularity`

Stage 3.  One new module, `RHTower/PrimeArchBernsteinBranchDecomposition.lean`:

* `abs_finiteBernsteinCoordinatePacketEnergy_sub_diagonal_le` — the polarized packet energy minus
  its diagonal is bounded by `(∑‖C‖)² γ^n` whenever every mixed cross moment is `≤ γ^n`;
* `exists_uniform_mixedCrossMoment_gap` — one rate `γ < B²` works for the whole finite maximal
  packet (finite `sup'` over the mixed pairs of the corpus per-pair gaps);
* `exists_remainder_exponential_bound` — the diagonal remainder is `≤ K γ^n` with
  `γ = max(mixed gap, Bβ, β²) < B²`, combining the above with the corpus `l1` packet bounds and
  the energy perturbation inequality;
* `summable_remainder_of_lt_inv_gamma` and `exists_branchDecomposition_of_not_rh` — the remainder
  Abel series converges on `|t| < 1/γ ⊋ [0, R_A]`, so the branch decomposition `(4)`--`(6)` holds
  with a remainder holomorphic across the critical radius.

Remaining stage-2 prime cards: 12.

## 2026-08-20 — card 11 promoted: `prime-log-action-condensation-normal-cone-law`

Stage 3.  One new module, `RHTower/PrimeLogActionCondensation.lean`, containing the card's whole
analytic layer: the depth carriers and their increment, the exact squarefree action expansion
(from the corpus reciprocal-zeta Dirichlet series), the asymptotic-deflation extraction theorem
with its elementary ratio-tail estimates, the diagonal blow-up identities, the condensation limits,
the universal normal-cone law for any nonvanishing germ, its completed-`ξ` specialization, and the
divisor residue `-dρ`.

Remaining stage-2 prime cards: 11.
