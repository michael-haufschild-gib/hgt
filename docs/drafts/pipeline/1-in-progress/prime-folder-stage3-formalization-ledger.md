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
