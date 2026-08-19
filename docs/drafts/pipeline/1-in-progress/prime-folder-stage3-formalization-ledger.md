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
