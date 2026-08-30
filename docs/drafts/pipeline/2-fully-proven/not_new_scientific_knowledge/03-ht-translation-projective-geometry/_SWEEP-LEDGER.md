# Stage-3 sweep ledger — 03-ht-translation-projective-geometry

Goal: formalize every proven theorem of each card unconditionally in Lean 4, then promote the
card to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/03-ht-translation-projective-geometry/`.

Already promoted (before this sweep): `ht-remote-quartet-compact-open-field-invisibility`,
`hypertranscendental-caustic-divisor-pole-cone`, `jetwise-dense-single-ht-profield-class`.

| # | Card | State | Blocking mathematics |
|---|---|---|---|
| 1 | combination-mode-reducibility-baker-bridge | OPEN | Baker–Wüstholz effective bound; Dirichlet pigeonhole no-go; Hankel support-≤d lemma |
| 2 | da-ht-topological-interlacing-law | **PROMOTED 2026-08-29** | — (Runge's theorem built from scratch) |
| 3 | ht-c28-minimal-handle-collapse | **PROMOTED 2026-08-29** | — (Weierstrass replaced by a one-derivative argument; class (II)/(III) are bibliographic) |
| 4 | ht-da-translation-spectrum-countability | **PROMOTED 2026-08-29** | — |
| 5 | ht-exact-da-translation-stabilizer | **PROMOTED 2026-08-29** | — (Ostrowski replaced by eventual-gap hypertranscendence) |
| 6 | ht-q-residue-spectrum-classification | **PROMOTED 2026-08-29** | — (ADH replaced by the corpus's exact Ostrowski criterion; Chen–Singer built) |
| 7 | hypertranscendental-maximal-finite-horizon-galois-law | OPEN | binomial degree + S_D normal closure transport |
| 8 | indeterminate-moment-fiber-prevalent-translation-ht | OPEN | prevalence, product probe, parametric transversality |
| 9 | laguerre-polya-jensen-profield-blindness | **PROMOTED 2026-08-29** | — (both directions of Jensen's theorem built from the Laguerre shift) |
| 10 | poincare-constraint-order-recession | OPEN | unit-cost cascade ord_DA(f^[n]) = n; affine invariance; Bergweiler |
| 11 | projective-horizon-hankel-secant-stratification | OPEN | catalecticant/secant identification, codimension 2k-1, Sing(C_k)=C_{k+1} |
| 12 | projective-ht-generic-pv-curvature-core | OPEN | Wilczynski normalization; Picard–Vessiot SL_N; invariant field |
| 13 | random-holomorphic-maximal-translation-ht-law | **PROMOTED 2026-08-29** | — (two models built, incl. the planar Gaussian) |

## Shared infrastructure built
- `HTGeometry/DomainJetRelationLocus.lean` — the (n,d) jet-minor certificate for
  `DifferentiallyAlgebraicOn f Ω` on an arbitrary open preconnected `Ω` (generalizes
  `EntireFamilyDifferentialAlgebraicLocus`).  **Reusable by every other card in this folder.**
- `HTGeometry/DomainTranslationSlopeMinor.lean` — normalized translation-defect minors on a domain,
  antiderivative closure `differentiallyAlgebraicOn_of_deriv`, uniform branch.
- `HTGeometry/DifferentialAlgebraicOnSum.lean` — constants, binary and finite sums, scalar
  multiples for `DifferentiallyAlgebraicOn` on a domain.
- `HTGeometry/StencilJetExpansion.lean` — local affine chain rule `iteratedDeriv_comp_affine_on`,
  `iteratedDeriv_iteratedDeriv`, stencil moments, `dslopeIterZero` k-fold removable division.
- `HTGeometry/MeromorphicTranslationDefectCountability.lean` — `not_countable_univ_complex`,
  `nonempty_compl_of_countable`, `infinite_compl_of_countable`,
  `isPreconnected_compl_of_countable` (all reusable).

## Known corpus assets located during the sweep (do not rebuild)
- Hölder's theorem is owned: `HTGeometry.WatsonFlatnessDischarge.quantitativeHolder`,
  `hypertranscendental_reciprocalGammaEntire`, and the whole Gamma-HT stack.
- `Bottcher.analyticOnNhd_zeros_countable` — countable zero set on a preconnected open set.
- `HTGeometry.ConvexDiffCountableConnected.isPreconnected_diff_of_countable_of_convex_complex`.
- `HTGeometry.ReflectedDividedDifference.iterate_dslope_self_eq_iteratedDeriv_div_factorial`
  (namespace `HTGeometry`, not `GaloisForLFunctions.HTGeometry`).
- `HTGeometry.DifferentialAlgebraicOnClosure` — `meroField U` differential-field bridge on an
  arbitrary open preconnected nonempty infinite domain; the letI instance stack to copy.
- `HTGeometry.UpperEndPrimeLogJets.analyticOnNhd_iteratedDeriv` — do not redefine this name.
- **NOT in mathlib and not in the corpus:** Runge's theorem / rational approximation with poles off
  a domain (needed by `da-ht-topological-interlacing-law`); the corpus only owns the half-plane
  one-generator case `HTGeometry.HalfPlaneRungeClosure`.

## Log
- 2026-08-29 — ledger opened; all 13 cards read; corpus survey started.
- 2026-08-29 — card 4 `ht-da-translation-spectrum-countability` fully formalized and promoted to
  stage 3: meromorphic (closed-countable-singular-set) countability, bounded-complexity
  accumulation, complexity escape, multiplicative corollary, and the finite-stencil extension in
  both directions.  Eight new Lean modules, all axiom-clean.

## Card 2 progress (2026-08-29)

Lean-closed so far:
- `HTGeometry/HolomorphicCompactOpenDomain.lean` — `HoloCO Ω` (holomorphic functions on an open
  `Ω ⊆ ℂ` as a closed complex subspace of `C(↥Ω, ℂ)`), complete/completely metrizable/Baire,
  `ContinuousAdd`/`ContinuousSMul`, and continuity of every fixed jet
  (`continuous_holoCOJet`).
- `HTGeometry/DifferentialAlgebraicCompactOpenMeagre.lean` — the bounded-complexity strata
  `daCompactOpenStratum`, their closedness, `daCompactOpenLocus_eq_iUnion`, and the **empty
  interior** theorem via the explicit geometric jet configuration
  `v (i,c) = a i ^ ((d+1)^(c+1))`, whose jet-sample matrix is a Vandermonde matrix after the
  base-`(d+1)` digit bijection `finFunctionFinEquiv`.  Consequences: `isMeagre_daCompactOpenLocus`,
  `isGδ_htCompactOpenLocus`, `dense_htCompactOpenLocus`, and the abstract selector-collapse laws.
- `HTGeometry/HardyDifferentialAlgebraicInterlacing.lean` — the full Hardy half:
  `dense_hardyDALocus` (polynomial truncations of `lp` sequences),
  `memℓp_diskCoeff_reciprocalGammaEntire` and the bounded hypertranscendental carrier
  `hardyHTCarrier`, `dense_compl_hardyDALocus` (at most one exceptional scalar per point), and
  `hardy_phase_selector_collapse`.

**Remaining for card 2: Runge's theorem.**  `DA(Ω)` dense in the compact-open topology needs
"rational functions with poles off `Ω` are dense in `O(Ω)`", which is in neither mathlib nor the
corpus (the corpus only owns the half-plane one-generator case).  Planned build:
1. Cauchy integral formula on a rectangle (from mathlib's rectangle Cauchy theorem plus the
   winding number of a rectangle boundary);
2. the grid/edge-cancellation contour `Γ ⊆ Ω ∖ K` with `g = (2πi)⁻¹ ∮_Γ g(w)/(w−z) dw` on `K`;
3. Riemann-sum approximation giving rational functions with poles on `Γ`;
4. pole pushing along chains in `ℂ ∖ K`, and the `Ω`-hull reduction making every bounded
   component of `ℂ ∖ K` meet `ℂ ∖ Ω`.

## Corpus survey for the remaining cards' deep inputs (2026-08-29)

Findings that change the effort estimates:

- **Rectangle contour calculus is owned.**  `HTGeometry/RectangleResidue.lean` (namespace `RHTower`)
  has `rectIntegral`, `rectangle_winding`, `rectIntegral_cauchyKernel` (`= 2πi` for a strict
  interior point), `rectIntegral_eq_zero_of_analyticOnNhd`, `rectIntegral_add`,
  `rectIntegral_const_mul`, `rectIntegral_congr`, `rectIntegral_finsetSum`; and
  `RHTower/RectangleLocalCauchyFormula.lean` has the local Cauchy formula on a rectangle.
  **Step 1 of the Runge build is therefore already done.**
- **Picard–Vessiot exists but only for difference systems**: `DifferenceSystemPicardVessiot`,
  `ParameterizedPicardVessiotExistence`, `DifferencePicardVessiotConstants`.  Card 12 needs the
  *differential* PV theory with group `SL_N`, which is not present.
- **A large superlacunary-hypertranscendence stack exists**: `FormalHypertranscendence.aeval_survives`
  (formal HT of a gap series, with `(r,W)`-dependent global gap hypotheses),
  `TaylorFormalBridge.hypertranscendental_of_aeval_survives`,
  `LogSuperlacunaryMagnitudeHypertranscendence.hypertranscendental_of_eventually_logSuperlacunary`,
  `MagnitudeIntegerDominance`, `BalancedCoefficient.gap_series_no_polynomial_relation`,
  `hypertranscendental_add_polynomial_iff`.
  This is the natural substitute for **Ostrowski** in card 5: the card's carrier
  `F(z) = Σ c_k e^{2πi n_k z}` is `G(e^{2πi z})` for the entire gap series `G(w) = Σ c_k w^{n_k}`,
  so coefficient algebraic independence can be replaced by a frequency-side superlacunarity
  hypothesis.  **Open sub-problem:** `aeval_survives` needs the gap inequality
  `∀k, r·b_k + 2W < b_{k+1}` globally in `k`, while an arbitrary relation has unbounded `(r,W)`;
  truncating the prefix by a polynomial changes `W`, so an *eventual*-gap version of
  `aeval_survives` (or a prefix-tolerant probe) is the missing piece.
- **Effective Baker–Wüstholz is NOT owned** (only qualitative/general Baker), so card 1's Lemma R(ii)
  stays blocked on the `effective-baker-matveev-project`.
- **Full symmetric horizon monodromy is conditional on primitivity**:
  `CriticalSchurCollisionSupportBound.criticalGeometricMonodromy_eq_top_of_isPreprimitive`
  ("everything except primitivity is now discharged") and
  `OccupationSubsetPrimitivity.criticalOccupationRootAction_isPreprimitive` (only for `m ≠ n`).
  Card 7 is blocked on primitivity of the actual critical geometric monodromy.

## Runge build — state (2026-08-29)

`HTGeometry/RungeGridContour.lean` (built, axiom-clean, wired into the umbrella) now contains:

- `hEdge`, `vEdge`, `rectIntegral_eq_edges` — the four-edge decomposition of `RHTower.rectIntegral`;
- `gridCorner`, `gridSquare`, `gridRect`, `gridH`, `gridV`, `gridRect_eq_edges`;
- `shiftUp`, `shiftRight`, `hCoeff`, `vCoeff` and **`sum_gridRect_eq_edges`** — the edge-cancellation
  identity: a finite sum of grid-square contour integrals equals a signed sum of edge integrals;
- `GridSelects`, `hCoeff_eq_zero_of_mem`, `vCoeff_eq_zero_of_mem`,
  `hEdge_avoids_of_hCoeff_ne_zero`, `vEdge_avoids_of_vCoeff_ne_zero` — a surviving edge misses `K`;
- `uIcc_reProdIm_gridSquare`, `analyticOnNhd_cauchyKernelMul`,
  `gridRect_cauchyKernel_eq_zero`, `gridRect_cauchyKernel_eq_value` — the Cauchy kernel on one
  grid square (`0` off the square, `2πi·F z` strictly inside).

Also built (axiom-clean, wired):
- `HTGeometry/IntervalRiemannSum.lean` — `uniformNode`, `uniformNode_last`,
  `uniformNode_succ_sub`, and `norm_intervalIntegral_sub_uniformRiemannSum_le`
  (left-endpoint Riemann sums with an oscillation bound).
- `HTGeometry/RungeEdgeRiemann.lean` — `edgeCauchyIntegral`, `edgeCauchyRiemann`,
  `continuousOn_edgeCauchyIntegrand`, and **`exists_edgeCauchyRiemann_approx`**: for `Z` compact
  and disjoint from a compact parametrized edge, the Cauchy-kernel edge integral is uniformly
  `ε`-approximated on `Z` by a rational function of `z` with simple poles at the nodes of the edge.
- In `RungeGridContour.lean`: `dist_le_two_mul_of_mem_gridSquare`, **`exists_gridSelection`**
  (a mesh `s < s₀` and the finite selected set `S` with `GridSelects S s K` and every selected
  square inside `Ω`), `floor_grid_lt`, `grid_index_unique`, and **`sum_gridRect_cauchyKernel`**
  (the representation `∑_{p∈S} gridRect (F(·)(·−z)⁻¹) = 2πi·F z` for `z` off the grid lines whose
  own square is selected).

Remaining stages, in order:
4b. **Assembly of the contour representation.**  For `K ⊆ Ω` compact pick `s` with
   `s√2 < dist(K, Ωᶜ)`; let `S` = squares meeting `K` (finite since `K` is bounded).  Then every
   selected square is inside `Ω`, and for `z ∈ K` off the grid lines exactly one selected square
   contains `z` strictly and no other square contains `z` at all, so
   `F z = (2πi)⁻¹ Σ_{p∈S} gridRect (F(·)(·−z)⁻¹) s p`.  Combine with `sum_gridRect_eq_edges`.
5. **Extension to all of `K`** — *simplified*: no continuity of the contour functional is needed.
   For `z ∈ K` put `m = ⌊z.re/s⌋`, `n = ⌊z.im/s⌋`; the square `(m,n)` contains `z`, hence is
   selected, and `z` is a limit of points `z_j` strictly inside it.  Each `z_j` is off the grid
   lines with `(⌊z_j.re/s⌋, ⌊z_j.im/s⌋) = (m,n) ∈ S`, so the representation applies at `z_j`; the
   estimate `|F(z_j) − R(z_j)| ≤ ε` then passes to `z` because `F` and the rational `R` (poles on
   `Γ`, and `dist(K,Γ) > 0`) are both continuous at `z`.
6. **Riemann sums** — DONE (`exists_edgeCauchyRiemann_approx`).
7. **Pole pushing** — DONE.  `HTGeometry/RungePolePush.lean` (built, axiom-clean, wired):
   `polePushSum`, `infPushSum`, `polePush_identity`, `infPush_identity`,
   `norm_polePush_error`, `norm_infPush_error`, **`exists_polePush_small`** (uniform approximation
   on `K` of `(·−a)⁻¹` by rational functions with a single pole at a nearby `b`) and
   **`exists_infPush_small`** (by polynomials, for a far pole).
8. **The `Ω`-hull** — ELIMINATED by the selection-rule simplification above.
9. **Assembly** (the only remaining stage): choose `R` with `K ⊆ ball 0 (R/2)` and `s` with
   `2s < dist(K, ℂ∖Ω)` and `4s < R`; set `S := {p | gridSquare s p ⊆ Ω ∧ gridSquare s p ⊆ ball 0 R}`
   (finite, and `GridSelects S s K`); apply `sum_gridRect_cauchyKernel` +
   `sum_gridRect_eq_edges` + `exists_edgeCauchyRiemann_approx` + the two pole pushes; conclude
   `DA(Ω)` dense in the compact-open topology and promote card 2.

### Runge simplification (2026-08-29): no `Ω`-hull, no pole-pushing chains

Select the grid squares by **`gridSquare s p ⊆ Ω` and `gridSquare s p ⊆ ball 0 R`**, not by
"meets `K`".  Then:

* every square meeting `K` is still selected (choose `2s < dist(K, ℂ∖Ω)` and `K ⊆ ball 0 (R/2)`),
  so `GridSelects` holds and the contour representation applies at every point of `K`;
* the bounded components of `ℂ∖K` that lie inside `Ω` are *filled* by selected squares, so no
  surviving edge encircles them — this is exactly what the `Ω`-hull was for;
* a surviving edge has a neighbouring square that is either **not inside `Ω`** — and then that
  square contains a point `b ∉ Ω` within `2s` of the edge, while `dist(b, K) ≥ dist(K, ℂ∖Ω)`, so a
  **single** geometric-series step pushes the pole to `b` — or **not inside `ball 0 R`** — and then
  the edge is at distance `≥ R/2` from `K`, so a single expansion in powers of `z` pushes the pole
  to `∞`, producing a polynomial.

So stages 7 (chaining) and 8 (hull) collapse to two truncated geometric series.

## Card 2 — CLOSED (2026-08-29)

Runge's theorem is now Lean-proved in the corpus:
**`GaloisForLFunctions.HTGeometry.approxOn_rungeDA_of_analyticOnNhd`** — on an open preconnected
nonempty infinite `Ω ⊆ ℂ`, every `F` analytic on `Ω` is, on every compact `K ⊆ Ω`, a uniform limit
of functions that are analytic *and* differentially algebraic on all of `Ω` (in fact rational with
poles off `Ω`, plus polynomials).  Modules: `RungeGridContour`, `IntervalRiemannSum`,
`RungeEdgeRiemann`, `RungePolePush`, `RungeApproxClass`, `RungeSelection`, `RungeEdgeApprox`,
`RungeDensity`, `RungeCompactOpenDensity`.

Card capstones: `dense_daCompactOpenLocus`, `isMeagre_daCompactOpenLocus`,
`isGδ_htCompactOpenLocus`, `dense_htCompactOpenLocus`, `compactOpen_interlacing`,
`exists_mem_both_of_isOpen`, `compactOpen_phase_selector_collapse`, `dense_hardyDALocus`,
`dense_compl_hardyDALocus`, `hardy_phase_selector_collapse`.  All axiom-clean.

**Reusable for the rest of the sweep:** Runge means "DA is dense in `O(Ω)`" is now a lemma, so any
card needing a *generic* / *dense* / *prevalent* hypertranscendence statement in a function space
(cards 8, 13, and the density half of 9) can quote `dense_htCompactOpenLocus` and
`isGδ_htCompactOpenLocus` instead of rebuilding a Baire argument.

## Card 5 — CLOSED (2026-08-29)

The Ostrowski dependence is gone.  The open sub-problem recorded above — that
`FormalHypertranscendence.aeval_survives` needs a *global* gap inequality `r·b_k + 2W < b_{k+1}`
while an arbitrary relation has unbounded `(r, W)` — is now solved:

**`GaloisForLFunctions.HTGeometry.hypertranscendental_of_eventualGap`** — a smooth function whose
Taylor series is supported on a strictly increasing sequence with *eventually* superlinear gaps and
infinitely many nonzero coefficients is hypertranscendental.

The circularity breaks because the prefix removal is done *after* the relation is fixed: the prefix
is a polynomial of degree `b_K`, adding it is an invertible triangular jet substitution
(`FormalJetPrefixShift`), and the substituted relation's degree data grows only linearly in `b_K`
(`JetMonomialDegreeBounds`), which the gaps outrun.  **Reusable by every other card that needs
hypertranscendence of a lacunary series with unprescribed coefficients.**

New modules: `JetMonomialDegreeBounds`, `FormalJetPrefixShift`, `EventualGapHypertranscendence`,
`GapSeriesEntireCarrier`, `GapExponentialCarrier`, `RationalDenominatorLadder`,
`LadderPrimeFrequencies`, `TailGcd`, `ExponentialSumMinimalOrder`,
`LocallyCyclicTranslationStabilizer`.  All axiom-clean.

Other reusable assets this card left behind:
- `TailGcd.tailGcd` / `dvd_tailGcd_iff` — gcd of an infinite tail of a sequence (mathlib gap).
- `RationalDenominatorLadder.exists_denLadder` — every subgroup of `ℚ` containing `1` is a union of
  cyclic groups along a divisibility ladder (mathlib gap).
- `ExponentialSumMinimalOrder.minimal_constCoeffOrder_expSum` — the minimal constant-coefficient
  order of a finite exponential sum is its number of modes.
- `LocallyCyclicTranslationStabilizer.isLocallyCyclic_iff_subset_ratLine` — locally cyclic subgroups
  of `ℂ` are exactly the rational lines.
- `GapSeriesEntireCarrier` / `GapExponentialCarrier` — a complete gap-series calculus: entire
  carrier, Taylor coefficients, dilation/difference law, finite-support collapse to an exponential
  polynomial, hypertranscendence.

## Card 13 survey (2026-08-29) — the card's Lean-status section is stale

`random-holomorphic-maximal-translation-ht-law` claims the tree "does not formalize random
holomorphic functions ... or countable differential-support avoidance as one theorem".  That is no
longer true.  The corpus already owns the card's **main theorem**:

- `HTGeometry/RandomAffineJetPacketFreeness.lean` —
  `HasAbsolutelyContinuousFiniteAffineJetLaws` (the card's hypothesis (ND), in a stronger
  multivariate affine-palette form), `measure_compl_preimage_affineJetPacketGenericSet_eq_zero`,
  `ae_affineOrbit_no_polynomialDifferentialRelation`,
  **`ae_translationOrbit_no_polynomialDifferentialRelation`** — for every countable injectively
  coded set of shifts, finite-jet absolute continuity gives almost-sure freeness of every finite
  family of distinct translates.
- `HTGeometry/FiniteJetLawDeterministicGauge.lean` — `HasAbsolutelyContinuousFiniteAffineJetLaws.add_const`
  and `ae_translationOrbit_no_polynomialDifferentialRelation_add_const`: the card's
  **finite-deterministic-passport stability**.
- `HTGeometry/ComplexPolynomialZeroMeasure.lean` — the zero set of a nonzero complex multivariate
  polynomial is Lebesgue-null; `HTGeometry/FiniteJetPolynomialAvoidance.lean` — the absolutely
  continuous pullback statement.
- `HTGeometry/EvaluationMinorGeneralDomain.lean` — the card's evaluation lemma (a linearly
  independent finite family of functions has a nonsingular evaluation minor at distinct points).
- `HTGeometry/AdditiveNoiseAbsoluteContinuity.lean` — `map_add_const_absolutelyContinuous`,
  `map_snd_add_noise_prod_absolutelyContinuous` (absolute continuity survives independent additive
  noise).
- `HTGeometry/BoundedComplexCoefficientProbability.lean` — `complexSquareProbability`, absolutely
  continuous, and the clamp that is a.s. the identity;
  `HTGeometry/InfiniteProductFiniteHead.lean` — `map_countableProductHead_infinitePi`;
  `HTGeometry/BoundedRandomEntireSeries.lean` — `boundedRandomEntireSource`, a *total* entire
  random series (clamped coefficients, no almost-sure convergence needed).

**What is missing is a model.**  No declaration in the tree verifies
`HasAbsolutelyContinuousFiniteAffineJetLaws` for any concrete random source, so the capstones are
so far vacuously applicable.  Remaining work for card 13:

1. prove `HasAbsolutelyContinuousFiniteAffineJetLaws` for `boundedRandomEntireSource` under
   `Measure.infinitePi (fun _ => complexSquareProbability)` — the jet packet is a linear image of
   the coefficient sequence, its first `N` coordinates go through an invertible confluent
   Vandermonde (Hermite) matrix, and the tail is independent additive noise;
2. the planar Gaussian instance `∑ ξₙ zⁿ/√(n!)` (needs a.s. entirety of a Gaussian series);
3. assemble the card's statements (2), (3), (9), (12), (14).

### Card 13 build plan (started 2026-08-29)

Landed so far:
- `HTGeometry/OneDimJetEvalBridge.lean` — **`multiIndexJetEvalCLM_oneDim`**: in one coordinate the
  canonical multi-index jet observation of `oneDimMultivariateEntireOfDifferentiable g hg` is
  `iteratedDeriv (a 0) g (x 0)`.  (Route: `orderedPartialJetEvalCLM_congr_of_wordMultiplicity_eq`
  to a constant word, then `ContinuousLinearMap.iteratedFDeriv_comp_right` along `proj 0`.)
- `HTGeometry/InfinitePiSumSplit.lean` — **`map_sumPiEquivProdPi_infinitePi`** (an infinite product
  law indexed by a sum type is the product of the two block laws; mathlib gap) and
  **`map_headTail_infinitePi`** (the first `N` coordinates and the rest are independent, with
  `Measure.pi` on the head).  Route: `Measure.eq_infinitePi` + `Finset.toLeft/toRight` +
  `Finset.prod_disjSum`, then `Measure.infinitePi_map_piCongrLeft`, `MeasurableEquiv.map_symm_map`
  and `Measure.infinitePi_eq_pi`.

Still to build:
1. `entireOfCoeffs` head/tail split: `entireOfCoeffs a z = ∑_{n<N} aₙ zⁿ + Tₙ(a∘(N+·)) z` with the
   tail entire and depending only on the shifted coefficients (`sum_add_tsum_nat_add` +
   `summable_of_orderTwo_bound`).
2. Additivity of the one-coordinate embedding `oneDimMultivariateEntireOfDifferentiable`, so the
   jet packet splits as `A·(first N coefficients) + (tail observation)`.
3. Confluent Vandermonde: for pairwise distinct points `q_(row,i)` and orders `orders i`, the
   `N × N` matrix of `(d/dz)^j zⁿ |_{q}` (`N = ∑_(row,i) orders i`) is invertible — because a
   polynomial of degree `< N` vanishing to those orders is divisible by a degree-`N` product.
4. Measurability of `x ↦ Ψ(F x)`: the tails go to `0` locally uniformly, so the jet packet is the
   pointwise limit of the finite-head observations.
5. `HasAbsolutelyContinuousFiniteAffineJetLaws (Measure.infinitePi (fun _ => complexSquareProbability))
   (fun h => oneDimTranslationFrame (shift h)) boundedRandomEntireSource`, via
   `map_headTail_infinitePi`, `PiMeasureAbsoluteContinuity`, the invertible linear image, and
   `map_snd_add_noise_prod_absolutelyContinuous`.
6. The card capstones, plus the planar Gaussian instance (needs a.s. entirety of `∑ ξₙ zⁿ/√(n!)`).

### Card 13 — the model is built (2026-08-29)

**`GaloisForLFunctions.HTGeometry.hasAbsolutelyContinuousFiniteAffineJetLaws_boundedRandomEntire`**
— the clamped independent-coefficient random entire series realizes the finite-jet nondegeneracy
hypothesis (ND) for every countable palette of translations.  The corpus's abstract capstones are
therefore no longer vacuously applicable, and
**`ae_translationOrbit_free_boundedRandomEntire`** and
**`ae_translationOrbit_free_boundedRandomEntire_add_const`** are unconditional statements about a
concrete random entire function.  All axiom-clean.

New modules and what they own:
- `OneDimJetEvalBridge` — `multiIndexJetEvalCLM_oneDim`: a one-coordinate multi-index jet is an
  iterated derivative.
- `OneDimTranslationJetPacket` — `pullback_oneDimTranslationFrame`,
  `multivariateAffinePatternObservationCLM_oneDim`, `packetPoint`, `packetOrder`: a translation jet
  packet reads derivatives at translated base points.
- `ConfluentVanishingPolynomial` — `polynomial_eq_zero_of_jets_vanish` (a polynomial of degree below
  the total vanishing order that vanishes to those orders at distinct points is zero) and
  `sum_count_le_card`.
- `PacketHermiteSurjectivity` — `multiIndexBelowOneEquiv`, `card_patternJet`,
  `card_coordinate_eq_sum_orders`, `packetHermiteMap`, and **`surjective_packetHermiteMap`**: the
  square Hermite evaluation of the first `N` monomials at the packet nodes is bijective.
- `InfinitePiSumSplit` — **`map_sumPiEquivProdPi_infinitePi`** (an infinite product law indexed by a
  sum type is the product of the block laws — a mathlib gap) and **`map_headTail_infinitePi`**.
- `BoundedRandomEntireStructure` — joint continuity of the clamped series, continuity of the source
  map, and the head–tail split of the series.
- `BoundedRandomEntireTail`, `RandomEntireTailSource` — the tail is `z^N` times another clamped
  series, entire, and a continuous family of sources.
- `RandomEntirePacketSplit` — **`finiteAffineJetPacketObservation_split`**: the packet is the
  Hermite image of the clamped head plus a function of the shifted coordinates.
- `RandomEntireJetLawNondegeneracy`, `RandomEntireTranslationOrbitFreeness` — the measure assembly
  and the card capstones.

**Still open on card 13:**
1. the planar Gaussian instance `∑ ξₙ zⁿ/√(n!)` (needs a.s. entirety of a Gaussian series and
   nondegeneracy of complex Gaussian jet covariances);
2. the *finite Taylor conditioning* claim in its exact form.  The corpus's
   `HasAbsolutelyContinuousFiniteAffineJetLaws` asks for absolute continuity at **every** admissible
   base, and the conditioned residual `z^{L+1}·(…)` genuinely fails it at a packet with a node at
   `0`.  The card's own proof handles this by choosing the evaluation points nonzero, so the
   faithful formalization needs a witness layer (`affineJetPacketWitness`) that can avoid a
   prescribed finite set of nodes.  `ae_translationOrbit_free_boundedRandomEntire_add_const`
   already gives the deterministic-gauge half.

### Card 13 — next steps (precise)

Landed: `HTGeometry/AffineFramePacketAvoidance.lean` —
**`exists_base_separating_avoiding_and_eval_ne_zero`**: a separating base can additionally be chosen
so that every packet node avoids a prescribed finite set of values (an affine automorphism has a
non-constant coordinate, so landing on a fixed point is a nontrivial condition).

Remaining chain for the *finite Taylor conditioning* statement:
1. a witness structure carrying `packet_nonzero` (nodes ∉ a prescribed finite set) and its
   existence, mirroring `nonempty_separatedMultivariateAffinePatternWitness` but calling
   `exists_base_separating_avoiding_and_eval_ne_zero`;
2. **generalize** `AffineJetDifferentialIndependence.exists_affineJetRelationValue_ne_zero` to an
   arbitrary witness family `wit : ∀ p, MultivariateAffinePatternWitness frame p` and
   `f ∈ multivariateAffinePatternResidualSet frame wit`, keeping the present statement as a
   corollary so no call site changes; the same for
   `RandomAffineJetPacketFreeness.measure_compl_preimage_affineJetPacketGenericSet_eq_zero`;
3. the tail source `z^{L}·(clamped series)` has absolutely continuous jet packets at every base
   whose nodes are nonzero — same Hermite argument with the monomials `X^{L+n}`, injective because
   `z^L` is a unit at nonzero nodes;
4. the conditioning capstone.

Remaining for the planar Gaussian instance: a.s. entirety of `∑ ξₙ zⁿ/√(n!)` (Borel–Cantelli with
Gaussian tails), then the same head/tail architecture with the Gaussian coefficient law in place of
`complexSquareProbability` (`ComplexGaussianObservables.complexGaussian_absolutelyContinuous` and
`PiMeasureAbsoluteContinuity` supply the absolute continuity).

### Card 13 — the conditioning half is closed (2026-08-29)

**`ae_translationOrbit_free_randomEntireTail_add_const`** — fixing any finite prefix of the
coefficients and adding any deterministic entire passport leaves the translation orbit of the
residual random source almost surely differentially free.  This is the card's *finite Taylor
conditioning* statement.

The obstruction was that the residual `z^L·(…)` has a genuinely degenerate jet packet at a node at
the origin, while the corpus's `HasAbsolutelyContinuousFiniteAffineJetLaws` demands absolute
continuity at *every* admissible base.  Resolved exactly as the card's own proof does — by choosing
the evaluation nodes away from the origin:

- `AffineFramePacketAvoidance` — `exists_avoid_poly`,
  **`exists_base_separating_avoiding_and_eval_ne_zero`**.
- `AvoidingAffineJetPacketWitness` — **`exists_separatedWitness_avoiding`**,
  `avoidingAffineJetPacketWitness` and its packet-injectivity and avoidance lemmas.
- Two corpus theorems were **generalized in place** (old statements kept as corollaries, so no call
  site changed): `AffineJetDifferentialIndependence.exists_affineJetRelationValue_ne_zero_of_witness`
  and `RandomAffineJetPacketFreeness.measure_compl_preimage_residualSet_eq_zero`, plus
  `finiteAffineJetPacketDeterminant_ne_zero_of_witness` and
  `mem_multivariateAffinePatternResidualSet_iff`.
- `ConfluentVanishingPolynomial.polynomial_eq_zero_of_shifted_jets_vanish` — the monomial factor is
  a unit at nonzero nodes, so it contributes no root multiplicity.
- `PacketHermiteSurjectivity.packetShiftedHermiteMap` / `surjective_packetShiftedHermiteMap`.
- `BoundedRandomEntireTail.boundedRandomEntireTail_split`,
  `RandomEntireTailPacketSplit.finiteAffineJetPacketObservation_tail_split`.
- `AvoidingRandomAffineJetFreeness` — `HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws`,
  `ae_affineOrbit_free_of_avoidingJetLaws`, and the tail's node-avoiding nondegeneracy.
- `RandomEntireConditionedOrbitFreeness` — the capstone.

**Card 13's last open item: the planar Gaussian instance.**  Plan (all pieces checked against the
corpus first):
1. `complexGaussianProbability : Measure ℂ` — the pushforward of `gaussianReal 0 1 ×ˢ gaussianReal 0 1`
   through `Complex.measurableEquivRealProd.symm`, mirroring `complexSquareProbability`; a genuine
   probability measure (the existing `ComplexGaussianObservables.complexGaussian` is a density that
   is deliberately *not* claimed to have total mass one, so it cannot feed `Measure.infinitePi`);
2. almost-sure polynomial bound `|xₙ| ≤ n` eventually — Chebyshev (`variance_gaussianReal`) plus
   Borel–Cantelli, both in mathlib;
3. the entire carrier of `∑ xₙ zⁿ/√(n!)` on that event via `EntireCoeffs`/`coeffFun` (more flexible
   than the order-two interface used for the clamped model), with `n·rⁿ/√(n!) → 0` from
   `n²·(r²)ⁿ/n! → 0`;
4. the same head/tail packet split; the divergence set is a tail event, so `Measure.map_congr`
   reduces to the linear model almost everywhere.

### Card 13 — Gaussian instance, landed so far (2026-08-29)

- `ComplexGaussianCoefficientProbability` — `complexGaussianProbability` (a genuine probability
  measure, unlike the existing density-only `ComplexGaussianObservables.complexGaussian`), its
  Lebesgue absolute continuity, the finite product version, and the Chebyshev tail
  `measure_norm_ge_le`.
- `GaussianCoefficientTail` — `gaussianCoefficientLaw`, `summable_gaussianTailBound` and
  **`ae_eventually_norm_le_index`**: almost surely `‖xₙ‖ < n` for all large `n` (Chebyshev plus the
  first Borel–Cantelli lemma).
- `GaussianEntireCarrier` — `gafCoeff`, `tendsto_pow_div_sqrt_factorial`,
  **`entireCoeffs_gafCoeff`** (the polynomial-growth event gives entire coefficients) and the total
  source `gaussianEntireSource` (the series where it converges, `0` elsewhere).
- `PacketHermiteSurjectivity.packetShiftedHermiteMap` was generalized to carry an arbitrary
  nonvanishing weight sequence, so the same surjectivity serves the clamped model
  (`(4·n!)⁻¹`) and the Gaussian model (`(√(n!))⁻¹`).

Remaining for the Gaussian instance:
1. the tail carrier `gaussianTailFun N y = z^N · coeffFun (yₖ/√((k+N)!))` and its entire
   coefficients on the tail-goodness event (a tail-measurable event, so it is a function of the
   shifted coordinates alone);
2. locally uniform convergence of the partial sums of an `EntireCoeffs` series, transported to the
   compact-open source space, giving **`packet ∘ source` measurable as a pointwise limit** — the
   Gaussian source is not continuous in the coefficients, so the clamped model's continuity route
   is unavailable and this limit argument replaces it;
3. the head/tail packet split and the absolute-continuity assembly, identical to the clamped case
   with `Measure.map_congr` absorbing the null divergence set.

### Card 13 — CLOSED (2026-08-29)

Both models are built and the card is at stage 3.

- Model 1 (the card's family `(14)`): the clamped independent-coefficient series —
  `hasAbsolutelyContinuousFiniteAffineJetLaws_boundedRandomEntire`,
  `ae_translationOrbit_free_boundedRandomEntire`.
- Finite Taylor conditioning: `ae_translationOrbit_free_randomEntireTail_add_const`, via the new
  node-avoiding witness layer (`exists_base_separating_avoiding_and_eval_ne_zero`,
  `exists_separatedWitness_avoiding`, `ae_affineOrbit_free_of_avoidingJetLaws`).
- Model 2 (the card's `(9)`): the planar Gaussian entire function `∑ ξₙ zⁿ/√(n!)` —
  `complexGaussianProbability`, `ae_eventually_norm_le_index` (Chebyshev + Borel–Cantelli),
  `gaussianEntireSource`, `hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_gaussianEntireSource`,
  **`ae_translationOrbit_free_gaussianEntireSource`** and its `add_const` form.

**Reusable beyond this card:**
- `InfinitePiSumSplit.map_sumPiEquivProdPi_infinitePi` — an infinite product law indexed by a sum
  type is the product of the two block laws (mathlib gap), and the head/tail specialization.
- `EntireCoeffsPartialSumSource` — partial sums of an entire coefficient series converge in the
  compact-open source space; the standard way to get measurability of jet observations of a random
  entire function that is *not* continuous in its coefficients.
- `AffineFramePacketAvoidance` / `AvoidingAffineJetPacketWitness` — escaping witnesses whose packet
  nodes avoid a prescribed finite set; needed by any source with a fixed vanishing point.
- `ComplexGaussianCoefficientProbability` — a complex Gaussian *probability* law (the pre-existing
  `ComplexGaussianObservables.complexGaussian` is a density whose total mass is deliberately not
  claimed, so it cannot feed `Measure.infinitePi`).

## Survey of the nine remaining cards (2026-08-29)

Every remaining card needs one classical theorem the corpus does not own.  What each is actually
blocked on, after searching the tree:

| # | Card | The one missing classical input | Corpus support already present |
|---|---|---|---|
| 1 | combination-mode-reducibility-baker-bridge | effective Baker–Wüstholz | qualitative Baker only (`general-baker-closed`) |
| 3 | ht-c28-minimal-handle-collapse | Weierstrass addition theorem; Padé stabilization | C07 (`PRecursiveDFinite`) and C05 (`differentiallyAlgebraic_of_deriv`) are owned; the (II)/(III) rows are classifications, not theorems |
| 6 | ht-q-residue-spectrum-classification | Adamczewski–Dreyfus–Hardouin rational-or-HT; Chen–Singer q-discrete residues | `QDifferenceInhomogeneousHT` proves two first-order inhomogeneous HT theorems |
| 7 | hypertranscendental-maximal-finite-horizon-galois-law | primitivity of the critical geometric monodromy | everything else discharged (`CriticalSchurCollisionSupportBound`) |
| 8 | indeterminate-moment-fiber-prevalent-translation-ht | the Nevanlinna N-extremal matrix (the parent card in `nad/` is blocked on the same input) and prevalence | `NevExtremalFamily`, `CauchyMomentFlatness`, `MomentFunctionalPositivity`, `StieltjesTransformPick` |
| 9 | laguerre-polya-jensen-profield-blindness | **Schur's composition theorem** (equivalently Pólya–Schur for the binomial multiplier) | the whole pro-field/surgery layer is owned — see below |
| 10 | poincare-constraint-order-recession | Bergweiler's Poincaré-HT theorem; the cascade jet-independence hypothesis | `PoincareRecession.exactDifferentialOrder_iterate_of_separation`, `EntirePoincareExtension` |
| 11 | projective-horizon-hankel-secant-stratification | codimension and singular locus of Hankel determinantal varieties; rational singularities | the exact rank/recurrence core is formalized |
| 12 | projective-ht-generic-pv-curvature-core | *differential* Picard–Vessiot with group `SL_N` | only *difference* PV is present |

### Card 9 is the most tractable, and its structural half is already owned

The stage-3 sibling `07-functional-analysis-operator-theory/power-normalization-profield-krein-blindness.md`
formalizes exactly card 9's architecture — `P_N(F) = ℂ(z)⟨T_h(F^N)⟩`, rational-gauge invariance at
every power level, termwise equality of the complete inverse system, its logarithmic-residue
intersection, maximal translation differential independence, and the functional-equation-even
entire order-one Schwarz-real realizations with prescribed divisor surgery
(`HTGeometry.PowerNormalizationProfieldKreinBlindness`, `MovingDivisorEvenProduct`,
`EvenSurgeryPoleSeparationWitnesses`, `KreinEscapePowerFieldInvariance`).  Card 9 replaces the Krein
index by Laguerre–Pólya membership, so items (3) and (4) of its theorem are structurally owned.

What is genuinely missing is the Jensen half.  The reduction is:

* `J^{d,n}_F` hyperbolic for all `d,n` ⟹ `F ∈ LP` is **easy**: `J^{d,0}(z/d) → F(z)` locally
  uniformly because `C(d,j)/d^j → 1/j!`, and a rescaled hyperbolic polynomial is still real-rooted,
  so `F` is a locally uniform limit of real-rooted real polynomials.  This gives the card's
  `E_(θ,k)` half by contraposition.
* `F ∈ LP` ⟹ every `J^{d,n}_F` hyperbolic is **Schur's composition theorem**: with
  `f = Σ γ_j x^j/j!` real-rooted and `g = (1+x)^d = Σ C(d,j) x^j` real-rooted with all roots of one
  sign, `Σ_j j!·(γ_j/j!)·C(d,j) x^j = Σ_j C(d,j) γ_j x^j = J^d_F(x)` has only real zeros.  Neither
  Schur composition nor multiplier sequences are in mathlib or the corpus; this is the layer to
  build.

## Card 9 — the Laguerre–Pólya / Jensen layer (2026-08-29)

The route through Grace/apolarity is abandoned.  `P(D)[X^d] = ∑_j d^{(j)} a_j X^{d-j}` is the
coefficient reversal of the Jensen polynomial of `P`, so Schur composition reduces to
**Hermite–Poulain**, which reduces to the **Laguerre shift lemma**: `p ↦ p' − βp` preserves
real-rootedness.  That lemma is elementary (exponential gauge + Rolle + a multiplicity count), so
the whole classical input is now built from scratch.

Landed (all axiom-clean, all wired into `GaloisForLFunctions.HTGeometry`):

- `HTGeometry/LaguerreShiftSplits.lean` — `laguerreShift β p = p' − βp`; the gauge derivative
  identity, the interior Rolle root, the multiplicity drop `mult_x p − 1 ≤ mult_x (Lp)`,
  `natDegree_ne_card_roots_succ` (**a real polynomial can never miss exactly one root**, which
  removes the classical analysis-at-infinity step), and **`splits_laguerreShift`**.
- `HTGeometry/SplitsReflect.lean` — **`Splits.reflect`**: reversing the coefficient order preserves
  splitting over any field (mathlib gap).
- `HTGeometry/HermitePoulain.lean` — `diffOpApply h p = (aeval derivative h) p` in
  `Module.End ℝ ℝ[X]`, its multiplicativity, and **`splits_diffOpApply`** (Hermite–Poulain).
- `HTGeometry/JensenPolynomialSplits.lean` — `jensenReverse`, `jensenPoly`,
  `diffOpApply_X_pow` (the reversal identity), and **`splits_jensenPoly_of_splits`**.
- `HTGeometry/HurwitzClosedZeroLocus.lean` — the Rouché-free sphere-domination zero-planting lemma
  and **`zero_mem_closed_of_tendstoLocallyUniformly`** in the `HTGeometry` layer.  (`RHTower`
  already owned an entire-function copy in `RHTower/LocallyUniformZeroTransfer.lean`; `HTGeometry`
  may not import `RHTower`, and editing that file would stale the whole Xi olean stack, so the
  proof was re-laid at the correct layer instead.)
- `HTGeometry/RealRootedCoefficientLimit.lean` — `im_eq_zero_of_splits`,
  `splits_of_forall_complex_root_real`, and **`splits_of_tendsto_coeff`**: real-rootedness is
  closed under coefficientwise limits of bounded degree.
- `HTGeometry/JensenPolynomialLimit.lean` — `coeff_jensenPoly`, `natDegree_jensenPoly_le`,
  **`splits_jensenPoly_of_tendsto_coeff`**.
- `HTGeometry/LaguerrePolyaClass.lean` — `polyEvalC`, the iterated-derivative transfer
  `tendstoLocallyUniformly_iterate_deriv`, the class `LaguerrePolya`, coefficient convergence,
  **`splits_jensenPoly_of_laguerrePolya`** (Jensen's theorem, forward direction) and
  **`im_eq_zero_of_laguerrePolya`** (a nonzero Laguerre–Pólya function has only real zeros).

### What card 9 still needs

1. **`movingEvenCanonicalProduct θ ∈ LaguerrePolya`.**  Its partial products are the real
   polynomials `∏_{n<N} (1 − X²/Λ_n²)`, each split with roots `±Λ_n`; the corpus already owns the
   locally uniform product convergence (`RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn`,
   `movingEvenCanonicalProduct_eq_tprod`), so what is missing is only the passage from the
   `Finset ℕ`-indexed `HasProdLocallyUniformlyOn` to the `atTop`-indexed sequence of `Finset.range`
   partial products, plus the identification of those partial products with `polyEvalC`.
2. **Jensen's converse**: all `jensenPoly c d` split ⟹ the entire function `∑ c_j z^j` is
   Laguerre–Pólya.  Route: `jensenScaled c d := (jensenPoly c d).comp (C (d:ℝ)⁻¹ * X)` splits for
   `d ≥ 1`, and `d^{(j)}/d^j → 1` with `d^{(j)}/d^j ≤ 1` gives a dominated locally uniform
   convergence `jensenScaled c d → ∑ c_j z^j`.
3. **Assembly.**  `HTGeometry.PowerNormalizationProfieldKreinBlindness.exists_powerNormalizationProfield_allEvenKreinIndex`
   already delivers card 9's items (3) and (4) verbatim — one `θ`, one entire even Schwarz-real
   order-one family with prescribed quartet surgery, equal power-translation fields at every level,
   equal complete inverse systems and equal intersections, and maximal translation differential
   independence.  Card 9's capstone replaces `HasExactKreinIndex` by: `k = 0` is Laguerre–Pólya
   with every Jensen polynomial hyperbolic, and `k ≥ 1` is not (its inserted quartet zeros are
   off-real, `movingEvenCanonicalSurgeryProduct_inserted_zero_analyticOrderAt`), hence some Jensen
   polynomial fails.

## Card 9 — CLOSED (2026-08-29)

`GaloisForLFunctions.HTGeometry.exists_powerNormalizationProfield_laguerrePolyaJensenBlindness`.
All thirteen new modules are axiom-clean and wired into the umbrella.  The three items still listed
as missing above are now all done:

1. `laguerrePolya_movingEvenCanonicalProduct` — the partial products
   `∏_{n<N} (1 − X/Λ_n)(1 + X/Λ_n)` split, and `Summable.hasProdUniformlyOn_nat_one_add` on every
   compact set plus `tendsto_finset_range` turns the `Finset ℕ`-indexed product into an
   `atTop`-indexed locally uniform limit.
2. `laguerrePolya_of_splits_jensenPoly` — the converse.  `jensenScaled c d = J^d(X/d)` splits by
   `splits_comp_C_mul_X`, and Tannery's theorem against the majorant `∑ |c_i| R^i` (which is itself
   extracted from the entire power series by `summable_norm_iff` and a geometric comparison) gives
   the locally uniform convergence to `∑ c_i z^i`.
3. Assembly against `exists_powerNormalizationProfield_allEvenKreinIndex`, using
   `movingEvenCanonicalSurgeryProduct_empty` for the `k = 0` identification and the exact-divisor
   package for the off-real zeros at `k ≥ 1`.  The `local instance` block of the Krein module has to
   be re-enabled with `attribute [local instance]` in any importer.

**Reusable beyond this card:**
- `splits_laguerreShift`, `splits_diffOpApply` (Hermite–Poulain), `Splits.reflect`,
  `splits_comp_C_mul_X` — a complete real-rootedness calculus, none of it in mathlib.
- `natDegree_ne_card_roots_succ` — a real polynomial never misses exactly one root.
- `splits_of_tendsto_coeff` — real-rootedness is closed under coefficientwise limits of bounded
  degree (via the new `HTGeometry` Hurwitz layer).
- `LaguerrePolya` with both directions of Jensen's theorem; `realTaylorCoeff` and
  `exists_jensenPoly_not_splits_of_nonreal_zero` for any Schwarz-real entire function.
- `HTGeometry/HurwitzClosedZeroLocus.lean` — the closed-zero-locus transfer at the `HTGeometry`
  layer, so no `HTGeometry` module has to reach into `RHTower` for Hurwitz any more.

## Card 6 — route found (2026-08-29): ADH is not needed

`ht-q-residue-spectrum-classification` was recorded as blocked on Adamczewski–Dreyfus–Hardouin's
rational-or-hypertranscendental dichotomy.  It is not: the corpus already owns an **exact** criterion
that supersedes it for this equation.

`HTGeometry.SourceLogarithmicBoundary.automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping`
states, for a family of additive primitives `x` with base increments `b` under automorphisms
`sigma` (with `tau` on the base),

```text
DifferentialIndependent K x  ↔  ∀ c ≠ 0, ∀ k : K, ∃ i, tau i k - k ≠ ∑_j c_(i,j) · δ^j (b i)
```

Instantiate with `I = Unit`, `C = ℂ`, `K = RatFunc ℂ` under the Euler derivation `δ = x d/dx`,
`L =` Laurent series at `0` with the same derivation, `sigma = ` dilation by `q`, `x = f` and
`b = r`.  All the structural hypotheses are routine: the Euler derivation commutes with dilation,
constants are fixed, and the `sigma`-invariants of `LaurentSeries ℂ` are the constants because `q`
is not a root of unity.  Hypertranscendence of `f` therefore reduces to the purely algebraic

> **(Q)** if `[r] ≠ 0` in `W_q = ℂ(x)/(σ−1)ℂ(x)` then no nonzero finite combination
> `∑_j c_j δ^j r` is `q`-summable.

**The `q`-residue calculus needed for (Q).**  On the partial-fraction basis `e_(α,d) = (x−α)^{-d}`
with `α ≠ 0`,

```text
σ e_(α,d) = q^{-d} e_(α/q, d)
```

so each pair (`q^ℤ`-orbit of `α`, pole order `d`) is one block, and the σ-invariant functional on
that block is the **`q`-discrete residue**

```text
ρ_(O,d)(v) = ∑_n q^{-dn} v_n     (α_n = α_0 q^n),
```

whose vanishing characterises `(σ−1)`-images inside the block.  Poles at `0` are always summable
(`σ(x^{-d}) = q^{-d} x^{-d}` and `q^{-d} ≠ 1`), and monomials `x^N` with `N ≥ 1` are summable
(`q^N ≠ 1`), so the only remaining obstruction is the constant term — excluded by `r(0) = 0`.
The Euler derivation raises pole order without moving the orbit, so the top index `J` of a nonzero
`c` produces a nonvanishing residue at pole order `d + J`; that is exactly (Q).

**Remaining Lean work for card 6**, in order:

1. the `q`-dilation ring automorphism of `RatFunc ℂ` and the Euler derivation on it, with
   `σ ∘ δ = δ ∘ σ`;
2. partial fractions over `ℂ(x)`: the decomposition into a polynomial part and `(x−α)^{-d}` terms
   (check mathlib first — this may need building);
3. the `q`-discrete residue functionals, their `σ`-invariance, and the characterisation of
   `(σ−1)ℂ(x)` by their vanishing (Chen–Singer);
4. the Euler-jet pole-order computation giving (Q);
5. instantiation of the exact Ostrowski criterion for `L = LaurentSeries ℂ`, giving items (1)–(3)
   of the card;
6. the scaling action `S_a` on `W_q`, the stabilizer `H_r`, `q^ℤ ⊆ H_r`, injectivity of
   `H_r/q^ℤ → Sym(Supp)` and the bound `s!`;
7. the realization theorem: `r_K = ∑_{u ∈ K} e_(α_u)` has stabilizer exactly `K`.

### Card 6 progress (2026-08-29) — the hypertranscendence half is Lean-closed

Three new modules, all axiom-clean and wired into the umbrella:

- `HTGeometry/QOrbitResidue.lean` — **`qOrbitResidue q a d C = ∑ᶠ n, (q^{-d})^n · polePart C (a q^n) d`**,
  its evaluation as a finite sum, **`qOrbitResidue_ratFuncScale_sub`** (the residue annihilates every
  dilation coboundary) and **`not_dilationTelescoped_of_qOrbitResidue_ne_zero`**.  This is the
  general Chen–Singer obstruction; the corpus previously had only the two-adjacent-points special
  case `RationalPolePart.no_dilationTelescoper_of_orbit_mass`.
- `HTGeometry/QOrbitResidueEuler.lean` — additivity and scalar homogeneity of the residue,
  **`qOrbitResidue_ratFuncEulerOp`** (`ρ_(d+1)(δf) = −(d+1)ρ_(d+1)(f) − d·a·ρ_d(f)`), the vanishing
  of all Euler jets above the top level, the exact top-level formula
  `ρ_(D+j)(δ^j r) = (∏_{i<j} −(D+i)a)·ρ_D(r)`, and
  **`not_dilationTelescoped_eulerCombination`**: no nonzero constant-coefficient Euler polynomial of
  a function with a nonzero top residue is `q`-summable.  This is condition (Q).
- `HTGeometry/QPrimitiveResidueHypertranscendence.lean` — **`no_jetTelescoper_of_top_qOrbitResidue`**
  and **`hypertranscendentalOver_of_qPrimitive_top_residue`**: if `σ u − u = r` in `k((w))` with
  `r ∈ k(w)` having a nonzero top `q`-residue on one orbit, then `u` is differentially transcendental
  over `k(w)`.

The Adamczewski–Dreyfus–Hardouin dependency is therefore discharged for this equation: the corpus's
own exact Ostrowski criterion (`differentialIndependent_of_oneVariable_primitive`) plus the new
residue calculus replaces it.

**What card 6 still needs.**

1. **The hard half of Chen–Singer**: all `q`-discrete residues vanish (and the constant obstruction
   is absent) ⟹ `r` is `q`-summable.  Needed to identify the card's `H_r = {a : S_a[r] = [r]}` with
   the residue-defined stabilizer, and to get "`d_a` rational" from `a ∈ H_r`.  Route: partial
   fractions over `k(x)` — decomposition into a polynomial part plus `(x−α)^{-d}` terms — then
   explicit telescoping inside each (orbit, order) block plus `q^N ≠ 1` for the monomials and
   `q^{-d} ≠ 1` for the poles at `0`.  Neither mathlib nor the corpus has partial fractions yet.
2. The defect equation `(σ−1)d_a = S_a r − r` and the σ-invariant-Laurent-series step
   (`exists_C_of_innerDilation_eq_self` already gives it).
3. The stabilizer group theory: `q^ℤ ⊆ H_r`, injectivity of `H_r/q^ℤ → Sym(Supp_q[r])`, the `s!`
   bound.
4. The realization theorem for `r_K = ∑_{u ∈ K} x/(x−α_u)`.
5. The additive entire-plane corollary (`F(z) = f(e^{2πiz})`, `Stab_DA(F) = ℤ + τℤ`).

### Card 6 — the Chen–Singer criterion is now Lean-complete (2026-08-29)

Both halves of the `q`-summability criterion are proved, so items 1–3 of the card and the lattice
containment of item 4 are closed.  Eight further modules, all axiom-clean and wired:

- `HTGeometry/PrincipalPartMonomial.lean` — `invLinPow α d = (x−α)^{-d}`, its principal-part
  coefficients (a Kronecker delta) and its regularity away from `α`.
- `HTGeometry/PrincipalPartDecomposition.lean` — `principalPartSum`, and
  **`exists_principalPart_decomposition`**: over an algebraically closed field every rational
  function is a polynomial plus a finite combination of principal-part monomials whose coefficients
  are exactly its `polePart`s.  (Proved by induction on the denominator degree, peeling
  `A = P(α)/Q₁(α)` at a root of multiplicity `m`; mathlib's `Polynomial.PartialFractions` is not in
  a usable shape for this.)
- `HTGeometry/PrincipalPartScale.lean` — `ratFuncScale q (invLinPow γ d) = q^{-d}·invLinPow (γ/q) d`.
- `HTGeometry/QBlockTelescoper.lean` — `blockCoeff`, its telescoping recursion and vanishing outside
  the window, and **`ratFuncScale_blockTelescoper_sub`**: a block with vanishing `q`-discrete
  residue is exactly a dilation coboundary.
- `HTGeometry/QSummabilityFromResidues.lean` — the block-removal induction
  `exists_dilationTelescoper_principalPartSum`, the polynomial case
  `exists_dilationTelescoper_polynomial`, and **`exists_dilationTelescoper_of_qOrbitResidue_vanish`**
  (Chen–Singer, converse half).
- `HTGeometry/QOrbitResidueTop.lean` — `polePart_eq_zero_of_poleOrder_lt`,
  `qOrbitResidue_eq_zero_of_natDegree_lt` and **`exists_top_qOrbitResidue`**: a nonzero residue has
  a top level, which is what the hypertranscendence criterion consumes.
- `HTGeometry/QPrimitiveExistence.lean` — `qPrimitive` and **`innerDilation_qPrimitive`**: the
  coefficientwise solution of `f(qx) − f(x) = r(x)`.
- `HTGeometry/QResidueSpectrum.lean` — `QSummable`, `qPrimitiveOf`, `qDefect`, and the card's
  items: **`hypertranscendentalOver_qPrimitiveOf`** (item 1),
  **`hypertranscendentalOver_qDefect`** (item 3 and `Spec_DA ⊆ H_r`),
  **`differentialAlgebraicOver_qDefect`** (`H_r ⊆ Spec_DA`), and
  **`qSummable_ratFuncScale_zpow_sub`** (`q^ℤ ⊆ H_r`).

**Still open on card 6:**
1. finiteness of `H_r/q^ℤ` and the bound `s!` — needs the residue support as a finite subset of
   `E_q` and the injection `H_r/q^ℤ → Sym(Supp)`;
2. the realization theorem: `r_K = ∑_{u ∈ K} x/(x−α_u)` has stabilizer exactly `K`;
3. the additive entire-plane corollary `Stab_DA(F) = ℤ + τℤ`.

### Card 6 — stabilizer and realization closed (2026-08-29)

Two further modules, axiom-clean and wired:

- `HTGeometry/QResidueStabilizer.lean` — **`qOrbitResidue_ratFuncScale`**
  (`ρ_(α,d)(S_a r) = a^{-d}·ρ_(aα,d)(r)`), `qOrbitResidue_eq_of_qSummable`, the residue support
  `residueSupport q r`, **`mul_mem_residueSupport`** (the stabilizer permutes the residue support),
  `residueSupport_subset_orbit_poles`, and **`qSummableStabilizer_eq_pole_div`**: every element of
  the stabilizer is a pole of `r` divided by a fixed residue-support point, times a power of `q`.
  This is the card's item 4/5 finiteness: `H_r` meets only finitely many `q`-orbits, and the map
  `a ↦ a·α₀` embeds `H_r/q^ℤ` into the (finite) set of residue-support orbits, so
  `|H_r/q^ℤ| ≤ s ≤ s!`.
- `HTGeometry/SimplePoleUnit.lean` — the normalized unit `x/(x−α)` and its complete principal-part
  calculus, the realization increment `simplePoleSum S = ∑_{α∈S} x/(x−α)`, the exact residue
  computation `ρ_(γ,1)(r_S) = γ` on the orbit union and `0` off it
  (**`residueSupport_simplePoleSum`**), and the capstone
  **`qSummable_ratFuncScale_simplePoleSum_sub_iff`**: for a finite set `S` of points in distinct
  `q`-orbits whose orbit union is division-closed, the summability stabilizer of `r_S` is *exactly*
  that orbit union.  This is the card's realization theorem: every finite subgroup of `E_q` is the
  exact DA scaling spectrum modulo `q^ℤ`.

**Card 6 status.**  Items 1, 2 (both directions), 3, 4, 5 and the realization theorem are Lean-proved
unconditionally.  The only remaining piece is the *additive entire-plane consequence*:
`F(z) = f(e^{2πiz})` is meromorphic on `ℂ`, and `Stab_DA(F) = {h : e^{2πih} ∈ H_r}`, so a one-point
residue class gives `Stab_DA(F) = ℤ + τℤ`.  That needs the analytic transfer of DA/HT through
`exp`/`log`; the corpus assets to use are `HTGeometry.MeroExponentialGauge`,
`HTGeometry.AnalyticJetFieldBridge` and `HTGeometry.MeromorphicRatFuncTranslation`.

## Card 3 — CLOSED (2026-08-29)

`GaloisForLFunctions.HTGeometry.hypertranscendental_no_classI_handle`.  The whole mathematical
content of the single-handle collapse lemma is class (I), and all five rows are now Lean-proved.

The Weierstrass addition-theorem citation is **eliminated**: differentiating `f(x+y) = P(f x, f y)`
in `y` at the origin gives the first-order autonomous equation `f' = Q(f)` directly, so no
classification of functions with addition theorems is needed
(`HTGeometry/AdditionTheoremCollapse.lean`).  The Padé row is closed by
`HTGeometry/RationalPadeCollapse.lean`: a Padé pair whose error has vanishing jets of every order is
exact for an entire function, giving a rational representation, which is an order-zero algebraic
differential equation.

Classes (II) and (III) of the card are a grading of which published theory covers which handle —
statements about the literature, not propositions about functions — so they have no formalizable
content.  Recorded in the card.

**Reusable:** `differentiallyAlgebraic_of_additionTheorem`, `differentiallyAlgebraic_of_rational`,
`differentiallyAlgebraic_of_padeStabilization`, `eq_zero_of_iteratedDeriv_zero` (an entire function
with vanishing jets at a point is zero), `biEval` (two-variable polynomial evaluation).

## Card 7 — the balanced gap reduced (2026-08-29)

`hypertranscendental-maximal-finite-horizon-galois-law` is blocked on primitivity of
`criticalGeometricMonodromy K m n` acting on `criticalGeometricSheet K m n`.  The corpus already
owns, unconditionally:

- `CriticalSchurCollisionSupportBound.exists_criticalGeometricMonodromy_isSwap` — the monodromy
  contains a literal transposition;
- `CriticalGeometricMonodromyJordan.criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap` —
  Jordan: primitive + a transposition ⟹ full symmetric group;
- `OccupationSubsetPrimitivity.criticalOccupationRootAction_isPreprimitive` — primitivity of the
  root action for `m ≠ n`.

**The balanced case is not a missing citation; it is one combinatorial statement.**  For `m = n` the
`S_(2m)`-action on `m`-subsets of `Fin (2m)` is imprimitive, with the complement pairing
`S ↦ Sᶜ` as its only nontrivial block system.  A transposition `(S T)` lying in a group that
preserves a nontrivial block system must have `S` and `T` in the *same* block (otherwise the image
of `S`'s block meets two distinct blocks).  Therefore:

> If the transposition supplied by `exists_criticalGeometricMonodromy_isSwap` swaps two sheets whose
> labels are **not** complementary `m`-subsets, the complement pairing is destroyed, the monodromy is
> primitive, and `(4)` follows.

Equivalently, in Johnson-graph language: conjugating the one transposition by the root action gives
all pairs `{S, T}` with `|S ∩ T| = j` fixed; that graph is connected for every `j` except `j = 0` in
the balanced case, where it is a perfect matching — exactly the complement pairing.

So card 7's remaining work is:
1. the combinatorial lemma "a transposition in a group preserving a nontrivial block system has both
   points in one block" (elementary, not in mathlib);
2. the classification "the complement pairing is the only nontrivial `S_(2m)`-invariant block system
   on `m`-subsets" (mathlib has the primitivity statement only for the unbalanced case);
3. the geometric input: the two colliding sheets at the Schur place carry non-complementary labels.

Items 1 and 2 are pure combinatorics and can be built directly; item 3 has to be read off the
`CriticalSchurCollisionInertia` / `CriticalSheetLabelInertiaOrbit` construction.

### Card 7 — item 1 is built (2026-08-29)

`HTGeometry/SwapBlockObstruction.lean` (axiom-clean, wired):
**`subsingleton_of_isBlock_of_swap`** — if `a ∈ B`, `b ∉ B` and the transposition `(a b)` lies in a
group for which `B` is a block, then `B` is a singleton; equivalently
**`mem_block_of_isBlock_of_swap`** — every transposition of a group with a nontrivial block lies
inside one block.

With it the balanced primitivity argument becomes purely combinatorial.  Let `G` contain the root
action of `S_(m+n)` and one transposition `(S₀ T₀)`, and let `B` be a block with `|B| ≥ 2`.  By the
lemma `S₀` and `T₀` lie in one block; conjugating by the root action, *every* pair `(S, T)` with
`|S ∩ T| = j₀ := |S₀ ∩ T₀|` lies in one block.  Blocks are therefore unions of connected components
of the Johnson-type graph `Γ_(j₀)` on `m`-subsets.  Hence:

> **`Γ_(j₀)` connected ⟹ the monodromy is primitive ⟹ `(4)`.**

`Γ_j` is connected for every `0 ≤ j < m` except the single balanced case `m = n`, `j = 0`, where it
is the perfect matching by complementation.  The two remaining pieces for card 7 are therefore:

1. **connectivity of `Γ_j`** for `m`-subsets of `Fin (m+n)`, `0 ≤ j < m`, excluding `(m = n, j = 0)`
   — a self-contained combinatorial theorem, not in mathlib;
2. the **geometric input** that the two sheets colliding at the Schur place carry labels with
   `|S₀ ∩ T₀| ≠ 0` when `m = n` — to be read off `CriticalSchurCollisionInertia` /
   `CriticalSheetLabelInertiaOrbit`.

### Card 7 — the connectivity lemma, fully specified

`Γ_j` on `m`-subsets of a type of card `N`, edges `|S ∩ T| = j`, is connected whenever `j < m` and
not (`N = 2m` and `j = 0`).  Proof to formalize:

1. **Complementation reduction.**  `S ↦ Sᶜ` is a bijection from `m`-subsets to `(N−m)`-subsets with
   `|Sᶜ ∩ Tᶜ| = N − 2m + |S ∩ T|`, so it carries `Γ_j` to `Γ_(N−2m+j)`.  Hence one may assume
   `2m ≤ N`.
2. **One swap at a time.**  If `|S ∩ S'| = m − 1`, write `S = A ∪ {x}`, `S' = A ∪ {y}`.  Choose `T`
   consisting of `j` elements of `A` together with `m − j` elements outside `A ∪ {x, y}`; this needs
   `N − (m+1) ≥ m − j`, i.e. `N ≥ 2m + 1 − j`, which holds for `j ≥ 1` when `2m ≤ N`, and for
   `j = 0` exactly when `N ≠ 2m`.  Then `|T ∩ S| = |T ∩ S'| = j`, so `S ~ T ~ S'`.
3. **Johnson connectivity.**  Any two `m`-subsets are joined by a chain of one-element swaps
   (induction on `m − |S ∩ S'|`), so step 2 propagates to all pairs.

Combined with `subsingleton_of_isBlock_of_swap` (built) and
`criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap` (owned), only the geometric input —
that the colliding sheets have `|S₀ ∩ T₀| ≠ 0` in the balanced case — then remains.

## Remaining cards after 2026-08-29

| # | Card | The single classical theorem still to build |
|---|---|---|
| 1 | combination-mode-reducibility-baker-bridge | effective Baker–Wüstholz (explicit constants) |
| 7 | hypertranscendental-maximal-finite-horizon-galois-law | `Γ_j` connectivity + the non-complementary collision |
| 8 | indeterminate-moment-fiber-prevalent-translation-ht | the Nevanlinna N-extremal matrix; prevalence |
| 10 | poincare-constraint-order-recession | Bergweiler's Poincaré hypertranscendence (Nevanlinna theory) |
| 11 | projective-horizon-hankel-secant-stratification | Hankel determinantal rings: codimension, singular locus, rational singularities (no CM theory in mathlib) |
| 12 | projective-ht-generic-pv-curvature-core | differential Picard–Vessiot theory with group `SL_N` (mathlib has none) |

Card 7 is the closest: its remaining pieces are elementary combinatorics plus one reading of an
existing corpus construction.

### Card 7 — the whole combinatorial side is now Lean-closed (2026-08-30)

Three new modules, axiom-clean and wired:

- `HTGeometry/SwapBlockObstruction.lean` — `subsingleton_of_isBlock_of_swap`,
  `mem_block_of_isBlock_of_swap`.
- `HTGeometry/JohnsonGraphConnected.lean` — `JohnsonStep`, the one-swap path
  `reflTransGen_of_inter_card_pred`, **`reflTransGen_johnsonStep`** (the fixed-intersection graph on
  `m`-subsets is connected whenever `j < m`, `2m ≤ N`, and not (`j = 0` and `N = 2m`)),
  `swap_mem_of_reflTransGen` (transpositions along a connected relation generate every
  transposition), `eq_top_of_forall_swap_mem`, and **`eq_top_of_johnsonSwaps`**.
- `HTGeometry/FixedIntersectionTransitive.lean` — `permOfFiberCardEq` (a permutation matching two
  maps with equal fibre cardinalities), the four-block index, **`exists_perm_image_pair`**
  (`S_N` is transitive on ordered pairs of `m`-subsets with a fixed intersection size),
  `cardImagePerm`, and the capstone

  > **`eq_top_of_rootAction_of_swap`** — a group of permutations of `m`-subsets that contains the
  > induced action of the ambient symmetric group together with *one* transposition of a pair
  > meeting in `j` points, with `j < m`, `2m ≤ N` and not (`j = 0` and `N = 2m`), is the **full**
  > symmetric group.

This bypasses primitivity and Jordan entirely, and it covers the balanced case `m = n` that the
`OccupationSubsetPrimitivity` route cannot reach.  Nothing combinatorial is left.

**What card 7 still needs, and it is now exactly two geometric facts about the corpus's own
construction:**

1. `criticalGeometricMonodromy K m n` contains the induced root action — the corpus states
   `criticalMonodromy_isPreprimitive_of_rootAction_le` with that containment as a *hypothesis*, and
   never discharges it for the actual monodromy;
2. the two sheets colliding at the Schur place (`exists_criticalGeometricMonodromy_isSwap`) carry
   labels whose intersection is nonempty when `m = n`.

Both live inside the `CriticalSheetLabelInertiaOrbit` / `CriticalSchurCollisionInertia` stack.  With
them, `eq_top_of_rootAction_of_swap` gives statement `(4)` immediately, and the rest of card 7
(degree, atomicity, radical threshold) is already discharged in the corpus.

## Next-session brief (2026-08-30)

Ten of the sixteen cards in this folder are at stage 3.  The six that remain are each blocked on one
named piece of mathematics; below is exactly where each stands and what to build first, so no time is
spent re-deriving the analysis.

### Card 7 — closest.  Two geometric facts.
Combinatorics **complete** (`SwapBlockObstruction`, `JohnsonGraphConnected`,
`FixedIntersectionTransitive`).  `criticalHorizonOccupationStates m n` is *definitionally*
`{S : Finset (Fin (m+n)) // S.card = m}` — the very subtype `eq_top_of_rootAction_of_swap` is stated
for — so statement `(4)` follows from:
1. `criticalGeometricMonodromy K m n` contains the induced root action.  The corpus never discharges
   this: `criticalMonodromy_isPreprimitive_of_rootAction_le` takes it as a hypothesis, and the
   occupation-state modules (`PostcriticalEscapeUnconditional`, `DeformedFibreLowerBound`,
   `ProjectiveHorizonPostcriticalRigidity`) are a *parallel* development to the Galois-theoretic
   `criticalGeometricSheet` one — **the sheet ↔ occupation-label bridge does not exist yet and is
   the real work**;
2. the two sheets colliding at the Schur place have labels with nonempty intersection when `m = n`.

### Card 10 — two hypotheses plus Bergweiler.
`PoincareRecession.exactDifferentialOrder_iterate_of_separation` already gives `ord_DA(f^[n]) = n`
and `exactDifferentialOrder_poincareApprox` already transports it along the affine reparametrisation,
so item 1 of the card needs only its two hypotheses discharged for iterates of a transcendental
entire solution of an autonomous first-order ADE: `StepSeparation` (a growth separation) and the
elimination step `helim`.  Item 2 (`φ` is hypertranscendental) is Bergweiler's theorem.  Note that
DA does *not* bound growth (`exp∘exp` satisfies `y y'' = y y' + y'²`), so no cheap growth argument
exists; mathlib now has value-distribution theory
(`Mathlib/Analysis/Complex/ValueDistribution/`: proximity, log counting, characteristic function,
the First Main Theorem, Cartan) but not the Second Main Theorem, which is the natural first build.

### Card 8 — the probe is card 13's machinery; the fibre is not.
The probabilistic core ("a compact product probe makes the full-translation-HT locus have
probability one") is exactly `RandomAffineJetPacketFreeness.ae_translationOrbit_no_polynomialDifferentialRelation`
plus `HasAbsolutelyContinuousFiniteAffineJetLaws`, already built and instantiated twice for card 13.
What is missing is the *source*: Nevanlinna's `N`-extremal measures for an indeterminate Hamburger
moment problem and the Cauchy-transform jet controllability.  Corpus assets: `NevExtremalFamily`,
`CauchyMomentFlatness`, `MomentFunctionalPositivity`, `StieltjesTransformPick`.

### Card 11 — needs commutative algebra mathlib does not have.
Codimension `2k−1` and `Sing(C_k) = C_(k+1)` are dimension/singular-locus statements about Hankel
determinantal rings, and the card also asserts normality, Cohen–Macaulayness and rational
singularities (Conca–Mostafazadehfard–Singh–Varbaro).  mathlib has Krull dimension but no
Cohen–Macaulay theory and no rational singularities.  The rank/recurrence core is already formalized
(`ProjectiveHorizonHankelSecant`).

### Card 12 — needs differential Picard–Vessiot theory.
mathlib has none; the corpus has only the *difference* theory
(`DifferenceSystemPicardVessiot`, `ParameterizedPicardVessiotExistence`).  Building differential PV
with group `SL_N` is the prerequisite.

### Card 1 — needs effective Baker–Wüstholz.
The corpus owns qualitative Baker only (`general-baker-closed`); the card needs explicit constants.

### Card 1 — Part 1 closed (2026-08-30)

`HTGeometry/DirichletBoxLinearForm.lean` (axiom-clean, wired) proves Dirichlet's box principle for a
nonnegative linear form (`exists_small_linear_form`) and the card's Part-1 no-go
(`not_polynomially_diophantine`): with the support size free, no fixed-exponent Diophantine
condition can hold, because bounded-entry modes make `|m·ℓ|` arbitrarily small.  Together with the
already-formalized Lemma R(i) (`DiagonalModeDivision`), the only remaining classical import on
card 1 is **Lemma R(ii)**, the effective Baker–Wüstholz bound.

### Card 1 — §3 and §4 closed too (2026-08-30)

- `HTGeometry/HankelDetTotalDegree.lean` — `totalDegree_hankelDet_le`: the `d × d` Hankel
  determinant has total degree `≤ d` in the power sums, i.e. **combination-mode support ≤ d** (§3).
- `HTGeometry/IntegerLogGap.lean` — `gap_div_le_abs_log_div`: `|a − b|/max(a,b) ≤ |log(a/b)|` for
  distinct positive integers, the controlling estimate of §4.

Everything on card 1 is now formalized except **Lemma R(ii)**.  An important sharpening recorded
here: the integer gap gives `|∑ m_p log p| ≥ (∏ p)^{−H(m)}` — *exponential* in `H(m)` — which makes
`‖h‖_{L²} < ∞` for every analytic `g` of radius `ρ > log ∏ p`.  Baker's polynomial bound
`≥ γ·H(m)^{−κ}` is needed exactly to reach all `ρ > 0`.  So the residual dependency is not "an
estimate" in general but specifically the *effective* Baker–Wüstholz theorem, whose formalization
needs Baker's method (auxiliary function, extrapolation, zero estimate) and is a project of its own.

### Cards 11 and 12 — first pieces landed (2026-08-30)

- `HTGeometry/HankelSecantRank.lean` (card 11) — `secantHankel_eq`: a coefficient window that is a
  sum of `t` geometric sequences has Hankel matrix `V · diag(c) · Vᵀ` with `V` the `t`-column
  Vandermonde; hence **`rank_secantHankel_le`** (`rank ≤ t`) and `corank_secantHankel_ge`
  (`corank ≥ m − t`).  This is the parametrized inclusion "spans of `t` points of the rational
  normal curve ⊆ the Hankel determinantal locus", one half of the card's catalecticant
  identification.  The reverse inclusion is the corpus's rank/recurrence core; what is still missing
  is the *dimension* theory (codimension `2k−1`, `Sing(C_k) = C_(k+1)`) and the
  normal/Cohen–Macaulay/rational-singularity assertions, for which mathlib has no Cohen–Macaulay
  theory at all.
- `HTGeometry/ProjectiveFrameCompanion.lean` (card 12) — `vecDeriv`, `frameMatrix`,
  `companionMatrix`, and **`deriv_frameMatrix`**: for a lift with `δ^N v = ∑_j q_j δ^j v`, the moving
  frame `[v, δv, …, δ^{N−1}v]` satisfies `δM = M·A` with `A` the companion matrix — the card's item
  (3), that the frame is a fundamental matrix of the companion system — together with `frameSL`,
  which places it in `SL_N` once the normalized Wronskian is `1`.  Items (4) and (5) need
  differential Picard–Vessiot theory, which mathlib does not have.

### Card 8 — the finite-support control block is built (2026-08-30)

`HTGeometry/MeanZeroAnnihilator.lean` — **`eq_of_annihilates_meanZero`**: a coefficient sequence
whose functional kills every finitely supported mean-zero direction is constant, proved by testing
against `δ_p − δ_q`.  This is the card's "Finite-support control blocks" step.

The card's *probabilistic* core is already owned and needs no new work: the probe conclusion
`Π_B({w : x + w ∈ G}) = 1` for every recentring `x` is exactly
`RandomAffineJetPacketFreeness.ae_translationOrbit_no_polynomialDifferentialRelation` together with
`FiniteJetLawDeterministicGauge.ae_translationOrbit_no_polynomialDifferentialRelation_add_const`
(the deterministic-recentring form), both formalized during the card-13 work.  What remains is
purely the *source*: Nevanlinna's `N`-extremal measures for an indeterminate Hamburger moment
problem, and the Cauchy-transform jet controllability that feeds
`HasAbsolutelyContinuousFiniteAffineJetLaws`.

### Card 10 — the residual hypotheses, precisely

`PoincareRecession.exactDifferentialOrder_iterate_of_separation` needs exactly two things for
iterates of a transcendental entire `f` satisfying a first-order autonomous ADE:

1. `PrefixStateIndependence.StepSeparation (fun j => f^[j]) (f^[m])` — for every nonzero polynomial
   `A` in the earlier iterates and every `c ≥ 0`, a point `z` where `|A|` is bounded below by some
   `ε > 0` while `posLog‖f^[m] z‖` exceeds `c·(1 + ∑_j posLog‖f^[j] z‖ + posLog ε⁻¹)`.  This is a
   growth statement about iterates of a transcendental entire function (`M(r, f∘g)` versus
   `M(r, g)`), and it is a *for some `z`* statement, which is the easy direction.
2. the elimination step `helim`, a differential-elimination statement about `statePoly`.

Item 2 of the card (`φ` is hypertranscendental) is Bergweiler's theorem.  Note DA does **not** bound
growth — `exp∘exp` satisfies `y·y'' = y·y' + y'²` — so no cheap growth argument replaces it.

### Card 11 — the catalecticant identification, generic case (2026-08-30)

`HTGeometry/RecurrenceGeometricBasis.lean` — `geomCombination`, `geomMap`, `geomMap_injective`
(independence of geometric sequences by Vandermonde), and
**`exists_geomCombination_of_distinct_roots`**: every solution of a linear recurrence whose
characteristic polynomial has as many distinct roots as its order is a combination of the
corresponding geometric sequences.

Together with `HankelSecantRank.rank_secantHankel_le` this closes **both directions** of the
catalecticant identification in the generic (distinct-root) case:

> a coefficient window has Hankel rank `≤ t` and a recurrence with `t` distinct characteristic roots
> ⟺ it is a sum of `t` geometric sequences, i.e. a point of the `t`-secant of the rational normal
> curve.

The corpus already owns the rank ⟺ recurrence half (`ProjectiveHorizonHankelSecant`).  What remains
on card 11 is the *confluent* (repeated-root) closure and, above all, the dimension and singularity
theory — codimension `2k−1`, `Sing(C_k) = C_(k+1)`, normality, Cohen–Macaulayness and rational
singularities — for which mathlib has no Cohen–Macaulay theory.

### Card 12 — the differential Picard–Vessiot foundation is built (2026-08-30)

Seven new modules, all axiom-clean and wired into `GaloisForLFunctions.HTGeometry`.  mathlib has no
differential Galois theory at all and the corpus had only the *difference* side, so every layer here
is new.

- `HTGeometry/DifferentialDeltaSimple.lean` — `IsDeltaIdeal`, `isDeltaIdeal_span_singleton_of_const`,
  **`isNilpotent_deriv_of_pow_eq_zero`** (the derivative of a nilpotent is nilpotent in a
  `ℚ`-algebra: `x^{n-k}(x′)^{2k+1} = 0` by induction), `isDeltaIdeal_nilradical`,
  **`exists_maximal_isDeltaIdeal`** (Zorn), `IsDeltaSimple`, `isReduced_of_isDeltaSimple`,
  `deltaConstantsSubring`, and **`isField_deltaConstantsSubring_of_isDeltaSimple`**.
- `HTGeometry/DifferentialDeltaQuotient.lean` — `isDeltaIdeal_comap` and
  **`isDeltaSimple_quotient_of_maximal`** (the corpus already owned the descended derivation
  `quotDeriv` / `quotientDifferential`).
- `HTGeometry/DifferentialSystemPicardVessiot.lean` —
  **`exists_deltaPicardVessiot_of_fundamentalMatrix`**: a nontrivial differential ring carrying an
  invertible fundamental matrix of `δ Y = B Y` has a `δ`-simple quotient in which the matrix is still
  an invertible fundamental matrix and whose constants form a field.
- `HTGeometry/DeterminantDerivation.lean` — **`deriv_finsetProd`** (Leibniz for a finite product),
  **`deriv_det`** (Jacobi's formula for a derivation: differentiate one column at a time),
  **`deriv_det_of_system`** (`δ det M = det M · tr A` when `δM = MA`) and
  **`trace_eq_zero_of_det_eq_one`**.  All four are mathlib gaps.
- `HTGeometry/ProjectiveFrameInvariance.lean` — `trace_companionMatrix`,
  **`top_coefficient_eq_zero_of_det_eq_one`** (the card's claim that the missing `δ^{N-1}v`
  coefficient of the normalized Wilczynski relation vanishes), `vecDeriv_mulVec`,
  `frameMatrix_mulVec`, **`rel_mulVec_of_rel`** (a constant gauge of the lift satisfies the same
  relation) and **`coefficients_unique`** (an invertible frame determines the coefficients).
  Together these are card item **(1)**, first half: the `q_j` are projective differential invariants.
- `HTGeometry/DifferentialMatrixGauge.lean` — `matDeriv`, `matDeriv_mul`, `matDeriv_const_mul`,
  `matDeriv_map`, `matDeriv_gauge`, and **`exists_constantGauge_of_differentialAut`**: a differential
  automorphism fixing the system matrix moves a normalized fundamental matrix by left multiplication
  with a *constant* matrix of determinant one.  This is the Galois cocycle, i.e. the embedding
  `Gal ↪ SL_N(C)`.
- `HTGeometry/GenericSpecialLinearTorsor.lean` — the generic torsor.  `genericDerivation` makes the
  generic matrix solve `δ Y = Y A`; because `A` is traceless the Wronskian is a constant
  (`deriv_det_fundamentalMatrix`), so `det Y − 1` generates a differential ideal
  (`isDeltaIdeal_slRelation`) and the quotient `genericSL I N` is a differential ring in which the
  generic matrix is a fundamental matrix of determinant one.  `gaugeHom`/`gaugeAut` realize every
  constant gauge of determinant one as a differential automorphism over the base
  (`gaugeAut_deriv`, `map_gaugeAut_torsorMatrix`), the identity point `slEvalOneQuot` splits the base
  inclusion and gives **`gaugeAut_injective`**, and the capstones are
  **`generic_specialLinear_torsor`** and **`exists_gaugeCocycle_of_differentialAut`**.

**Card 12 status.**  Item (3) was already Lean-closed (`ProjectiveFrameCompanion`).  Item (1) first
half (invariance) and the normalization claim of `(2)`–`(3)` are now closed.  Item (4) is closed in
both directions modulo the card's own genericity hypothesis: every constant gauge in `SL_N(C)` is a
differential automorphism of the generic torsor, distinct gauges act differently, and conversely
every differential automorphism over the base is such a gauge
(`exists_gaugeCocycle_of_differentialAut`).

**Still open on card 12:**
1. joint differential independence of the `q_j` (item 1, second half) — needs the `dtrdeg` chain:
   a Picard--Vessiot extension has differential transcendence degree `0` over its base, so
   `dtrdeg(I/C) = dtrdeg(F/C) = N−1`, and a spanning family of size `dtrdeg` in the differential
   matroid is independent.  Corpus assets: `DifferentialTranscendenceDegree`,
   `ConstraintRelativity.CofinalRankTransfer`, `DifferentialFamilyMatroid`,
   `DifferentialSubfieldTransfer`.
2. item (2), `I = F^{PGL_N(C)}` — the Galois correspondence; needs `δ`-simplicity of the generic
   torsor ring and "no new constants", which is Seiss's theorem.
3. items (5) and (6) — the center/unipotent fixed-field statements, which the card itself derives
   from the horizon-building theorem of `projective-horizon-tits-building`.

### Card 12 — item (1) second half reduced to one hypothesis (2026-08-30)

`HTGeometry/ProjectiveCurvatureIndependence.lean` (axiom-clean, wired):

- `frameJet`, **`deriv_frameJet`** — the jets `v_i, δv_i, …, δ^{N−1}v_i` of one component of a
  normalized lift are the coordinates of the first-order system with matrix `(companionMatrix q)ᵀ`;
- **`differentialAlgebraicOver_lift_component`** — every component of the lift is therefore
  differentially algebraic over the curvature field (via the corpus's
  `differentialAlgebraicOver_finiteLinearSystem_coordinate`);
- **`curvature_differentialIndependent`** — a curvature family over which the source is
  differentially algebraic and whose size does not exceed `dtrdeg(F/C)` is differentially
  independent.

This is the card's dtrdeg argument in Lean: the Picard--Vessiot direction "a finite-dimensional
constant Galois group does not lower differential transcendence degree" is replaced by the *exact*
statement that the frame satisfies a linear system over `I`, hence adds no differential
transcendence.  The one hypothesis still supplied from outside is `hspan` — that every element of
the source field is differentially algebraic over `I` — which needs the finite-family form of
"the differential field generated by differentially algebraic elements is differentially algebraic";
the corpus owns only the singleton form
(`RGClockBetaEquivalence.differentialAlgebraicOver_of_mem_adjoin`,
`FiniteDifferentialCircuitBoundary.differentialAlgebraicOver_of_mem_differentialAdjoin_singleton`).
The differential matroid layer (`DifferentialFamilyMatroid`, `WickContractedMatroidPersistence`) is
the natural place to get it.

### Card 12 — item (1) is CLOSED (2026-08-30)

The `hspan` hypothesis is gone.  `ProjectiveCurvatureIndependence` now also owns:

- **`differentialAlgebraicOver_differentialAdjoin_union`** — transitivity of differential
  algebraicity over generated differential fields, obtained from the corpus's unconditional Kolchin
  closure law (`differentialMatroid_mem_closure_iff_differentialAlgebraicOver_differentialAdjoin`)
  plus matroid closure idempotence.  Reusable: it is the finite-family form of "the differential
  field generated by differentially algebraic elements is differentially algebraic", which the
  corpus previously owned only for a single element.
- **`forall_differentialAlgebraicOver_curvature`** and its general form
  **`forall_differentialAlgebraicOver_of_curvature_mem`** — the normalized lift adds no differential
  transcendence over any generating set containing the curvatures (so the `q_{N-1} = 0` slot is
  harmless).
- **`curvature_differentialIndependent_of_lift`** — the card's item (1): for a differential-generic
  source (`dtrdeg(F/C) ≥` the number of curvatures) with the source generated by the curvatures and
  the lift, the curvature tuple is differentially independent over the constants.

Card 12 items (1), (3) and (4) are now Lean-closed; (2), (5), (6) need the differential Galois
correspondence (δ-simplicity of the generic torsor ring and Seiss's no-new-constants theorem, then
the center/unipotent fixed fields).

### Card 8 — the recorded blocker is stale (2026-08-30)

The ledger and the card both say card 8 is blocked on "the Nevanlinna `N`-extremal matrix (the parent
card in `nad/` is blocked on the same input)".  Both statements are out of date:

- the parent card `indeterminate-moment-fiber-maximal-translation-ht` is at **stage 3**
  (`docs/drafts/pipeline/3-formalized/nad/`), with capstone
  `analyticNevCarrierFamily_maximalTranslationPhase_dense_residual`;
- the classical `N`-extremal Nevanlinna family is **constructed**, not assumed:
  `HTGeometry.nevExtremalFamily` builds every field of `ClassicalNevanlinnaExtremalFamily` from the
  moment sequence (matrix from the orthogonal polynomials, leaves from quasi-orthogonal quadrature,
  carriers from the denominator fibres, moments from quadrature exactness, weak continuity from
  tightness), and `nevExtremalFamily_atoms` identifies the weights as Christoffel limits;
- pairwise mutual singularity of leaves at distinct parameters is owned:
  `FiberClosed.mutuallySingular_leaf` (via the exact label recovery
  `map_projectiveLabel_leaf`), and `BoundaryBarycenterSpectralTransport.measureBarycenter_mutuallySingular`
  transports it to barycenters;
- the whole full-rank-witness machinery for maximal translation differential freeness of a weighted
  boundary carrier is owned: `BoundaryCarrierTranslationFreeness`
  (`MaximalTranslationFullRankWitness`, `maximalTranslationDifferentialFree_of_fullRankWitness`,
  `probabilityCarrierExpandedFullRankWitness_weightedBoundaryProbabilityCarrier`,
  `hypertranscendental_weightedBoundaryProbabilityCarrierCauchy`),
  `NevanlinnaBoundaryFaceMaximalTranslation` (the dense/residual phase) and
  `StratifiedParametricAvoidance` (the finite-dimensional stratified transversality engine).

**What card 8 actually still needs** is only its own upgrade from *residual* to *locally prevalent*:

1. the mean-zero chart: `E_η = {v ∈ ℓ^∞ : ∑ η_n v_n = 0}` and `X_δ = {1 + v : ‖v‖_∞ < δ}`, as a
   submodule of the `L^∞(η)` density space the corpus already uses
   (`weightedBoundaryProbabilityCarrier` takes `Lp ℝ ⊤ eta`);
2. the compact product probe `V = ∑_j a_j ∑_k X_{j,k} v_{j,k}` with `∑_j a_j d_j < r`: a uniformly
   convergent random series over `Ω = ∏_j [-1,1]^{d_j}` with product Lebesgue law, hence a
   compactly supported Borel probability on `E_η`;
3. the a.s. full-rank statement after every deterministic recentring.  The natural engine is the
   card-13 architecture — an absolutely continuous *finite* block plus a nonzero
   analytic/polynomial obstruction — with the finite block supplied by the finite-support mean-zero
   controllability already proved in `MeanZeroAnnihilator.eq_of_annihilates_meanZero`;
4. the definition of prevalence and the local-prevalence capstone, plus the convex-insertion
   corollary `ν = (1−ε)μ₀ + ε μ_{x+V}`.

### Card 8 — the prevalence engine is built (2026-08-30)

Two new modules, axiom-clean and wired.  Together they are the exact upgrade of the corpus's Baire
avoidance machinery to a measure statement, which is all that separates card 8 from its stage-3
parent.

- `HTGeometry/StratifiedParametricPrevalence.lean` —
  **`volume_parameter_preimage_finite_stratification_eq_zero`**: the bad parameter set of a
  stratified parametric family over a Euclidean probe block is Lebesgue *null*.  The corpus already
  bounds its Hausdorff dimension by `finrank − 1`
  (`dimH_parameter_preimage_finite_stratification_le_pred`); combining that with
  `hausdorffMeasure_pi_real` and `measure_zero_of_dimH_lt` replaces
  `dense_compl_of_dimH_lt_finrank` by a null statement.  Consequences:
  **`measure_parameter_preimage_finite_stratification_eq_zero`** (every probe law absolutely
  continuous for Lebesgue measure), **`measure_compactConfigurationAvoidance_eq_one`** (compact-patch
  avoidance has probability one, with no measurability hypothesis on the avoidance set), and
  **`measure_compactConfigurationAvoidance_smoothAffineControlFamily_eq_one`** — the same statement
  for the corpus's affine finite-probe families `F(v,h) = base h + direction h v`, whose
  surjectivity hypothesis is exactly finite-block controllability.
- `HTGeometry/PrevalentSets.lean` — `CompactProbe`, `PrevalentOn`, `Prevalent`, `PrevalentOn.mono`,
  `PrevalentOn.subset`, **`prevalentOn_iInter`** (a countable family tested by one probe), and
  `CompactProbe.map`.  Prevalence is defined by *null complement*, so no measurability of the tested
  set is ever needed — which matters because the maximal-translation phase is defined by an
  uncountable quantifier.

**Remaining for card 8:** assemble these against the parent's compact-patch call sites
(`NevanlinnaTranslatedExpandedEvaluationCompactPatch`,
`WeightedCauchyTranslatedExpandedEvaluationCompactPatch`,
`NevanlinnaNoncriticalProjectiveCompactPatch`), i.e. replace
`dense_compactConfigurationAvoidance_of_dense_submodule_perturbations` by the probe-measure version,
build the mean-zero `L^∞(η)` chart and the convergent product probe
`V = ∑_j a_j ∑_k X_{j,k} v_{j,k}`, and conclude with `prevalentOn_iInter` over the countable
enumeration of relation patterns and patches.

### Card 8 is CLOSED and promoted to stage 3 (2026-08-30)

Two new modules finish the residual-to-prevalent upgrade, and the card moved to
`3-formalized/not_new_scientific_knowledge/03-ht-translation-projective-geometry/`.

- `HTGeometry/PrevalentCountableIntersection.lean` — general theory, a genuine mathlib gap.
  Mathlib has `Measure.infinitePi` but no coordinate/complement splitting of it, and no prevalence
  notion.  Built here: `infinitePi_indepFun_eval_restrictCompl`,
  `infinitePi_map_eval_restrictCompl`, `infinitePi_null_of_slice_null` (the Fubini step obtained
  from `iIndepFun_infinitePi` + `indep_iSup_of_disjoint` on the singleton/complement split of the
  index set); the explicit compact product probe `productProbeMap` with `unitTruncate`,
  `blockProbeLaw`, `isCompact_range_productProbeMap`, `productProbeMap_split`,
  `norm_productProbeMap_le`; the block null law `blockProbeLaw_block_null`; and the prevalence
  capstones `BlockPrevalentRadius`, `blockPrevalentRadius_iInter_of_blockControl_scalable`,
  `globalWitness_blockPrevalentRadius_of_sigmaCompact_family`, plus the bridge
  `Prevalent.of_blockPrevalent` to the `CompactProbe` definition of `PrevalentSets.lean`.
  **Nothing about the ambient Banach space is needed beyond completeness** — the null sets are sets
  of *parameters*, so no measurable structure on the tangent space is ever required.  That is what
  makes the statement usable on `LinearMap.ker frozen.toLinearMap ≤ Lp ℝ ⊤ mu`.
- `HTGeometry/NevanlinnaPrevalentFullRankWitness.lean` — the instantiation:
  `blockControlled_finite_atlas`,
  `compact_injectiveShiftPatch_blockControlled_completeAtlas_actualNevanlinna`,
  `countablePatterns_actualNevanlinna_fullRankWitness_blockPrevalentRadius`,
  `countablePatterns_actualNevanlinna_relationFree_blockPrevalentRadius`,
  `countablePatterns_actualNevanlinna_relationFree_blockPrevalent`, and the moment-fibre cloud
  corollary `convexInsertion_actualNevanlinna_relationFree_blockPrevalentRadius`.

Method note for the remaining cards: the corpus's dense/residual capstones are systematically
upgradable to prevalence by replacing `globalWitness_dense_residual_of_sigmaCompact` with
`globalWitness_blockPrevalentRadius_of_sigmaCompact_family`, provided the per-patch density proof
already produces an *explicit* finite probe (the `..._has_uniform_finiteProbe` family) rather than
a bare `Dense` statement.

### Card 12 — the generic-matrix differential Galois torsor (2026-08-30)

New module `HTGeometry/GenericMatrixDifferentialGalois.lean` (axiom-clean, wired).  It realizes the
card's generic Picard--Vessiot situation *concretely*, on the corpus's free differential rational
field, so that **no δ-simplicity and no no-new-constants theorem is needed**: the corpus already
proves `Differential.ContainConstants C (JetField C ι)` in `JetFieldConstantKernel.lean`.

- `genericJetMatrix`, `det_genericJetMatrix_ne_zero`, `isUnit_det_genericJetMatrix` — the generic
  matrix `Y` of jet coordinates is invertible (evaluate at the identity matrix).
- `genericSystemMatrix` `A = Y⁻¹ δY` and `matDeriv_genericJetMatrix` — `Y` is a fundamental matrix
  of its own system, tautologically.
- `matDeriv_one`, `matDeriv_inv` — matrix calculus supplements (`δ(M⁻¹) = −M⁻¹ (δM) M⁻¹`).
- `genericSliceMatrix` `B_k = Y⁻¹ Y^{(k)}` with `genericSliceMatrix_succ`:
  `B_{k+1} = δB_k + A·B_k`.  Every jet of `Y` is `Y` times a differential polynomial in `A`.
- `leftTranslationIndexMatrix`, `leftTranslationPolyEquiv`, `leftTranslationFieldEquiv` — the
  jetwise substitution `x_{ij}^{(m)} ↦ (Z Y^{(m)})_{ij}` for a constant invertible `Z`, built on the
  corpus's `DifferentialLinearChangeAutomorphism` with the index matrix `Z ⊗ 1`.
- `leftTranslationFieldEquiv_deriv` — it is a **differential** automorphism of the free
  differential rational field (conjugate-derivation plus `fractionRing_derivation_ext`).
- `map_leftTranslationFieldEquiv_genericJetMatrix` — it multiplies `Y` on the left by `Z`.
- **`map_leftTranslationFieldEquiv_genericSystemMatrix`** — it therefore *fixes* `A`.  The whole
  general linear group of constants acts on the generic torsor over its own invariant base.

**What remains for card 12 items (2), (5), (6)** is the fixed-field half, i.e. the slice argument
`E^{GL_N(C)} = C⟨A⟩`.  Its two inputs are (i) algebraic independence of the slice coordinates
`{Y_{ij}} ∪ {(B_k)_{ij}}` over `C`, provable by exhibiting the mutually inverse substitutions
`X_{((i,j),k)} ↦ (Y·X_k)_{ij}` and `X_{((i,j),k)} ↦ (Y⁻¹X_k)_{ij}` on `JetPoly[1/det]`, and (ii)
`L(Y)^{GL_N(C)} = L` for a matrix of independent variables over `L`, provable by Zariski density
of `GL_N(C)` in `GL_N` over an infinite field followed by the substitution `Z ↦ W Y⁻¹`.

### Card 12 — generic-gauge coinvariance is CLOSED (2026-08-30)

Two more modules, both axiom-clean and wired.

- `HTGeometry/SubfieldPointVanishing.lean` — **`mvPolynomial_eq_zero_of_eval_subfield_eq_zero`**: a
  polynomial over `L` vanishing at every point of an infinite subfield `C` is zero (coefficient push
  through a `C`-linear functional plus `MvPolynomial.funext`).  This is the Zariski-density input of
  every rational-point separation argument.
- `HTGeometry/GenericGaugeCoinvariance.lean` — the **hard half of the differential Galois
  correspondence for the generic torsor**, with no δ-simplicity, no no-new-constants theorem and no
  faithfully flat descent:
  * `slPointPoly`, `slPoint`, `map_slPoint_torsorMatrix` — evaluation of `genericSL I N` at any
    determinant-one matrix over any commutative ring, i.e. the gauge action in its functorial form;
  * `genericGauge I N := genericSL (genericSL I N) N` — the *generic gauge*: a second free
    determinant-one matrix over the torsor ring;
  * `genericGaugeCoaction` `Y ↦ g·Y`, and `genericGaugeEval` — the specialisation `g ↦ Y⁻¹`, legal
    because the generic matrix has determinant one and is therefore invertible over the torsor ring
    itself;
  * **`genericGaugeEval_coaction`** — that specialisation turns the coaction into evaluation at the
    identity point;
  * **`mem_range_slBase_of_genericGauge_invariant`** — an element fixed by the generic gauge lies in
    the base ring.

**Remaining for card 12 item (2)**: the density step, i.e. "fixed by every constant gauge over the
algebraically closed constants" ⟹ "fixed by the generic gauge".  Two routes:
(a) Nullstellensatz — needs `det − 1` irreducible and the vanishing-ideal computation;
(b) **transvections** — for each pair `i ≠ j` the one-parameter family `E_{ij}(s)` has determinant
one for a *free* parameter `s`, so invariance for all `s ∈ C` upgrades to invariance for a free `s`
by the univariate root count alone (no Nullstellensatz), and then `Y⁻¹` over `Frac(genericSL I N)`
is a product of transvections because `SL_N` of a field is generated by them.  Route (b) is the one
to try first.

### Card 12 — item (2) is CLOSED (2026-08-30)

Three more modules, all axiom-clean and wired.  The route is the **slice specialisation**, which
replaces invariant theory, Nullstellensatz and faithfully flat descent by one substitution.

- `HTGeometry/GenericMatrixDifferentialGalois.lean` (earlier today) — the generic matrix `Y` over the
  corpus's free differential rational field `E = JetField K (Fin N × Fin N)`, its system matrix
  `A = Y⁻¹δY`, the slice recursion `B_{m+1} = δB_m + A·B_m`, and the constant left translations
  `σ_Z` as *differential* automorphisms fixing `A`.
- `HTGeometry/GenericMatrixFixedField.lean` — **`mem_sliceSubfield_of_leftTranslation_invariant`**.
  Write `u = p/q`, introduce a generic gauge matrix `z` of `N²` free variables and set
  `Δ = p(zY)·q − p·q(zY)`.  Constant invariance kills `Δ` at every `K`-point of `GL_N`; multiplying
  by `det z` kills it at every `K`-point of the whole matrix space, so `Δ = 0` by
  `SubfieldPointVanishing.mvPolynomial_eq_zero_of_eval_subfield_eq_zero`.  Substituting
  `z ↦ w·Y⁻¹` turns `Y^{(m)}` into `w·B_m`, and a `K`-point `w` with `q(wB) ≠ 0` (density again)
  exhibits `u` as a ratio of two elements of the slice subfield.
- `HTGeometry/GenericCurvatureInvariantField.lean` — `genericSliceMatrix_mem_curvatureField` (the
  slice recursion inside `differentialAdjoin K (systemEntries K N)`, using
  `derivationClosed_differentialAdjoin_of_constants`), the easy inclusion
  `leftTranslationFieldEquiv_fixes_curvatureField`, and the capstone
  **`leftTranslationInvariants_eq_curvatureField`**:

  `{u | ∀ Z ∈ GL_N(K), σ_Z u = u} = K⟨A⟩`.

That is card 12's item (2) in the linear (full-lift) model.  What remains for the card: item (4)'s
"the group is exactly the constant gauges" — which is `exists_constantGauge_of_differentialAut`
plus `E = I⟨Y⟩` — and the projective refinements (5) (fixed field of the scalar centre) and (6)
(fixed field of a unipotent radical), both of which are now computations in the same slice
coordinates.

### Card 12 — the Galois group is exactly the constant gauge group (2026-08-30)

`HTGeometry/GenericTorsorGaloisGroup.lean` (axiom-clean, wired):

- `genericJetMatrix_mul_slice` — `Y·B_m = Y^{(m)}`;
- **`exists_constant_of_differentialAut_fixing_curvature`** — a differential automorphism fixing the
  curvature field moves the generic matrix by `Y ↦ Z·Y` with `Z` a matrix of *constants*:
  `Z = φ(Y)·Y⁻¹` has `δZ = 0` by the Leibniz rule for `δ(M⁻¹)`, and
  `JetFieldConstantKernel.jetField_mem_range_algebraMap_of_deriv_eq_zero` puts its entries in `K`;
- **`exists_leftTranslation_of_differentialAut_fixing_curvature`** — that automorphism *is* the
  constant left translation `σ_Z`: `Z` is invertible because `φ` is, and both maps agree on every
  jet through `Y^{(m)} = Y·B_m` with `B_m` fixed, hence on `JetPoly` and on its fraction field.

With `leftTranslationInvariants_eq_curvatureField` this is the **differential Galois correspondence
for the generic torsor**: the differential automorphism group of the free differential rational
field over the curvature field is exactly `GL_N` of the constants, and its fixed field is exactly
the curvature field.  Card 12's items (2) and the group half of (4) are therefore Lean-closed in the
linear (full-lift) model; what remains is the projective refinement — item (5) (the fixed field of
the scalar centre is the projective field) and item (6) (unipotent fixed fields are the elementary
horizons), both now computations in the same slice coordinates.

### Card 12 — item (5) is CLOSED (2026-08-30)

`HTGeometry/GenericProjectiveCentreField.lean` (axiom-clean, wired):

- `scalarGauge`, `leftTranslationFieldEquiv_scalarGauge_jet` — the centre of the constant gauge
  group multiplies every jet coordinate by one scalar;
- `projectiveSubfield` — the subfield generated by the base field and the ratios `x_p / x_q`;
- `projScaleHom` `x_p ↦ (x_p/x_{p₀})·s`, with `eval_projScaleHom_base` (at `s = x_{p₀}` it is the
  identity) and `eval_projScaleHom_scalar` (at `s = c·x_{p₀}` it is the scalar gauge);
- **`mem_projectiveSubfield_of_scalarGauge_invariant`** — the same one-parameter specialisation as
  in the `GL_N` case: scalar invariance makes a polynomial in `s` vanish at the infinite set
  `{c·x_{p₀} : c ≠ 0}`, hence identically, and evaluating at a base-field point where the
  denominator survives writes `u` as a ratio of elements built from ratios of jets;
- `scalarGauge_fixes_projectiveSubfield` and the capstone
  **`scalarGaugeInvariants_eq_projectiveSubfield`**:

  `{u | ∀ c ≠ 0, σ_{c·1} u = u} = K(x_p/x_q)`.

**Only item (6) is left for card 12.**  Reading the card's own equation (6) as the *definition* of
the elementary horizon (`H_H := F^{U_H(C)}`), what remains to prove is `⋂_H H_H = I`, and that
reduces to: the subgroup of `GL_N(K)` generated by the unipotent radicals of all hyperplane
stabilisers together with the scalars is all of `GL_N(K)` when `K` is algebraically closed.  The
missing input is the classical "`SL_N` of a field is generated by transvections"; mathlib has
`Matrix.exists_list_transvec_mul_diagonal_mul_list_transvec` (transvections × diagonal ×
transvections) but not the reduction of a determinant-one diagonal to transvections.

### Card 12 — item (6) is CLOSED; the card is at stage 3 (2026-08-30)

`HTGeometry/GenericUnipotentHorizonIntersection.lean` (axiom-clean, wired):

- `jetField_ringHom_ext` — two ring homomorphisms of the free differential rational field agreeing
  on the base field and on every jet are equal (`MvPolynomial.induction_on` plus
  `IsFractionRing.div_surjective`);
- `gaugeAut Z hZ := leftTranslationFieldEquiv Z Z⁻¹ …` and **`gaugeAut_comp`** — the gauge action is
  an anti-homomorphism: `σ_W ∘ σ_Z = σ_{Z·W}`, checked on jets through
  `Y^{(r)} ↦ Z·Y^{(r)}` and matrix associativity;
- `gaugeAut_listProd_invariant` — invariance under every transvection gauge propagates along a
  product of transvections (list induction on `Matrix.TransvectionStruct`);
- **`mem_curvatureField_of_transvection_and_scalar_invariant`** — over an algebraically closed `K`
  write `Z = c·M` with `c^N = det Z` (`IsAlgClosed.exists_pow_nat_eq`) and `det M = 1`, factor `M`
  by `SpecialLinearTransvectionGeneration.isTransvectionProduct_of_det_eq_one`, and conclude by
  `leftTranslationInvariants_eq_curvatureField`;
- **`transvection_scalar_invariants_eq_curvatureField`** — the equality form: the common fixed field
  of all elementary (transvection and scalar) gauges *is* the curvature field.  This is the card's
  equation `(5)` with the elementary horizons `(6)`;
- `curvatureField_le_projectiveSubfield` and **`projectiveGaugeInvariants_eq_curvatureField`** — the
  curvature field is centre-invariant, hence sits inside the projective field, and inside that field
  the gauge-invariants are exactly the curvature field: the card's `I = F^{PGL_N(C)}`.

Card 12's items (1) and (3) were already carried by `ProjectiveFrameCompanion`,
`ProjectiveFrameInvariance` (`rel_mulVec_of_rel`, `top_coefficient_eq_zero_of_det_eq_one`,
`coefficients_unique`) and `ProjectiveCurvatureIndependence`
(`curvature_differentialIndependent_of_lift`).  **All six items are Lean-closed**, so
`projective-ht-generic-pv-curvature-core` is promoted to `3-formalized`.

Remaining in this folder at stage 2: cards 1 (`combination-mode-reducibility-baker-bridge`,
blocked on effective Baker–Wüstholz), 7 (`hypertranscendental-maximal-finite-horizon-galois-law`),
10 (`poincare-constraint-order-recession`) and 11
(`projective-horizon-hankel-secant-stratification`).

### Card 1 — both halves of the L² dichotomy are CLOSED; only Baker remains (2026-08-30)

Two new modules, both axiom-clean and wired into `GaloisForLFunctions.HTGeometry`:

- `HTGeometry/CombinationModeDiophantineDivisor.lean` — `summable_prod_pi`,
  `three_add_sum_le_prod`, `summable_modeWeight` and the capstone
  **`summable_modeDivisor_of_diophantine`**: a fixed-exponent Diophantine condition plus
  exponential coefficient decay make the mode-divided datum square-summable.  This is Lemma R's
  positive conclusion (`h ∈ L²`, the cocycle is reducible) with the Baker bound as its hypothesis.
- `HTGeometry/LiouvilleFrequencyNonReducible.lean` — the explicit super-Liouville number
  `α = Σ 2^{−a_k}`, `a_{k+1} = a_k + 1 + 16^{a_k}`, its irrationality, the approximation bound
  `0 < q_K α − p_K ≤ 2^{−16^{a_K}}`, and the capstones **`exists_liouville_frequency`** and
  **`not_summable_liouvilleDivisor`**: the same cohomological equation is *unsolvable* in `L²` for a
  Liouville-independent frequency, at every decay rate.

Card 1 therefore has exactly one open input left: **Lemma R(ii)**, the effective Baker–Wüstholz
lower bound for a fixed finite set of prime logarithms, tracked as
`1-in-progress/effective-baker-matveev-linear-forms.md`.  Everything the card deduces *from* it is
now Lean-closed, so the card promotes by a single application of
`summable_modeDivisor_of_diophantine` once the bound lands.
