# Stage-3 sweep ledger — 03-ht-translation-projective-geometry

Goal: formalize every proven theorem of each card unconditionally in Lean 4, then promote the
card to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/03-ht-translation-projective-geometry/`.

Already promoted (before this sweep): `ht-remote-quartet-compact-open-field-invisibility`,
`hypertranscendental-caustic-divisor-pole-cone`, `jetwise-dense-single-ht-profield-class`.

| # | Card | State | Blocking mathematics |
|---|---|---|---|
| 1 | combination-mode-reducibility-baker-bridge | OPEN | Baker–Wüstholz effective bound; Dirichlet pigeonhole no-go; Hankel support-≤d lemma |
| 2 | da-ht-topological-interlacing-law | **PROMOTED 2026-08-29** | — (Runge's theorem built from scratch) |
| 3 | ht-c28-minimal-handle-collapse | OPEN | per-handle collapse citations (Weierstrass addition, holonomic, integration closure, vdPS, Hardouin–Singer) |
| 4 | ht-da-translation-spectrum-countability | **PROMOTED 2026-08-29** | — |
| 5 | ht-exact-da-translation-stabilizer | **PROMOTED 2026-08-29** | — (Ostrowski replaced by eventual-gap hypertranscendence) |
| 6 | ht-q-residue-spectrum-classification | OPEN | ADH rational-or-HT; Chen–Singer q-discrete residues |
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
