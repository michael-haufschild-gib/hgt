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
| 9 | laguerre-polya-jensen-profield-blindness | OPEN | LP class, Jensen's theorem, even canonical product, quartet surgery |
| 10 | poincare-constraint-order-recession | OPEN | unit-cost cascade ord_DA(f^[n]) = n; affine invariance; Bergweiler |
| 11 | projective-horizon-hankel-secant-stratification | OPEN | catalecticant/secant identification, codimension 2k-1, Sing(C_k)=C_{k+1} |
| 12 | projective-ht-generic-pv-curvature-core | OPEN | Wilczynski normalization; Picard–Vessiot SL_N; invariant field |
| 13 | random-holomorphic-maximal-translation-ht-law | OPEN | random entire functions, finite-jet absolute continuity, GAF nondegeneracy |

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
