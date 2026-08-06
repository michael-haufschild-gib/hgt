# Card: cusp-spectrum-radius-law — formalization in progress

Card: `docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md`
(carries a "Formalization status" section + a "Corpus reuse audit" section).

## ALREADY IN THE CORPUS — REUSE, DO NOT REBUILD
- **`HTGeometry/ResidueJumpLowerBound.lean`** (root namespace `HTGeometry`):
  `residue_jump_bound`, `residue_jump_of_integral_eq_zero`.
  This IS the card's jump lemma
  (`sup_{|s-s*_0|=r}|F_α - F_{α'}| ≥ |ρ_0(α)|/r`). Its docstring already names
  the standard twist as the intended application.
- See `cusp_card_corpus_reuse_audit_2026_08_06` for the full audit
  (`Bottcher/NaturalBoundary*`, `RHTower/BVPrimeWindowContinuation`,
  mathlib `mellin` + `HTGeometry/SmoothWeightPerron`,
  `SelfDualPrimitiveDirichletDatum`).

## DONE BY ME (unconditional; axioms propext/Classical.choice/Quot.sound;
all wired into the HTGeometry umbrella)
- `HTGeometry/ShiftLatticeRadiusLaw.lean` — Cauchy–Hadamard bridge
  (`hadamardLimsup`, `radius_ofScalars_eq_inv_hadamardLimsup`,
  `hadamardLimsup_geometric`, `hadamardLimsup_of_radius`) + spectrum
  (`shiftSpectrum`, `infDist_zero_shiftSpectrum` = **Δ(0) = d q^{-1/d}**,
  `cusp_constant_eq`, `hadamardLimsup_cusp`).
- `HTGeometry/ShiftLatticeThetaSeries.lean` — convergence layer
  (`summable_rpow_mul_exp_neg_rpow`, `thetaTerm`, `thetaSeries`,
  `norm_thetaTerm`, `summable_norm_thetaTerm_of_im_pos`,
  `summable_thetaTerm_of_im_pos`, `summable_thetaTerm_of_re`).
- `HTGeometry/ShiftLatticeExpansion.lean` — Step 1 interior + UPPER bound
  (`hasSum_shiftLatticeExpansion`, `hadamardLimsup_shiftLatticeCoeff_le`).
  Needs `set_option maxHeartbeats 1600000 in` on the expansion theorem.
- `HTGeometry/PowerSeriesSingularRadius.lean` — LOWER bound mechanism
  (`shiftSumFun`, `analyticOnNhd_shiftSumFun`,
  `exists_analytic_extension_of_lt_radius`,
  `radius_le_of_no_analytic_extension`,
  `le_hadamardLimsup_of_no_analytic_extension`).
- `HTGeometry/ResidueJumpNoLimit.lean` — the two missing consequences of the
  corpus jump lemma: `not_analyticOnNhd_of_circleIntegral_ne_zero` (Cauchy
  certificate, feeds `radius_le_of_no_analytic_extension`) and
  `not_tendstoUniformlyOn_of_residue_ne_zero` (qualitative jump).
- `HTGeometry/ShiftSpectrumSpacing.lean` — the card's **Consequences** section:
  `shiftSpectrumPoint`, `shiftSpectrumMap`, `shiftSpectrumSlope`,
  `hasDerivAt_shiftSpectrumMap`, `shiftSpectrumGap`, `shiftSpectrumGap_nonneg`,
  `exists_shiftSpectrumGap_eq` (MVT form of the card's `≍`),
  `shiftSpectrumGap_le`, `tendsto_shiftSpectrumGap_nhds_zero`
  (= **Δ(α_m) → 0 for d > 1**), `tendsto_degreeOneLatticeRoot_atTop`
  (= degree-one lattice has radius zero above degree one), plus
  `tendsto_rpow_neg_nhds_zero`.
  Needs imports `Mathlib.Analysis.Calculus.Deriv.MeanValue`,
  `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`,
  `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`.
- `HTGeometry/ShiftLatticeVerification.lean` — the card's **Verifications**
  table: `shiftSpectrum_degree_one` (degree-one spectrum is the rational
  lattice), `infDist_zero_shiftSpectrum_zeta` / `_dirichlet` / `_degree_two`,
  and `cusp_constant_zeta` / `_dirichlet` / `_degree_two` (= 1/(4π)).

## FURTHER CORPUS REUSE FOUND (do not rebuild)
`HTGeometry/BohrFejerConcentration.lean` already carries the bounded
exponential-sum machinery: `expChar`, `fejerSum`, `fejerSum_eq_geom`,
`norm_expChar`, `norm_expChar_sub_one_sq`, and — INSIDE the proof of
`fejerKernel_norm_le` — the bound `‖fejerSum β N u‖ ≤ 2/‖expChar β u - 1‖`.
That inline bound is exactly "exponential sums off the lattice are bounded",
the input that makes the degree-one standard twist entire off its spectrum.
DONE: extracted as `norm_fejerSum_le` in
`HTGeometry/LatticeExpSumDichotomy.lean`, together with `latticeChar`,
`latticeChar_eq`, `latticeChar_ne_one`, `norm_latticeExpSum_le` (bounded off the
lattice, uniformly in N) and `latticeExpSum_at_integer` (= N+1 on the lattice).
That is the degree-one dichotomy behind verification rows 1 and 2.
- `HTGeometry/LatticeTwistConvergence.lean` — the ANALYTIC degree-one dichotomy:
  `twistWeight`, `antitone_twistWeight`, `tendsto_twistWeight`,
  `cauchySeq_latticeTwist` + `exists_tendsto_latticeTwist` (off the lattice the
  twisted series converges for EVERY σ > 0, via mathlib's Dirichlet test
  `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`),
  `latticeTwist_at_integer` (on the lattice it is the real p-series),
  `not_summable_twistWeight` (which diverges for σ ≤ 1).
  So in DEGREE ONE the card's Step-2 input is available without K–P.
  NOTE: needs `import Mathlib.Analysis.PSeries` for
  `Real.summable_one_div_nat_rpow`.
  Corpus precedent for the Dirichlet test:
  `HTGeometry/OddDirichletKernel.cauchySeq_sum_oddHarmonicSine`.
- `HTGeometry/RootGrowthEngine.lean` — Step 3's k-th-root mechanism:
  `tendsto_const_rpow_inv_nat`, `tendsto_nat_rpow_div_self`,
  `tendsto_rpow_inv_of_polynomial_bounds` (polynomial envelopes are invisible
  to the k-th root), `hadamardLimsup_eq_one_of_tendsto`,
  `hadamardLimsup_geometric_of_tendsto_one` (only the geometric factor
  survives).  Uses `Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero`.

## STEP 3 — WHAT IS LEFT, AND WHAT IS ALREADY CORPUS-OWNED
Chain: `ζ(s-k) = 2(2π)^{-(1-s+k)} cos(π(1-s+k)/2) Γ(1-s+k) ζ(1-s+k)`
(mathlib `riemannZeta_one_sub`), then take k-th roots.
- `|ζ(1-s+k)| → 1`: ALREADY CORPUS-OWNED —
  `RHTower.tendsto_riemannZeta_of_re_atTop`
  (`RHTower/XiSourceNormalConeDivisorConservation.lean:394`), and for Dirichlet
  characters `RHTower.tendsto_LSeries_atTop`
  (`RHTower/DirichletLRayLowerBound.lean:24`). DO NOT REBUILD.
- `(2π)^{-k}` → handled by `hadamardLimsup_geometric_of_tendsto_one`.
- Gamma ratio: DONE, no Stirling needed. `tendsto_rpow_inv_one_of_ratio_one`
  (ratio → 1 ⇒ k-th root → 1, by telescoping + `Filter.Tendsto.cesaro`),
  `tendsto_gammaRatioFactor`, `tendsto_norm_gammaRatio_rpow_inv`
  (all in `HTGeometry/RootGrowthEngine.lean`).
  The corpus has a related but DIFFERENT statement in
  `HTGeometry/DeterminantRatioRoot.lean` (`cesaro_range_div_succ_atBot`,
  `tendsto_rpow_inv_succ_zero_of_ratio_zero`) — that is the ratio → 0 ⇒ root → 0
  case; mine is the unit case.
- STILL MISSING for Step 3: only the oscillating `cos(π(1-s+k)/2)` factor
  (vanishes at odd integers, so the limsup needs a subsequence where it is
  bounded below).</repl>


  Corpus Abel-summation layer (if needed later):</repl>

  `HTGeometry/ShiftPartialSummation.lean`, `HTGeometry/DiscreteAbelIcc.lean`,
  `HTGeometry/TopSumMajorization.lean`, `RHTower/ZetaPartialSumStrip.lean`,
  `RHTower/CesaroHull.lean`, `RHTower/OddHarmonicAbel.lean`.</repl>
</repl>
</repl>
</repl>
</invoke>


## STATE OF THE PROOF
Hadamard mechanism complete in BOTH directions; jump lemma + its consequences
complete. What remains is genuinely K–P/Selberg-class construction:
1. Selberg class `S^♯` as a Lean structure (model on
   `RHTower/SelfDualDirichletRealZeros.lean`'s `SelfDualPrimitiveDirichletDatum`).
2. The standard twist `F_α` with its meromorphic continuation off `Spec(F)`
   (model on `RHTower/BVPrimeWindowContinuation.lean`'s `continuedSource` +
   `LSeries_…_eq_continuation` idiom).
3. `ρ_0(α) ≠ 0` on `Spec(F)` — the K–P residue nonvanishing. Once available,
   `residue_jump_of_integral_eq_zero` +
   `not_analyticOnNhd_of_circleIntegral_ne_zero` +
   `le_hadamardLimsup_of_no_analytic_extension` close the lower bound.
4. Step 1 at the boundary `z₀ = -α₀ ∈ ℝ`: Mellin–Barnes (mathlib `mellin`,
   contour technique as in `HTGeometry/SmoothWeightPerron.lean`).
5. Step 3: functional equation + uniform Stirling.

## TRAPS
- `TendstoUniformlyOn` is stated with the uniformity filter; use
  `Metric.tendstoUniformlyOn_iff` for the ε form.
- `AnalyticAt.comp` mis-unifies `f`; pass `(g := …) (f := …) (x := …)`.
- `le_of_forall_lt` is strict; use `by_contra` + `rw [not_le]` + `exists_between`.
- `ofReal_norm` (ROOT ns); `ofReal_norm_eq_enorm` is deprecated.
- `Metric.eball`/`Metric.mem_eball` (`EMetric.ball` deprecated).
- `ENNReal.ofReal_inv_of_pos` states `ofReal x⁻¹ = (ofReal x)⁻¹` — use `←`.

## NOTE
`+GaloisForLFunctions.HTGeometry` intermittently fails on `DbarSeveral.lean` /
`CriticalTailFibreCount.lean`, both dirty from a CONCURRENT session. Not mine.
