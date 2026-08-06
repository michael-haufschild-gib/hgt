# Card: cusp-spectrum-radius-law — formalization in progress

Card: `docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md`
(carries a "Formalization status" section with the declaration tables).

## DONE (unconditional; axioms propext/Classical.choice/Quot.sound; both wired
into the HTGeometry umbrella)

### `HTGeometry/ShiftLatticeRadiusLaw.lean` — the Hadamard bridge + spectrum
`hadamardLimsup`, `nnnorm_ofScalars`,
`radius_ofScalars_eq_inv_hadamardLimsup` (Cauchy–Hadamard),
`hadamardLimsup_geometric`, `hadamardLimsup_of_radius` (**the bridge**:
radius `R` for `∑ A^k c_k ζ^k` ⇒ `limsup ‖c_k‖^{1/k} = 1/(‖A‖R)`),
`shiftSpectrum`, `shiftSpectrum_pos`, `zero_notMem_shiftSpectrum`,
`shiftSpectrum_diff_zero`, `base_mem_shiftSpectrum`,
`infDist_zero_shiftSpectrum` (**Δ(0) = d q^{-1/d}**), `cusp_constant_eq`,
`hadamardLimsup_cusp`.

### `HTGeometry/ShiftLatticeThetaSeries.lean` — the convergence layer
`summable_rpow_mul_exp_neg_rpow` (`∑ n^A e^{-c n^e} < ∞`, any A, c>0, e>0),
`thetaTerm`, `thetaSeries`, `thetaTerm_zero`, `norm_thetaTerm`,
`const_nonneg_of_bound`, `summable_thetaTerm_of_im_pos` (converges for EVERY
spectral parameter above the real axis), `summable_thetaTerm_of_re` (the
standard twist on its abscissa half-plane).

## NEXT STEP (well-scoped, no new theory needed)
The INTERIOR shift-lattice expansion needs no Mellin–Barnes. For `z₀ ∈ ℍ` and
`|ζ| < Im z₀`, the double family
`((2πiζ)^k/k!) · a(n) n^{-(s-k/d)} e(z₀ n^{1/d})` on `ℕ × ℕ` is absolutely
summable: summing over `k` first turns `e^{-2π(Im z₀)n^{1/d}}` into
`e^{-2π(Im z₀-|ζ|)n^{1/d}}`, still covered by
`summable_rpow_mul_exp_neg_rpow`. Fubini (`HasSum.prod_fiberwise` /
`Summable.tsum_prod`) then yields
`HasSum (fun k => ((2πiζ)^k/k!) * thetaSeries a d (s-k/d) z₀)
   (thetaSeries a d s (z₀+ζ))`,
and with `FormalMultilinearSeries.le_radius_of_summable_nnnorm` +
`radius_ofScalars_eq_inv_hadamardLimsup` gives the UPPER bound
`limsup_k |Θ(s-k/d,z₀)/k!|^{1/k} ≤ 1/(2π Im z₀)`.
Per-`n` identity needed: `n^{-(s-k/d)} = n^{-s}·(n^{1/d})^k` and
`∑_k (2πiζ n^{1/d})^k/k! = e(ζ n^{1/d})` (mathlib `Complex.exp_eq_tsum_div` /
`NormedSpace.exp`).

## STILL MISSING (large, from scratch)
- The BOUNDARY case `z₀ = -α₀ ∈ ℝ`: Mellin–Barnes + Kaczorowski–Perelli
  continuation of `F_α` off `Spec(F)`, and `ρ_0(α) ≠ 0` on the spectrum
  (jump lemma) — this is what upgrades the upper bound to the exact radius.
- The Selberg class `S^♯` as a Lean structure (Dirichlet series, continuation,
  functional equation, Ramanujan bound). The corpus has NO such layer: the
  `RHTower/Selberg*.lean` modules are the Selberg SIEVE.
- Step 3 (independent cusp constant): functional equation + uniform Stirling.

## mathlib assets found
- `FormalMultilinearSeries.ofScalars`, `ofScalars_norm`, `radius_eq_liminf`
  (in `Mathlib.Analysis.Analytic.RadiusLiminf`, NOT `.OfScalars`),
  `le_radius_of_summable_nnnorm`, `le_radius_of_bound`.
- `ENNReal.inv_limsup`, `ENNReal.limsup_const_mul_of_ne_top` (any filter;
  `ENNReal.limsup_const_mul` needs `CountableInterFilter`, which ℕ's `atTop`
  is NOT), `ENNReal.ofReal_inv_of_pos`, `ENNReal.eq_div_iff`.
- `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` and `tendsto_rpow_atTop`
  (ROOT namespace); `isLittleO_exp_neg_mul_rpow_atTop`.
- `summable_of_isBigO_nat`, `Asymptotics.IsBigO.of_bound`,
  `Filter.Tendsto.eventually_lt_const`.
- `Complex.norm_natCast_cpow_of_pos`, `Complex.norm_exp`,
  `Real.summable_nat_rpow_inv`.
- `Metric.infDist_le_dist_of_mem` needs `(x := …)` explicitly.
- `Mathlib.Analysis.SpecialFunctions.Pow.NNRpow` does not exist; use `.NNReal`.

## NOTE
`HTGeometry/DbarSeveral.lean` currently fails the umbrella build with a
`whnf` heartbeat timeout. It is NOT mine — a concurrent session is editing it
(modified 15:57, working-tree dirty). My modules build clean in isolation.
