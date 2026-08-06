# Card: cusp-spectrum-radius-law — formalization started

Card: `docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md`
(now carries a "Formalization status" section).

## DONE — `HTGeometry/ShiftLatticeRadiusLaw.lean`
(unconditional; axioms propext/Classical.choice/Quot.sound; wired into the
HTGeometry umbrella; umbrella builds clean at 15152 jobs)

- `hadamardLimsup c = limsup (fun n => ↑(‖c n‖₊ ^ (1/n))) atTop` in ℝ≥0∞.
- `nnnorm_ofScalars`, `radius_ofScalars_eq_inv_hadamardLimsup` — Cauchy–Hadamard,
  from mathlib `FormalMultilinearSeries.radius_eq_liminf` + `ENNReal.inv_limsup`.
- `hadamardLimsup_geometric` — the growth functional scales by `‖A‖`.
- `hadamardLimsup_of_radius` — **the bridge**: radius `R` for
  `∑ A^k c_k ζ^k` ⇒ `limsup ‖c_k‖^{1/k} = 1/(‖A‖R)`.
- `shiftSpectrum a d q = {d(m/q)^{1/d} : m ≥ 1, a m ≠ 0}`, `shiftSpectrum_pos`,
  `zero_notMem_shiftSpectrum`, `shiftSpectrum_diff_zero`,
  `base_mem_shiftSpectrum`, `infDist_zero_shiftSpectrum` (= **Δ(0) = d q^{-1/d}**).
- `cusp_constant_eq` (`1/(2π·d q^{-1/d}) = q^{1/d}/(2πd)`), `hadamardLimsup_cusp`.

## REMAINING (large, from scratch)
The corpus has NO Selberg-class layer. The `RHTower/Selberg*.lean` modules are
the Selberg SIEVE, not the Selberg class of L-functions. So the two missing
inputs must be built:
1. Step 1 — Mellin–Barnes: `Φ_F(s,-α₀+ζ) - (singular part)
   = ∑_k ((2πiζ)^k/k!) F_{α₀}(s-k/d)`.
   Needs `e^{-x} = (2πi)^{-1}∫_{(c)} Γ(u) x^{-u} du` and contour shifting.
2. Step 2 — `radius = Δ(α₀)`: Kaczorowski–Perelli standard-twist theory —
   continuation of `F_α` across every `α ∉ Spec(F)`, plus `ρ_0(α) ≠ 0` on the
   spectrum for the jump lemma. Requires defining the Selberg class `S^♯`
   (Dirichlet series + continuation + functional equation + Ramanujan bound)
   as a Lean structure.
3. Step 3 (independent cusp constant) — functional equation + uniform Stirling
   for `Γ` along a leftward horizontal shift; also needs the class axioms.

## mathlib assets found
- `FormalMultilinearSeries.ofScalars`, `ofScalars_norm`, `radius_eq_liminf`
  (in `Mathlib.Analysis.Analytic.RadiusLiminf` — NOT in `.OfScalars`).
- `ENNReal.inv_limsup`, `ENNReal.inv_liminf`,
  `ENNReal.limsup_const_mul_of_ne_top` (works for ANY filter;
  `ENNReal.limsup_const_mul` needs `CountableInterFilter`, which `atTop` on ℕ
  is NOT).
- `ENNReal.ofReal_inv_of_pos`, `ENNReal.ofReal_div_of_pos`, `ENNReal.eq_div_iff`.
- `Metric.infDist_le_dist_of_mem` (pass `(x := …)`; the `have :=` form cannot
  infer it), `Metric.le_infDist`.
- `Mathlib.Analysis.SpecialFunctions.Pow.NNRpow` does NOT exist; use
  `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`.
