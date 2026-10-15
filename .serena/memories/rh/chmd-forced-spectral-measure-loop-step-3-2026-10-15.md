# CHMD loop step 3: the forced spectral measure (2026-10-15, MUST-1531)

Module `formal/GaloisForLFunctions/RHTower/CHMDForcedSpectralMeasureAndOffLineDefectWave.lean`
(namespace `RHTower.CHMDForcedMeasure`; imports the separation-law module; wired; standard axioms).

Task: "produce the spectral-realisation object for the CHMD causal wave or prove the class empty." Result: the class is
nonempty iff RH, so neither is decidable; but the object is forced and produced:
- `kgZeroMeasure := Measure.sum (ρ ↦ ofReal (m Re w_ρ / 2) • (dirac (Re ρ_ρ) + dirac (−Re ρ_ρ)))`, unconditional finite
  positive measure (`Re w_ρ > 0` for every zero), `kgZeroMeasure_univ`, `integral_kgZeroMeasure`.
- `charFun_kgZeroMeasure : charFun kgZeroMeasure t = shadowWave t`, `shadowWave t = Σ' m Re w cos(t Re ρ_ρ)`,
  `abs_shadowWave_le_zero_value`, `shadowWave_zero = chmdWave 0`.
- `offLineDefectWave = chmdWave − shadowWave = Σ' defectTerm`, `defectTerm_eq_zero_of_im_kgFreq_eq_zero` (on-line terms vanish).
- `riemannHypothesis_iff_offLineDefectWave_eq_zero`, `riemannHypothesis_iff_offLineDefectWave_bddAbove`,
  `riemannHypothesis_iff_charFun_kgZeroMeasure_eq`, `eq_kgZeroMeasure_of_charFun_eq'` (uniqueness via `Measure.ext_of_charFun`),
  `riemannHypothesis_iff_exists_finiteMeasure_charFun_defect` (bounded-defect class nonempty ⟺ RH).

Lesson: a Hilbert–Pólya operator for the KG wave is the diagonal zero operator or nothing; no construction can avoid the zeros.
Remaining content = sign of the off-line defect wave = Wall 1. Do not pursue realisation constructions for CHMD.

Lean notes: `integral_sum_measure` needs `Integrable f (Measure.sum μ)` (from `integrable_const.mono'` with the finite-measure
instance); `integrable_dirac (by simp)`; `inner ℝ x t = t * x` by `simp [RCLike.inner_apply]`; `Complex.cos` unfolds with
`rw [Complex.cos]`, then `push_cast; field_simp` closes `exp(ix) + exp(−ix) = 2 cos x` (no trailing `ring`).
