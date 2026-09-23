import GaloisForLFunctions.HTGeometry.KleinGordonWindowCascade

/-!
# The shifted frequency of a diagonal potential

A real frequency-diagonal potential `v` changes the Klein–Gordon equation only by shifting the
frequency: the equation `ü + (⟨D⟩² + v)u = 0` is the free equation with `⟨ξ⟩` replaced by

`Ω_v(ξ) = √(⟨ξ⟩² + v(ξ))`,

which is a genuine positive frequency whenever `|v| ≤ b < 1`, because `⟨ξ⟩² ≥ 1`. This module builds
the shifted symbols `cos(tΩ)`, `sin(tΩ)` and `sin(tΩ)/Ω` together with their bounds, and the Fourier
multipliers they define.

The bounds are unconditional: where the shifted frequency degenerates the Lean square root returns
zero and the quotient `sin(tΩ)/Ω` returns zero, which satisfies the same estimate. The hypotheses on
`v` are needed only for the identity `Ω² = ⟨ξ⟩² + v` and for positivity.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The shifted frequency -/

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The frequency of the Klein–Gordon operator shifted by a real diagonal potential. -/
def kgShiftedFreq (v : E → ℝ) (ξ : E) : ℝ := Real.sqrt (kgFreq ξ ^ (2 : ℕ) + v ξ)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedFreq_nonneg (v : E → ℝ) (ξ : E) : 0 ≤ kgShiftedFreq v ξ := Real.sqrt_nonneg _

section Positivity

variable {v : E → ℝ} {b : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedFreq_sq_arg_pos (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) (ξ : E) :
    0 < kgFreq ξ ^ (2 : ℕ) + v ξ := by
  have h1 : (1 : ℝ) ≤ kgFreq ξ := one_le_kgFreq ξ
  have h2 : (1 : ℝ) ≤ kgFreq ξ ^ (2 : ℕ) := by nlinarith
  have h3 : -b ≤ v ξ := neg_le_of_abs_le (hvb ξ)
  linarith

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The shifted frequency is a genuine positive frequency.** -/
theorem kgShiftedFreq_pos (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) (ξ : E) :
    0 < kgShiftedFreq v ξ :=
  Real.sqrt_pos.mpr (kgShiftedFreq_sq_arg_pos hb1 hvb ξ)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The shifted frequency squares to the shifted symbol.** -/
theorem kgShiftedFreq_sq (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) (ξ : E) :
    kgShiftedFreq v ξ ^ (2 : ℕ) = kgFreq ξ ^ (2 : ℕ) + v ξ :=
  Real.sq_sqrt (kgShiftedFreq_sq_arg_pos hb1 hvb ξ).le

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The shifted frequency is bounded below away from zero. -/
theorem one_sub_le_kgShiftedFreq_sq (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) (ξ : E) :
    1 - b ≤ kgShiftedFreq v ξ ^ (2 : ℕ) := by
  have h1 : (1 : ℝ) ≤ kgFreq ξ := one_le_kgFreq ξ
  have h2 : (1 : ℝ) ≤ kgFreq ξ ^ (2 : ℕ) := by nlinarith
  have h3 : -b ≤ v ξ := neg_le_of_abs_le (hvb ξ)
  rw [kgShiftedFreq_sq hb1 hvb ξ]
  linarith

end Positivity

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedFreq {v : E → ℝ} (hv : Measurable v) :
    Measurable (kgShiftedFreq v) :=
  Real.continuous_sqrt.measurable.comp
    (((continuous_kgFreq (E := E)).measurable.pow_const 2).add hv)

/-! ## The shifted symbols -/

/-- The shifted cosine symbol. -/
def kgShiftedCos (v : E → ℝ) (t : ℝ) (ξ : E) : ℂ :=
  ((Real.cos (t * kgShiftedFreq v ξ) : ℝ) : ℂ)

/-- The shifted sine symbol. -/
def kgShiftedSin (v : E → ℝ) (t : ℝ) (ξ : E) : ℂ :=
  ((Real.sin (t * kgShiftedFreq v ξ) : ℝ) : ℂ)

/-- The shifted sine symbol divided by the shifted frequency. -/
def kgShiftedSinOverFreq (v : E → ℝ) (t : ℝ) (ξ : E) : ℂ :=
  ((Real.sin (t * kgShiftedFreq v ξ) / kgShiftedFreq v ξ : ℝ) : ℂ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedCos {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    Measurable (kgShiftedCos v t) :=
  Complex.continuous_ofReal.measurable.comp
    (Real.continuous_cos.measurable.comp (measurable_const.mul (measurable_kgShiftedFreq hv)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedSin {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    Measurable (kgShiftedSin v t) :=
  Complex.continuous_ofReal.measurable.comp
    (Real.continuous_sin.measurable.comp (measurable_const.mul (measurable_kgShiftedFreq hv)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedSinOverFreq {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    Measurable (kgShiftedSinOverFreq v t) :=
  Complex.continuous_ofReal.measurable.comp
    ((Real.continuous_sin.measurable.comp
      (measurable_const.mul (measurable_kgShiftedFreq hv))).div (measurable_kgShiftedFreq hv))

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgShiftedCos_le (v : E → ℝ) (t : ℝ) (ξ : E) : ‖kgShiftedCos v t ξ‖ ≤ 1 := by
  rw [kgShiftedCos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgShiftedSin_le (v : E → ℝ) (t : ℝ) (ξ : E) : ‖kgShiftedSin v t ξ‖ ≤ 1 := by
  rw [kgShiftedSin, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The shifted sine, divided by the shifted frequency, is bounded by the elapsed time** — the
estimate that makes the shifted propagator a bounded operator with no lower bound on the frequency. -/
theorem norm_kgShiftedSinOverFreq_le (v : E → ℝ) (t : ℝ) (ξ : E) :
    ‖kgShiftedSinOverFreq v t ξ‖ ≤ |t| := by
  rw [kgShiftedSinOverFreq, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_lt_of_le (kgShiftedFreq_nonneg v ξ) with hzero | hpos
  · rw [← hzero]
    simp [abs_nonneg]
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |Real.sin (t * kgShiftedFreq v ξ)| ≤ |t * kgShiftedFreq v ξ| := Real.abs_sin_le_abs
      _ = |t| * kgShiftedFreq v ξ := by rw [abs_mul, abs_of_pos hpos]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem starRingEnd_kgShiftedCos (v : E → ℝ) (t : ℝ) (ξ : E) :
    (starRingEnd ℂ) (kgShiftedCos v t ξ) = kgShiftedCos v t ξ := Complex.conj_ofReal _

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem starRingEnd_kgShiftedSinOverFreq (v : E → ℝ) (t : ℝ) (ξ : E) :
    (starRingEnd ℂ) (kgShiftedSinOverFreq v t ξ) = kgShiftedSinOverFreq v t ξ :=
  Complex.conj_ofReal _

/-! ## The shifted propagators -/

/-- The cosine propagator of the shifted frequency. -/
def kgShiftedCosOp {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgShiftedCos hv t) zero_le_one (norm_kgShiftedCos_le v t)

/-- The sine propagator of the shifted frequency, divided by that frequency. -/
def kgShiftedSinFreqOp {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgShiftedSinOverFreq hv t) (abs_nonneg t)
    (norm_kgShiftedSinOverFreq_le v t)

theorem norm_kgShiftedCosOp_le {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    ‖kgShiftedCosOp (E := E) hv t‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

theorem norm_kgShiftedSinFreqOp_le {v : E → ℝ} (hv : Measurable v) (t : ℝ) :
    ‖kgShiftedSinFreqOp (E := E) hv t‖ ≤ |t| :=
  norm_fourierMulCLM_le _ _ _

/-- **The shifted propagators are self-adjoint**, because their symbols are real. -/
theorem kgShiftedCosOp_inner {v : E → ℝ} (hv : Measurable v) (t : ℝ)
    (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgShiftedCosOp hv t f) g : ℂ) = inner ℂ f (kgShiftedCosOp hv t g) :=
  fourierMulCLM_inner _ _ _ (starRingEnd_kgShiftedCos v t) f g

theorem kgShiftedSinFreqOp_inner {v : E → ℝ} (hv : Measurable v) (t : ℝ)
    (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgShiftedSinFreqOp hv t f) g : ℂ) = inner ℂ f (kgShiftedSinFreqOp hv t g) :=
  fourierMulCLM_inner _ _ _ (starRingEnd_kgShiftedSinOverFreq v t) f g

end GaloisForLFunctions.HTGeometry
