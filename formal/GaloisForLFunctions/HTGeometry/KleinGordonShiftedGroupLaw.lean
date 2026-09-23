import GaloisForLFunctions.HTGeometry.KleinGordonShiftedFrequency

/-!
# The group law of the shifted propagator

The shifted symbols obey the addition formulas of the circle, and the Fourier multipliers they define
inherit them. So the shifted propagator is a one-parameter family with the same algebra as the free
one: it is the identity at time zero, and advancing by `t + s` is advancing by `t` and then by `s`,
with the cosine and sine mixing exactly as they do for the free field.

The division by `Ω` is harmless throughout: the identity `sin((t+s)Ω)/Ω = (sin(tΩ)/Ω)cos(sΩ) +
cos(tΩ)(sin(sΩ)/Ω)` holds as an identity of division rings, so it is true where the shifted frequency
degenerates as well, both sides being zero there.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The symbol identities -/

section Symbols

variable {v : E → ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedCos_zero (ξ : E) : kgShiftedCos v 0 ξ = 1 := by
  rw [kgShiftedCos, zero_mul, Real.cos_zero, Complex.ofReal_one]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedSin_zero (ξ : E) : kgShiftedSin v 0 ξ = 0 := by
  rw [kgShiftedSin, zero_mul, Real.sin_zero, Complex.ofReal_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedSinOverFreq_zero (ξ : E) : kgShiftedSinOverFreq v 0 ξ = 0 := by
  rw [kgShiftedSinOverFreq, zero_mul, Real.sin_zero, zero_div, Complex.ofReal_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The cosine addition formula for the shifted frequency.** -/
theorem kgShiftedCos_add (t s : ℝ) (ξ : E) :
    kgShiftedCos v (t + s) ξ
      = kgShiftedCos v t ξ * kgShiftedCos v s ξ - kgShiftedSin v t ξ * kgShiftedSin v s ξ := by
  have hsplit : (t + s) * kgShiftedFreq v ξ
      = t * kgShiftedFreq v ξ + s * kgShiftedFreq v ξ := by ring
  rw [kgShiftedCos, kgShiftedCos, kgShiftedCos, kgShiftedSin, kgShiftedSin, hsplit,
    Real.cos_add]
  push_cast
  ring

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The sine addition formula for the shifted frequency.** -/
theorem kgShiftedSin_add (t s : ℝ) (ξ : E) :
    kgShiftedSin v (t + s) ξ
      = kgShiftedSin v t ξ * kgShiftedCos v s ξ + kgShiftedCos v t ξ * kgShiftedSin v s ξ := by
  have hsplit : (t + s) * kgShiftedFreq v ξ
      = t * kgShiftedFreq v ξ + s * kgShiftedFreq v ξ := by ring
  rw [kgShiftedSin, kgShiftedSin, kgShiftedSin, kgShiftedCos, kgShiftedCos, hsplit,
    Real.sin_add]
  push_cast
  ring

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The addition formula for `sin(tΩ)/Ω`**, valid where the shifted frequency degenerates as
well. -/
theorem kgShiftedSinOverFreq_add (t s : ℝ) (ξ : E) :
    kgShiftedSinOverFreq v (t + s) ξ
      = kgShiftedSinOverFreq v t ξ * kgShiftedCos v s ξ
        + kgShiftedCos v t ξ * kgShiftedSinOverFreq v s ξ := by
  have hsplit : (t + s) * kgShiftedFreq v ξ
      = t * kgShiftedFreq v ξ + s * kgShiftedFreq v ξ := by ring
  rw [kgShiftedSinOverFreq, kgShiftedSinOverFreq, kgShiftedSinOverFreq, kgShiftedCos,
    kgShiftedCos, hsplit, Real.sin_add]
  push_cast
  ring

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The shifted symbols lie on the circle.** -/
theorem kgShiftedSin_sq_add_cos_sq (t : ℝ) (ξ : E) :
    kgShiftedSin v t ξ * kgShiftedSin v t ξ + kgShiftedCos v t ξ * kgShiftedCos v t ξ = 1 := by
  rw [kgShiftedSin, kgShiftedCos, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_add]
  have h := Real.sin_sq_add_cos_sq (t * kgShiftedFreq v ξ)
  rw [show Real.sin (t * kgShiftedFreq v ξ) * Real.sin (t * kgShiftedFreq v ξ)
      + Real.cos (t * kgShiftedFreq v ξ) * Real.cos (t * kgShiftedFreq v ξ)
      = Real.sin (t * kgShiftedFreq v ξ) ^ (2 : ℕ) + Real.cos (t * kgShiftedFreq v ξ) ^ (2 : ℕ) by ring, h,
    Complex.ofReal_one]

end Symbols

/-! ## The operator identities -/

section Operators

variable {v : E → ℝ}

/-- The sine propagator of the shifted frequency. -/
def kgShiftedSinOp (hv : Measurable v) (t : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgShiftedSin hv t) zero_le_one (norm_kgShiftedSin_le v t)

theorem norm_kgShiftedSinOp_le (hv : Measurable v) (t : ℝ) :
    ‖kgShiftedSinOp (E := E) hv t‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

set_option maxHeartbeats 1000000 in
/-- **The shifted cosine propagator is the identity at time zero.** -/
theorem kgShiftedCosOp_zero (hv : Measurable v) :
    kgShiftedCosOp (E := E) hv 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
  fourierMulCLM_eq_id _ _ _ (Eventually.of_forall (kgShiftedCos_zero (v := v)))

set_option maxHeartbeats 1000000 in
/-- The shifted sine propagator vanishes at time zero. -/
theorem kgShiftedSinOp_zero (hv : Measurable v) :
    kgShiftedSinOp (E := E) hv 0 = 0 :=
  fourierMulCLM_eq_zero _ _ _ (Eventually.of_forall (kgShiftedSin_zero (v := v)))

set_option maxHeartbeats 1000000 in
theorem kgShiftedSinFreqOp_zero (hv : Measurable v) :
    kgShiftedSinFreqOp (E := E) hv 0 = 0 :=
  fourierMulCLM_eq_zero _ _ _ (Eventually.of_forall (kgShiftedSinOverFreq_zero (v := v)))

set_option maxHeartbeats 1000000 in
/-- **The group law of the shifted cosine propagator.** -/
theorem kgShiftedCosOp_add (hv : Measurable v) (t s : ℝ) :
    kgShiftedCosOp (E := E) hv (t + s)
      = (kgShiftedCosOp hv t).comp (kgShiftedCosOp hv s)
        - (kgShiftedSinOp hv t).comp (kgShiftedSinOp hv s) := by
  have hcc : Measurable fun ξ : E => kgShiftedCos v t ξ * kgShiftedCos v s ξ :=
    (measurable_kgShiftedCos hv t).mul (measurable_kgShiftedCos hv s)
  have hccb : ∀ ξ : E, ‖kgShiftedCos v t ξ * kgShiftedCos v s ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le v t ξ) (norm_nonneg _) (norm_kgShiftedCos_le v s ξ)
  have hss : Measurable fun ξ : E => kgShiftedSin v t ξ * kgShiftedSin v s ξ :=
    (measurable_kgShiftedSin hv t).mul (measurable_kgShiftedSin hv s)
  have hssb : ∀ ξ : E, ‖kgShiftedSin v t ξ * kgShiftedSin v s ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedSin_le v t ξ) (norm_nonneg _) (norm_kgShiftedSin_le v s ξ)
  have hc : (kgShiftedCosOp (E := E) hv t).comp (kgShiftedCosOp hv s)
      = fourierMulCLM hcc zero_le_one hccb :=
    fourierMulCLM_comp _ _ hcc _ _ _ _ zero_le_one hccb (Eventually.of_forall fun _ => rfl)
  have hs : (kgShiftedSinOp (E := E) hv t).comp (kgShiftedSinOp hv s)
      = fourierMulCLM hss zero_le_one hssb :=
    fourierMulCLM_comp _ _ hss _ _ _ _ zero_le_one hssb (Eventually.of_forall fun _ => rfl)
  rw [hc, hs, kgShiftedCosOp]
  exact fourierMulCLM_sub hcc hss _ zero_le_one hccb zero_le_one hssb zero_le_one
    (norm_kgShiftedCos_le v (t + s)) (Eventually.of_forall (kgShiftedCos_add t s))

set_option maxHeartbeats 1000000 in
/-- **The group law of the shifted sine propagator.** -/
theorem kgShiftedSinFreqOp_add (hv : Measurable v) (t s : ℝ) :
    kgShiftedSinFreqOp (E := E) hv (t + s)
      = (kgShiftedSinFreqOp hv t).comp (kgShiftedCosOp hv s)
        + (kgShiftedCosOp hv t).comp (kgShiftedSinFreqOp hv s) := by
  have hsc : Measurable fun ξ : E => kgShiftedSinOverFreq v t ξ * kgShiftedCos v s ξ :=
    (measurable_kgShiftedSinOverFreq hv t).mul (measurable_kgShiftedCos hv s)
  have hscb : ∀ ξ : E, ‖kgShiftedSinOverFreq v t ξ * kgShiftedCos v s ξ‖ ≤ |t| := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgShiftedSinOverFreq_le v t ξ
    have h2 := norm_kgShiftedCos_le v s ξ
    nlinarith [norm_nonneg (kgShiftedSinOverFreq v t ξ), norm_nonneg (kgShiftedCos v s ξ)]
  have hcs : Measurable fun ξ : E => kgShiftedCos v t ξ * kgShiftedSinOverFreq v s ξ :=
    (measurable_kgShiftedCos hv t).mul (measurable_kgShiftedSinOverFreq hv s)
  have hcsb : ∀ ξ : E, ‖kgShiftedCos v t ξ * kgShiftedSinOverFreq v s ξ‖ ≤ |s| := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgShiftedCos_le v t ξ
    have h2 := norm_kgShiftedSinOverFreq_le v s ξ
    nlinarith [norm_nonneg (kgShiftedCos v t ξ), norm_nonneg (kgShiftedSinOverFreq v s ξ)]
  have hsccomp : (kgShiftedSinFreqOp (E := E) hv t).comp (kgShiftedCosOp hv s)
      = fourierMulCLM hsc (abs_nonneg t) hscb :=
    fourierMulCLM_comp _ _ hsc _ _ _ _ (abs_nonneg t) hscb (Eventually.of_forall fun _ => rfl)
  have hcscomp : (kgShiftedCosOp (E := E) hv t).comp (kgShiftedSinFreqOp hv s)
      = fourierMulCLM hcs (abs_nonneg s) hcsb :=
    fourierMulCLM_comp _ _ hcs _ _ _ _ (abs_nonneg s) hcsb (Eventually.of_forall fun _ => rfl)
  rw [hsccomp, hcscomp, kgShiftedSinFreqOp]
  exact fourierMulCLM_add hsc hcs _ (abs_nonneg t) hscb (abs_nonneg s) hcsb (abs_nonneg (t + s))
    (norm_kgShiftedSinOverFreq_le v (t + s)) (Eventually.of_forall (kgShiftedSinOverFreq_add t s))

end Operators

end GaloisForLFunctions.HTGeometry
