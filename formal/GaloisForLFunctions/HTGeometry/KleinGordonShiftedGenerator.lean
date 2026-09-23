import GaloisForLFunctions.HTGeometry.KleinGordonShiftedDerivative

/-!
# The generator of the shifted propagator, below a fixed frequency

The second equation of motion of a frequency-diagonal background carries the factor `Ω²`, which is
unbounded. Below a fixed frequency it is bounded — `Ω² ≤ 1 + R² + b` — so the symbol `Ω²χ_R` defines a
Fourier multiplier, the generator of the shifted propagator restricted to that band.

The identity that drives the second equation of motion is the cosine addition formula rewritten
through the bounded sine symbol:

`cos((t+s)Ω)χ = cos(tΩ)cos(sΩ)χ − Ω²χ·(sin(tΩ)/Ω)·(sin(sΩ)/Ω)χ`,

which holds because `Ω > 0` for a weak potential and the band symbol is idempotent.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Generator

variable {v : E → ℝ} {b : ℝ}

/-- The symbol of `Ω²`, cut to the frequencies below `R`. -/
def kgShiftedFreqSqLow (v : E → ℝ) (R : ℝ) (ξ : E) : ℂ :=
  ((kgShiftedFreq v ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedFreqSqLow (hv : Measurable v) (R : ℝ) :
    Measurable (kgShiftedFreqSqLow v R) :=
  (Complex.continuous_ofReal.measurable.comp
    ((measurable_kgShiftedFreq hv).pow_const 2)).mul (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Below a fixed frequency the generator symbol is bounded.** -/
theorem norm_kgShiftedFreqSqLow_le (hb0 : 0 ≤ b) (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b)
    (R : ℝ) (ξ : E) : ‖kgShiftedFreqSqLow v R ξ‖ ≤ 1 + R ^ (2 : ℕ) + b := by
  have hband := band_bound_nonneg (b := b) hb0 R
  rw [kgShiftedFreqSqLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (kgShiftedFreq v ξ))]
    exact kgShiftedFreq_sq_le hb1 hvb hξ
  · simpa using hband

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem starRingEnd_kgShiftedFreqSqLow (v : E → ℝ) (R : ℝ) (ξ : E) :
    (starRingEnd ℂ) (kgShiftedFreqSqLow v R ξ) = kgShiftedFreqSqLow v R ξ := by
  rw [kgShiftedFreqSqLow, map_mul, Complex.conj_ofReal, starRingEnd_kgLowPass]

/-- **The generator of the shifted propagator on a band.** -/
def kgShiftedFreqSqLowOp (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (R : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgShiftedFreqSqLow hv R)
    (band_bound_nonneg (b := b) hb0 R) (norm_kgShiftedFreqSqLow_le hb0 hb1 hvb R)

theorem norm_kgShiftedFreqSqLowOp_le (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (R : ℝ) :
    ‖kgShiftedFreqSqLowOp (E := E) hv hb0 hb1 hvb R‖ ≤ 1 + R ^ (2 : ℕ) + b :=
  norm_fourierMulCLM_le _ _ _

/-- **The generator is self-adjoint**, because its symbol is real. -/
theorem kgShiftedFreqSqLowOp_inner (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (R : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgShiftedFreqSqLowOp hv hb0 hb1 hvb R f) g : ℂ)
      = inner ℂ f (kgShiftedFreqSqLowOp hv hb0 hb1 hvb R g) :=
  fourierMulCLM_inner _ _ _ (starRingEnd_kgShiftedFreqSqLow v R) f g

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The cosine addition formula through the bounded sine symbol**, cut to a band: the identity
behind the second equation of motion. -/
theorem kgShiftedCos_add_lowPass (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) (t s R : ℝ) (ξ : E) :
    kgShiftedCos v (t + s) ξ * kgLowPass R ξ
      = kgShiftedCos v t ξ * (kgShiftedCos v s ξ * kgLowPass R ξ)
        - kgShiftedFreqSqLow v R ξ
            * (kgShiftedSinOverFreq v t ξ * (kgShiftedSinOverFreq v s ξ * kgLowPass R ξ)) := by
  have hpos := kgShiftedFreq_pos hb1 hvb ξ
  have hne : kgShiftedFreq v ξ ≠ 0 := ne_of_gt hpos
  have hprod : ((kgShiftedFreq v ξ ^ (2 : ℕ) : ℝ) : ℂ)
      * (kgShiftedSinOverFreq v t ξ * kgShiftedSinOverFreq v s ξ)
      = kgShiftedSin v t ξ * kgShiftedSin v s ξ := by
    rw [kgShiftedSinOverFreq, kgShiftedSinOverFreq, kgShiftedSin, kgShiftedSin,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [kgShiftedCos_add t s ξ, kgShiftedFreqSqLow]
  rw [kgLowPass]
  split
  · simp only [mul_one]
    rw [hprod]
  · simp

end Generator

end GaloisForLFunctions.HTGeometry
