import GaloisForLFunctions.RHTower.SteinhausAffineCircleMean

open MeasureTheory Complex
open scoped ENNReal ComplexConjugate

noncomputable section
namespace RHTower
open SteinhausModel

/-- Exact original-law squared density cost of prescribing one circle mean. -/
theorem integral_sq_steinhausAffineCircleWeight (m : ℂ) :
    (∫ x, steinhausAffineCircleWeight m x ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
      1 + 2 * ‖m‖ ^ 2 := by
  have hp (x : ℝ) : (steinhausAffineCircleWeight m x : ℂ) ^ 2 =
      ((1 + 2 * ‖m‖ ^ 2 : ℝ) : ℂ) +
        (2 * conj m) * charFactor 1 x + (2 * m) * charFactor (-1) x +
        conj m ^ 2 * charFactor 2 x + m ^ 2 * charFactor (-2) x := by
    have hs : charFactor 1 x * charFactor 1 x = charFactor 2 x := by
      simpa using (charFactor_add 1 1 x).symm
    have ht : charFactor (-1) x * charFactor (-1) x = charFactor (-2) x := by
      simpa using (charFactor_add (-1) (-1) x).symm
    have hi : charFactor 1 x * charFactor (-1) x = 1 := by
      simpa [charFactor_zero] using (charFactor_add 1 (-1) x).symm
    rw [steinhausAffineCircleWeight_coe]
    calc
      _ = 1 + 2 * (conj m * m) * (charFactor 1 x * charFactor (-1) x) +
          (2 * conj m) * charFactor 1 x + (2 * m) * charFactor (-1) x +
          conj m ^ 2 * (charFactor 1 x * charFactor 1 x) +
          m ^ 2 * (charFactor (-1) x * charFactor (-1) x) := by ring
      _ = _ := by
        rw [hs, ht, hi, Complex.conj_mul']
        push_cast
        ring
  have hi (c : ℂ) (k : ℤ) : Integrable (fun x => c * charFactor k x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := (integrable_charFactor k).const_mul c
  have h0 : Integrable (fun _ : ℝ => ((1 + 2 * ‖m‖ ^ 2 : ℝ) : ℂ))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := integrable_const _
  have h1 : Integrable (fun x => ((1 + 2 * ‖m‖ ^ 2 : ℝ) : ℂ) +
      (2 * conj m) * charFactor 1 x) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    h0.add (hi (2 * conj m) 1)
  have h2 : Integrable (fun x => ((1 + 2 * ‖m‖ ^ 2 : ℝ) : ℂ) +
      (2 * conj m) * charFactor 1 x + (2 * m) * charFactor (-1) x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := h1.add (hi (2 * m) (-1))
  have h3 : Integrable (fun x => ((1 + 2 * ‖m‖ ^ 2 : ℝ) : ℂ) +
      (2 * conj m) * charFactor 1 x + (2 * m) * charFactor (-1) x +
      conj m ^ 2 * charFactor 2 x) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    h2.add (hi (conj m ^ 2) 2)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_pow, hp]
  rw [integral_add h3 (hi (m ^ 2) (-2)),
    integral_add h2 (hi (conj m ^ 2) 2),
    integral_add h1 (hi (2 * m) (-1)), integral_add h0 (hi (2 * conj m) 1),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  simp [charInt]

/-- The concrete phase law with the finite affine Fourier density. -/
def steinhausAffineCircleMeasure (m : ℂ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (steinhausAffineCircleWeight m x))

theorem isProbabilityMeasure_steinhausAffineCircleMeasure {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) :
    IsProbabilityMeasure (steinhausAffineCircleMeasure m) := by
  constructor
  rw [steinhausAffineCircleMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (continuous_steinhausAffineCircleWeight m).integrableOn_Icc
      (Filter.Eventually.of_forall (steinhausAffineCircleWeight_nonneg hm)),
    integral_steinhausAffineCircleWeight]
  norm_num

/-- Exact change of measure, retaining the original uniform phase interval. -/
theorem integral_steinhausAffineCircleMeasure {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) (f : ℝ → F) :
    (∫ x, f x ∂steinhausAffineCircleMeasure m) =
      ∫ x, steinhausAffineCircleWeight m x • f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [steinhausAffineCircleMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_steinhausAffineCircleWeight m).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (steinhausAffineCircleWeight_nonneg hm x)])

/-- The actual biased probability law has precisely the requested complex phase mean. -/
theorem integral_phase_steinhausAffineCircleMeasure {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) :
    (∫ x, charFactor 1 x ∂steinhausAffineCircleMeasure m) = m := by
  rw [integral_steinhausAffineCircleMeasure hm]
  simpa only [Complex.real_smul] using integral_steinhausAffineCircleWeight_mul_phase m

end RHTower
