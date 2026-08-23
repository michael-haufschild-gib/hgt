import GaloisForLFunctions.RHTower.SteinhausProfileLogIntegral

/-!
# The circle projection is sub-Gaussian with proxy one

The projection is bounded in `[−1,1]` and centred, so Hoeffding's lemma gives
`log I₀(x) ≤ x²/2`.  Together with `log I₀(x) ≤ x` this pins the cumulant near the origin, which is
what makes the rate function strictly positive off `q = 0`.
-/

open MeasureTheory ProbabilityTheory Set

namespace HTGeometry

local instance phaseCirclePositiveSub : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- **The Haar integral of any function is its average over one period.** -/
theorem integral_haar_eq_intervalIntegral (f : PhaseCircle → ℝ) :
    (∫ x : PhaseCircle, f x ∂AddCircle.haarAddCircle)
      = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), f ((t : ℝ) : PhaseCircle) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpre := AddCircle.integral_preimage (2 * Real.pi) 0 f
  have hleft : (∫ a in Set.Ioc (0 : ℝ) (0 + 2 * Real.pi), f ((a : ℝ) : PhaseCircle))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), f ((t : ℝ) : PhaseCircle) := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    simp only [zero_add]
  rw [hleft] at hpre
  have hright : (∫ b : PhaseCircle, f b)
      = (2 * Real.pi) * ∫ x : PhaseCircle, f x ∂AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
      ENNReal.toReal_ofReal hpi.le, smul_eq_mul]
  rw [hright] at hpre
  rw [hpre]
  field_simp

/-- **The projection is centred.** -/
theorem integral_steinhausProjection_eq_zero :
    (∫ x : PhaseCircle, steinhausProjection x ∂AddCircle.haarAddCircle) = 0 := by
  rw [integral_haar_eq_intervalIntegral]
  have hcongr : (∫ t in (0 : ℝ)..(2 * Real.pi), steinhausProjection ((t : ℝ) : PhaseCircle))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos t :=
    intervalIntegral.integral_congr fun t _ => steinhausProjection_coe t
  rw [hcongr, integral_cos]
  simp

/-- **Hoeffding's lemma for the circle projection.** -/
theorem steinhausLogLaplace_le_sq (x : ℝ) : steinhausLogLaplace x ≤ x ^ 2 / 2 := by
  have hbound : ∀ᵐ ω ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)),
      steinhausProjection ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards with ω
    have h := abs_steinhausProjection_le_one ω
    rw [abs_le] at h
    exact ⟨h.1, h.2⟩
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := AddCircle.haarAddCircle (T := 2 * Real.pi)) (X := steinhausProjection)
    continuous_steinhausProjection.aemeasurable hbound integral_steinhausProjection_eq_zero
  have hproxy : ((‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2 : NNReal) = 1 := by norm_num
  rw [hproxy] at hsub
  have hcgf := hsub.cgf_le x
  rw [steinhausLogLaplace_eq_cgf]
  simpa using hcgf

end

end HTGeometry
