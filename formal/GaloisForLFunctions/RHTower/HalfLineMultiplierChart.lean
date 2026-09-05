import GaloisForLFunctions.HTGeometry.InvariantMultiplierChart
import GaloisForLFunctions.RHTower.CCMActualHeadQuantileGammaChiSquareProducer
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundFrequencyLocalization

/-!
# The half-line Paley--Wiener realization of the Euler multiplier chart

In logarithmic coordinates the two Hardy sides of the critical line are the closed subspaces of
`L²(ℝ)` supported in `Iic b` and in its complement, and multiplication by `p^{-z}` is translation.
A finite Euler denominator `D_t = ∏ (1 - t_p p^{-z})` is then a strict perturbation of the identity
by translations that preserve one side, and the numerator `N_t = ∏ (1 - t_p p^{z-1})` preserves the
other side.  Hence both are invertible and preserve their side exactly, which is precisely the
input of the abstract multiplier chart:

`S(u N_t D_t⁻¹) = D_t S(u)`.
-/

namespace RHTower

open MeasureTheory Set


noncomputable section

/-- Nested indicator cutoffs compose to the cutoff of the smaller set. -/
theorem indicatorCutoff_mul_of_subset (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) :
    indicatorCutoff s hs * indicatorCutoff t ht = indicatorCutoff s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae s hs (indicatorCutoff t ht f),
    indicatorCutoff_ae t ht f, indicatorCutoff_ae s hs f] with x houter hinner htarget
  rw [show ((indicatorCutoff s hs * indicatorCutoff t ht) f)
      = indicatorCutoff s hs (indicatorCutoff t ht f) from rfl, houter, htarget]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, hinner,
      Set.indicator_of_mem (hst hxs)]
  · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs]

/-- The same composition in the opposite order. -/
theorem indicatorCutoff_mul_of_superset (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) :
    indicatorCutoff t ht * indicatorCutoff s hs = indicatorCutoff s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae t ht (indicatorCutoff s hs f),
    indicatorCutoff_ae s hs f] with x houter hinner
  rw [show ((indicatorCutoff t ht * indicatorCutoff s hs) f)
      = indicatorCutoff t ht (indicatorCutoff s hs f) from rfl, houter]
  by_cases hxt : x ∈ t
  · rw [Set.indicator_of_mem hxt]
  · rw [Set.indicator_of_notMem hxt, hinner, Set.indicator_of_notMem (fun hx => hxt (hst hx))]

theorem logHalflineCutoff_mul_of_le (b c : ℝ) (hbc : b ≤ c) :
    logHalflineCutoff b * logHalflineCutoff c = logHalflineCutoff b :=
  indicatorCutoff_mul_of_subset _ _ _ _ (Set.Iic_subset_Iic.mpr hbc)

theorem logHalflineCutoff_mul_of_ge (b c : ℝ) (hbc : b ≤ c) :
    logHalflineCutoff c * logHalflineCutoff b = logHalflineCutoff b :=
  indicatorCutoff_mul_of_superset _ _ _ _ (Set.Iic_subset_Iic.mpr hbc)

theorem logHalflineCutoff_idempotent (b : ℝ) : IsIdempotentElem (logHalflineCutoff b) :=
  indicatorCutoff_idempotent _ _

/-- Functions supported in the lower logarithmic half-line `Iic b`. -/
def logHalflineLower (b : ℝ) : Submodule ℂ SoninL2 :=
  LinearMap.range ((logHalflineCutoff b : SoninL2 →L[ℂ] SoninL2) : SoninL2 →ₗ[ℂ] SoninL2)

/-- Functions supported in the upper logarithmic half-line `Ioi b`. -/
def logHalflineUpper (b : ℝ) : Submodule ℂ SoninL2 :=
  LinearMap.range (((1 - logHalflineCutoff b : SoninL2 →L[ℂ] SoninL2)) : SoninL2 →ₗ[ℂ] SoninL2)

theorem mem_logHalflineLower {b : ℝ} {f : SoninL2} :
    f ∈ logHalflineLower b ↔ logHalflineCutoff b f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    have h : logHalflineCutoff b * logHalflineCutoff b = logHalflineCutoff b :=
      logHalflineCutoff_idempotent b
    exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T g) h
  · intro h
    exact ⟨f, h⟩

theorem mem_logHalflineUpper {b : ℝ} {f : SoninL2} :
    f ∈ logHalflineUpper b ↔ logHalflineCutoff b f = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    have h : logHalflineCutoff b * (1 - logHalflineCutoff b) = 0 := by
      have hi : logHalflineCutoff b * logHalflineCutoff b = logHalflineCutoff b :=
        logHalflineCutoff_idempotent b
      rw [mul_sub, mul_one, hi, sub_self]
    exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T g) h
  · intro h
    refine ⟨f, ?_⟩
    show f - logHalflineCutoff b f = f
    rw [h, sub_zero]

theorem isClosed_logHalflineLower (b : ℝ) : IsClosed (logHalflineLower b : Set SoninL2) := by
  have := ContinuousLinearMap.IsIdempotentElem.isClosed_range (logHalflineCutoff_idempotent b)
  simpa [logHalflineLower] using this

theorem isClosed_logHalflineUpper (b : ℝ) : IsClosed (logHalflineUpper b : Set SoninL2) := by
  have hidem : IsIdempotentElem (1 - logHalflineCutoff b : SoninL2 →L[ℂ] SoninL2) :=
    (logHalflineCutoff_idempotent b).one_sub
  have := ContinuousLinearMap.IsIdempotentElem.isClosed_range hidem
  simpa [logHalflineUpper] using this

theorem apply_mul_soninL2 (A B : SoninL2 →L[ℂ] SoninL2) (f : SoninL2) : (A * B) f = A (B f) := rfl

/-- Nonnegative translations preserve the lower half-line. -/
theorem logTranslationCLM_mem_logHalflineLower (b h : ℝ) (hh : 0 ≤ h) {f : SoninL2}
    (hf : f ∈ logHalflineLower b) : logTranslationCLM h f ∈ logHalflineLower b := by
  rw [mem_logHalflineLower] at hf ⊢
  have hf' : logHalflineCutoff (b + h) f = f := by
    have hswap : logHalflineCutoff (b + h) * logHalflineCutoff b = logHalflineCutoff b :=
      logHalflineCutoff_mul_of_ge b (b + h) (by linarith)
    have hval := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f) hswap
    simp only [apply_mul_soninL2] at hval
    rw [hf] at hval
    exact hval
  have hcov := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f)
    (logHalflineCutoff_mul_logTranslationCLM b h)
  simp only [apply_mul_soninL2] at hcov
  rw [hf'] at hcov
  exact hcov

/-- Nonpositive translations preserve the upper half-line. -/
theorem logTranslationCLM_mem_logHalflineUpper (b h : ℝ) (hh : h ≤ 0) {f : SoninL2}
    (hf : f ∈ logHalflineUpper b) : logTranslationCLM h f ∈ logHalflineUpper b := by
  rw [mem_logHalflineUpper] at hf ⊢
  have hf' : logHalflineCutoff (b + h) f = 0 := by
    have hswap : logHalflineCutoff (b + h) * logHalflineCutoff b = logHalflineCutoff (b + h) :=
      logHalflineCutoff_mul_of_le (b + h) b (by linarith)
    have hval := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f) hswap
    simp only [apply_mul_soninL2] at hval
    rw [hf, map_zero] at hval
    exact hval.symm
  have hcov := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f)
    (logHalflineCutoff_mul_logTranslationCLM b h)
  simp only [apply_mul_soninL2] at hcov
  rw [hf', map_zero] at hcov
  exact hcov

/-- The physical realization of the local Euler denominator `1 - t p^{-z}`. -/
def halflineEulerDenominator (t p : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  1 - ((t / Real.sqrt p : ℝ) : ℂ) • logTranslationCLM (-Real.log p)

/-- The physical realization of the local Euler numerator `1 - t p^{z-1}`. -/
def halflineEulerNumerator (t p : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  1 - ((t / Real.sqrt p : ℝ) : ℂ) • logTranslationCLM (Real.log p)

/-- **`(5)`: the Euler factor is a strict contraction perturbation of the identity.** -/
theorem norm_smul_logTranslationCLM_lt_one (t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p)
    (h : ℝ) : ‖((t / Real.sqrt p : ℝ) : ℂ) • logTranslationCLM h‖ < 1 := by
  have hsqrt : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hlt : |t| / Real.sqrt p < 1 := (div_lt_one hsqrt).mpr ht
  have hc : ‖((t / Real.sqrt p : ℝ) : ℂ)‖ = |t| / Real.sqrt p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hsqrt.le]
  calc ‖((t / Real.sqrt p : ℝ) : ℂ) • logTranslationCLM h‖
      = ‖((t / Real.sqrt p : ℝ) : ℂ)‖ * ‖logTranslationCLM h‖ := norm_smul _ _
    _ ≤ |t| / Real.sqrt p * 1 := by
        rw [hc]
        exact mul_le_mul_of_nonneg_left (norm_logTranslationCLM_le_one h)
          (by positivity)
    _ < 1 := by rw [mul_one]; exact hlt

theorem isUnit_halflineEulerDenominator (t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p) :
    IsUnit (halflineEulerDenominator t p) :=
  (Units.oneSub _ (norm_smul_logTranslationCLM_lt_one t p hp ht _)).isUnit

theorem isUnit_halflineEulerNumerator (t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p) :
    IsUnit (halflineEulerNumerator t p) :=
  (Units.oneSub _ (norm_smul_logTranslationCLM_lt_one t p hp ht _)).isUnit

/-- **`(4)`--`(5)`: the denominator preserves the upper Hardy side exactly.** -/
theorem map_halflineEulerDenominator (t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p) (b : ℝ) :
    Submodule.map ((halflineEulerDenominator t p : SoninL2 →L[ℂ] SoninL2) :
        SoninL2 →ₗ[ℂ] SoninL2) (logHalflineUpper b) = logHalflineUpper b := by
  refine HTGeometry.map_one_sub_eq_of_norm_lt_one (isClosed_logHalflineUpper b) ?_
    (norm_smul_logTranslationCLM_lt_one t p hp ht _)
  intro x hx
  have hlog : (0 : ℝ) < Real.log p := Real.log_pos hp
  have := logTranslationCLM_mem_logHalflineUpper b (-Real.log p) (by linarith) hx
  exact (logHalflineUpper b).smul_mem _ this

/-- **`(4)`--`(5)`: the numerator preserves the lower Hardy side exactly.** -/
theorem map_halflineEulerNumerator (t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p) (b : ℝ) :
    Submodule.map ((halflineEulerNumerator t p : SoninL2 →L[ℂ] SoninL2) :
        SoninL2 →ₗ[ℂ] SoninL2) (logHalflineLower b) = logHalflineLower b := by
  refine HTGeometry.map_one_sub_eq_of_norm_lt_one (isClosed_logHalflineLower b) ?_
    (norm_smul_logTranslationCLM_lt_one t p hp ht _)
  intro x hx
  have hlog : (0 : ℝ) < Real.log p := Real.log_pos hp
  have := logTranslationCLM_mem_logHalflineLower b (Real.log p) hlog.le hx
  exact (logHalflineLower b).smul_mem _ this

/-- **`(4)`: the exact Euler chart of the half-line multiplier kernel.** -/
theorem multiplierKernel_halflineEuler (t p : ℝ) (hp : 1 < p) (ht : |t| < Real.sqrt p) (b : ℝ)
    (u : SoninL2 →L[ℂ] SoninL2)
    (hcomm : u * halflineEulerNumerator t p = halflineEulerNumerator t p * u) :
    HTGeometry.multiplierKernel (logHalflineUpper b) (logHalflineLower b)
        (u * halflineEulerNumerator t p * Ring.inverse (halflineEulerDenominator t p))
      = Submodule.map ((halflineEulerDenominator t p : SoninL2 →L[ℂ] SoninL2) :
          SoninL2 →ₗ[ℂ] SoninL2)
        (HTGeometry.multiplierKernel (logHalflineUpper b) (logHalflineLower b) u) :=
  HTGeometry.multiplierKernel_deformed _ _ u _ _
    (isUnit_halflineEulerDenominator t p hp ht) (isUnit_halflineEulerNumerator t p hp ht)
    (map_halflineEulerDenominator t p hp ht b) (map_halflineEulerNumerator t p hp ht b) hcomm

theorem logTranslationCLM_mul (a h : ℝ) :
    logTranslationCLM a * logTranslationCLM h = logTranslationCLM (a + h) := by
  apply ContinuousLinearMap.ext
  intro f
  exact logTranslationCLM_add_apply a h f

/-- A concrete unimodular archimedean-type multiplier commutes with the Euler numerator, so the
chart is not vacuous. -/
theorem multiplierKernel_halflineEuler_translation (t p : ℝ) (hp : 1 < p)
    (ht : |t| < Real.sqrt p) (b a : ℝ) :
    HTGeometry.multiplierKernel (logHalflineUpper b) (logHalflineLower b)
        (logTranslationCLM a * halflineEulerNumerator t p *
          Ring.inverse (halflineEulerDenominator t p))
      = Submodule.map ((halflineEulerDenominator t p : SoninL2 →L[ℂ] SoninL2) :
          SoninL2 →ₗ[ℂ] SoninL2)
        (HTGeometry.multiplierKernel (logHalflineUpper b) (logHalflineLower b)
          (logTranslationCLM a)) := by
  refine multiplierKernel_halflineEuler t p hp ht b _ ?_
  rw [halflineEulerNumerator, mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
    logTranslationCLM_mul, logTranslationCLM_mul, add_comm]

end

end RHTower
