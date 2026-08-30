import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.HilbertClosedRange

/-!
# Arbitrarily small symbols destroy closed range

An injective multiplication operator on `L²` whose symbol becomes arbitrarily small on sets of
positive finite measure has dense but nonclosed range.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℂ} {C : ℝ}

/-- **No transverse lower bound.**  If the symbol is arbitrarily small on sets of positive finite
measure, the multiplication operator is not bounded below on the orthogonal complement of its
kernel. -/
theorem not_hasTransverseLowerBound_lpBoundedMulCLM
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hinj : Function.Injective (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC))
    (hsmall : ∀ c : ℝ, 0 < c → ∃ S : Set α, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ∞ ∧
      ∀ᵐ x ∂μ, x ∈ S → ‖φ x‖ ≤ c) :
    ¬ ContinuousLinearMap.HasTransverseLowerBound (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC) := by
  set T := lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC with hT
  rintro ⟨c, hc, hbound⟩
  obtain ⟨S, hSm, hS0, hSfin, hSle⟩ := hsmall (c / 2) (by linarith)
  have hker : LinearMap.ker (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  set f : Lp ℂ 2 μ := indicatorConstLp 2 hSm hSfin (1 : ℂ) with hf
  set g : Lp ℂ 2 μ := indicatorConstLp 2 hSm hSfin (((c / 2 : ℝ) : ℂ)) with hg
  have hrpow : (0 : ℝ) < μ.real S ^ (1 / (2 : ℝ≥0∞).toReal) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact ENNReal.toReal_pos hS0 hSfin
  have hfnorm : ‖f‖ = μ.real S ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [hf, norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp
  have hgnorm : ‖g‖ = (c / 2) * μ.real S ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [hg, norm_indicatorConstLp (by norm_num) (by norm_num)]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hfpos : 0 < ‖f‖ := by rw [hfnorm]; exact hrpow
  have hmem : f ∈ (LinearMap.ker (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ))ᗮ := by
    rw [hker, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  have h1 : c * ‖f‖ ≤ ‖T f‖ := hbound f hmem
  have h2 : ‖T f‖ ≤ ‖g‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f,
      indicatorConstLp_coeFn (p := 2) (hs := hSm) (hμs := hSfin) (c := (1 : ℂ)),
      indicatorConstLp_coeFn (p := 2) (hs := hSm) (hμs := hSfin) (c := ((c / 2 : ℝ) : ℂ)),
      hSle] with x h1x h2x h3x h4x
    rw [show ((T f : Lp ℂ 2 μ) : α → ℂ) x = φ x * ((f : Lp ℂ 2 μ) : α → ℂ) x from h1x,
      show ((f : Lp ℂ 2 μ) : α → ℂ) x = S.indicator (fun _ => (1 : ℂ)) x from h2x,
      show ((g : Lp ℂ 2 μ) : α → ℂ) x = S.indicator (fun _ => ((c / 2 : ℝ) : ℂ)) x from h3x]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact h4x hx
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rw [hgnorm, ← hfnorm] at h2
  nlinarith [h1, h2, hfpos]

/-- **Dense nonclosed range.**  An almost-everywhere nonvanishing real symbol that is
arbitrarily small on sets of positive finite measure gives an injective multiplication operator
with dense but nonclosed range. -/
theorem not_isClosed_range_lpBoundedMulCLM
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hinj : Function.Injective (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC))
    (hsmall : ∀ c : ℝ, 0 < c → ∃ S : Set α, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ∞ ∧
      ∀ᵐ x ∂μ, x ∈ S → ‖φ x‖ ≤ c) :
    ¬ IsClosed (Set.range (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC)) := fun hclosed =>
  not_hasTransverseLowerBound_lpBoundedMulCLM hφ hC0 hC hinj hsmall
    ((ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range _).mpr hclosed)

end

end GaloisForLFunctions.HTGeometry
