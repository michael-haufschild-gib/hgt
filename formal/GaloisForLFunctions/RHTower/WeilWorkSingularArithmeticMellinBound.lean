import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A uniform one-sided bound for the source Mellin integral

The small-parameter signed estimate gives an integrable upper envelope.
Absolute Mellin convergence is supplied independently by the actual source.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private def mellinUpperEnvelope (C D t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun t => C * t ^ (-11 / 12 : ℝ)) t +
    (Ioi (1 : ℝ)).indicator (fun t => D * t ^ (-5 / 4 : ℝ)) t

private theorem integrable_mellinUpperEnvelope (C D : ℝ) :
    Integrable (mellinUpperEnvelope C D) := by
  have h0 : IntegrableOn (fun t : ℝ => t ^ (-11 / 12 : ℝ)) (Ioo 0 2) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num)
  have h1 := h0.mono_set (show Ioc (0 : ℝ) 1 ⊆ Ioo 0 2 from fun _ ht => ⟨ht.1, by linarith [ht.2]⟩)
  have h2 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)
  exact (IntegrableOn.integrable_indicator (h1.const_mul C) measurableSet_Ioc).add
    (IntegrableOn.integrable_indicator (h2.const_mul D) measurableSet_Ioi)

private theorem re_mellinIntegrand (F : ℝ → ℂ) (σ t : ℝ) (ht : 0 < t) :
    ((t : ℂ) ^ ((σ : ℂ) / 2 - 1) * F t).re =
      t ^ (σ / 2 - 1) * (F t).re := by
  have he : (σ : ℂ) / 2 - 1 = ((σ / 2 - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_cpow ht.le]
  simp

/-- A fixed real upper envelope for absolutely convergent Gaussian-type Mellin profiles. -/
theorem exists_re_mellin_le_of_profile_bounds (F : ℝ → ℂ)
    (hconv : ∀ σ : ℝ, 1 < σ → σ < 3 / 2 → MellinConvergent F ((σ : ℂ) / 2))
    (hsmall : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (F t).re ≤ C * t ^ (-5 / 12 : ℝ))
    (hlarge : ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t → ‖F t‖ ≤ D / t) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → σ < 3 / 2 →
      (mellin F ((σ : ℂ) / 2)).re ≤ B := by
  obtain ⟨C, hC0, hC⟩ := hsmall
  obtain ⟨D, hD0, hD⟩ := hlarge
  refine ⟨∫ t in Ioi (0 : ℝ), mellinUpperEnvelope C D t, fun σ hσ hσ' => ?_⟩
  have hi := hconv σ hσ hσ'
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) / 2 - 1) *
    F t) (Ioi 0) at hi
  have hr : IntegrableOn (fun t : ℝ => t ^ (σ / 2 - 1) *
      (F t).re) (Ioi 0) :=
    IntegrableOn.congr_fun hi.re (fun t ht => re_mellinIntegrand F σ t ht) measurableSet_Ioi
  have he : (mellin (F) ((σ : ℂ) / 2)).re =
      ∫ t in Ioi (0 : ℝ), t ^ (σ / 2 - 1) * (F t).re := by
    simp only [mellin, smul_eq_mul]
    refine (integral_re hi).symm.trans ?_
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => re_mellinIntegrand F σ t ht
  rw [he]
  refine integral_mono_ae hr (integrable_mellinUpperEnvelope C D).restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  by_cases ht1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
    have hm' : t ∉ Ioi (1 : ℝ) := not_lt.mpr ht1
    simp only [mellinUpperEnvelope, indicator_of_mem hm, indicator_of_notMem hm', add_zero]
    calc
      t ^ (σ / 2 - 1) * (F t).re ≤
          t ^ (σ / 2 - 1) * (C * t ^ (-5 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hC t ht ht1) (Real.rpow_nonneg ht.le _)
      _ = C * t ^ (σ / 2 - 1 + (-5 / 12 : ℝ)) := by rw [Real.rpow_add ht]; ring
      _ ≤ C * t ^ (-11 / 12 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)) hC0
  · have ht1' : 1 < t := lt_of_not_ge ht1
    have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
    simp only [mellinUpperEnvelope, indicator_of_notMem hm,
      indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht1'), zero_add]
    have hreal : (F t).re ≤ D / t :=
      (Complex.re_le_norm _).trans (hD t ht)
    calc
      t ^ (σ / 2 - 1) * (F t).re ≤
          t ^ (σ / 2 - 1) * (D / t) :=
        mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg ht.le _)
      _ = D * t ^ (σ / 2 - 1 + (-1 : ℝ)) := by
        rw [Real.rpow_add ht, Real.rpow_neg_one]
        ring
      _ ≤ D * t ^ (-5 / 4 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1'.le (by linarith)) hD0

/-- The real Mellin transform stays uniformly bounded above to the right of one. -/
theorem exists_re_mellin_sourceGaussianProfile_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → σ < 3 / 2 →
      (mellin (sourceGaussianProfile lam) ((σ : ℂ) / 2)).re ≤ B :=
  exists_re_mellin_le_of_profile_bounds (sourceGaussianProfile lam)
    (fun _ hσ _ => mellinConvergent_sourceGaussianProfile hW (by simpa using hσ))
    (exists_re_sourceGaussianProfile_le hW) (exists_norm_sourceGaussianProfile_le hW)

end RHTower.WeilSingularArithmetic
