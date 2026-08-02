import GaloisForLFunctions.HTGeometry.SchwartzSupL2Bound

/-!
# The `L¹` norm is bounded by a weighted `L²` norm

Writing `‖h‖ = (1+t²)⁻¹ · (1+t²)‖h‖` and applying Hölder's inequality with both exponents equal to
two bounds the `L¹` norm of a Schwartz function by a fixed constant times the `L²` norm of its
quadratic weighting.  The constant is the `L²` norm of `(1+t²)⁻¹`, finite because the square of
that weight is dominated by the weight itself, which is integrable.

Combined with the bound of the supremum by the `L¹` norm of the Fourier transform, this bounds the
supremum of a Schwartz function by an `L²` norm of a quadratic weighting of its transform.

* `integrable_inv_one_add_sq_sq`, `memLp_inv_one_add_sq` : the weight is square integrable.
* `integral_norm_le_weight` : **`∫‖h‖ ≤ C · ‖(1+t²)h‖₂`.**
* `norm_apply_le_weight_fourier` : **`‖f x‖ ≤ C · ‖(1+t²)·𝓕f‖₂`.**
-/

open scoped Real SchwartzMap FourierTransform ENNReal
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The weight is square integrable -/

theorem one_add_sq_pos (t : ℝ) : (0 : ℝ) < 1 + t ^ 2 := by positivity

theorem continuous_inv_one_add_sq : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun t => (one_add_sq_pos t).ne'

theorem integrable_inv_one_add_sq_sq :
    Integrable (fun t : ℝ => ((1 + t ^ 2)⁻¹) ^ 2) (volume : Measure ℝ) := by
  refine Integrable.mono' integrable_inv_one_add_sq ?_ ?_
  · exact (continuous_inv_one_add_sq.pow 2).aestronglyMeasurable
  · filter_upwards with t
    have hpos := one_add_sq_pos t
    have hone : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ((1 + t ^ 2)⁻¹) ^ 2 = (1 + t ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by ring
      _ ≤ (1 + t ^ 2)⁻¹ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [inv_le_one_iff₀]
          exact Or.inr hone
      _ = (1 + t ^ 2)⁻¹ := by ring

theorem memLp_inv_one_add_sq :
    MemLp (fun t : ℝ => (1 + t ^ 2)⁻¹) 2 (volume : Measure ℝ) := by
  refine (memLp_two_iff_integrable_sq ?_).mpr integrable_inv_one_add_sq_sq
  exact continuous_inv_one_add_sq.aestronglyMeasurable

/-! ## The weighted Hölder bound -/

theorem norm_weightSchwartz_apply (h : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖weightSchwartz h t‖ = (1 + t ^ 2) * ‖h t‖ := by
  rw [weightSchwartz_apply, norm_mul]
  congr 1
  have : (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_add_sq_pos t)]

theorem memLp_weight_mul_norm (h : 𝓢(ℝ, ℂ)) :
    MemLp (fun t : ℝ => (1 + t ^ 2) * ‖h t‖) 2 (volume : Measure ℝ) := by
  have hmem : MemLp (fun t : ℝ => ‖weightSchwartz h t‖) 2 (volume : Measure ℝ) :=
    ((weightSchwartz h).memLp 2 (volume : Measure ℝ)).norm
  have hfun : (fun t : ℝ => (1 + t ^ 2) * ‖h t‖) = fun t : ℝ => ‖weightSchwartz h t‖ :=
    funext fun t => (norm_weightSchwartz_apply h t).symm
  rw [hfun]
  exact hmem

/-- **The `L¹` norm of a Schwartz function is bounded by the `L²` norm of its quadratic
weighting.** -/
theorem integral_norm_le_weight (h : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, ‖h t‖
      ≤ (∫ t : ℝ, ((1 + t ^ 2)⁻¹) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        * ‖(weightSchwartz h).toLp 2 (volume : Measure ℝ)‖ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hf_nonneg : (0 : ℝ → ℝ) ≤ᵐ[(volume : Measure ℝ)] fun t : ℝ => (1 + t ^ 2)⁻¹ := by
    filter_upwards with t
    positivity
  have hg_nonneg : (0 : ℝ → ℝ) ≤ᵐ[(volume : Measure ℝ)]
      fun t : ℝ => (1 + t ^ 2) * ‖h t‖ := by
    filter_upwards with t
    have := one_add_sq_pos t
    positivity
  have hmemf : MemLp (fun t : ℝ => (1 + t ^ 2)⁻¹) (ENNReal.ofReal 2) (volume : Measure ℝ) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact memLp_inv_one_add_sq
  have hmemg : MemLp (fun t : ℝ => (1 + t ^ 2) * ‖h t‖) (ENNReal.ofReal 2)
      (volume : Measure ℝ) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact memLp_weight_mul_norm h
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf_nonneg hg_nonneg
    hmemf hmemg
  have hleft : (∫ t : ℝ, (1 + t ^ 2)⁻¹ * ((1 + t ^ 2) * ‖h t‖)) = ∫ t : ℝ, ‖h t‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (1 + t ^ 2)⁻¹ * ((1 + t ^ 2) * ‖h t‖) = ‖h t‖
    rw [← mul_assoc, inv_mul_cancel₀ (one_add_sq_pos t).ne', one_mul]
  have hright : (∫ t : ℝ, ((1 + t ^ 2) * ‖h t‖) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      = ‖(weightSchwartz h).toLp 2 (volume : Measure ℝ)‖ := by
    have hsq : (∫ t : ℝ, ((1 + t ^ 2) * ‖h t‖) ^ (2 : ℝ))
        = ‖(weightSchwartz h).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
      rw [norm_toLp_sq_eq_integral]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ((1 + t ^ 2) * ‖h t‖) ^ (2 : ℝ) = ‖weightSchwartz h t‖ ^ 2
      rw [norm_weightSchwartz_apply h t, ← Real.rpow_natCast ((1 + t ^ 2) * ‖h t‖) 2]
      norm_num
    rw [hsq, ← Real.rpow_natCast ‖(weightSchwartz h).toLp 2 (volume : Measure ℝ)‖ 2,
      ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hleft, hright] at hholder
  exact hholder

/-- **The supremum of a Schwartz function is bounded by the `L²` norm of the quadratic weighting
of its Fourier transform.** -/
theorem norm_apply_le_weight_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖f x‖
      ≤ (∫ t : ℝ, ((1 + t ^ 2)⁻¹) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        * ‖(weightSchwartz (fourierSCLM f)).toLp 2 (volume : Measure ℝ)‖ := by
  refine le_trans (norm_apply_le_integral_norm_fourier f x) ?_
  have hfun : (fun t : ℝ => ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖)
      = fun t : ℝ => ‖(fourierSCLM f) t‖ := by
    funext t
    rw [fourierSCLM_apply]
  rw [hfun]
  exact integral_norm_le_weight (fourierSCLM f)

end GaloisForLFunctions

end
