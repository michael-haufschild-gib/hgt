import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxProfile
import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridUniformTail
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Exact derivative-energy translation bounds for actual compact sources

The compact derivative defines a physical L² velocity. Its primitive is the
source minus its origin value. Box contraction then controls every translation
increment by the actual derivative energy, with coefficient exactly the squared lag.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

/-- The actual L² class of a compact continuous real source. -/
def compactSourceVelocity (f : C_c(ℝ, ℝ)) : Velocity :=
  (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp (f : ℝ → ℝ)

theorem ae_compactSourceVelocity (f : C_c(ℝ, ℝ)) :
    compactSourceVelocity f =ᵐ[volume] (f : ℝ → ℝ) := MemLp.coeFn_toLp _

/-- The actual compact derivative, represented in physical L² by continuity and compact support. -/
def compactDerivativeVelocity (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) : Velocity :=
  ((hf.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport f.hasCompactSupport.deriv).toLp
    (deriv (f : ℝ → ℝ))

theorem ae_compactDerivativeVelocity (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    compactDerivativeVelocity f hf =ᵐ[volume] deriv (f : ℝ → ℝ) := MemLp.coeFn_toLp _

theorem norm_sq_compactSourceVelocity (f : C_c(ℝ, ℝ)) :
    ‖compactSourceVelocity f‖ ^ 2 = ∫ u, (f u) ^ 2 := by
  rw [norm_sq_velocity]
  apply integral_congr_ae
  filter_upwards [ae_compactSourceVelocity f] with u hu
  exact congrArg (fun a : ℝ => a ^ 2) hu

/-- The constructed derivative velocity has exactly the source's ordinary Dirichlet energy. -/
theorem norm_sq_compactDerivativeVelocity (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    ‖compactDerivativeVelocity f hf‖ ^ 2 = ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  rw [norm_sq_velocity]
  apply integral_congr_ae
  filter_upwards [ae_compactDerivativeVelocity f hf] with u hu
  exact congrArg (fun a : ℝ => a ^ 2) hu

/-- The fundamental theorem identifies the derivative velocity's actual primitive everywhere. -/
theorem primitive_compactDerivativeVelocity (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (t : ℝ) :
    primitive (compactDerivativeVelocity f hf) t = f t - f 0 := by
  unfold primitive
  calc
    _ = ∫ u in 0..t, deriv (f : ℝ → ℝ) u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_compactDerivativeVelocity f hf] with u hu
      exact fun _ => hu
    _ = _ := intervalIntegral.integral_deriv_eq_sub
      (fun u _ => (hf.differentiable (by norm_num)).differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 t)

/-- Every positive translation increment is exactly a scaled box average of the derivative. -/
theorem physicalTranslation_compactSource_sub_eq_box (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {t : ℝ} (ht : 0 < t) :
    physicalTranslation t (compactSourceVelocity f) - compactSourceVelocity f =
      t • physicalBoxAverage (Real.log t) (compactDerivativeVelocity f hf) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (physicalTranslation t (compactSourceVelocity f)) (compactSourceVelocity f),
    ae_physicalTranslation t (compactSourceVelocity f),
    ae_physicalTranslate_pullback t (ae_compactSourceVelocity f), ae_compactSourceVelocity f,
    Lp.coeFn_smul t (physicalBoxAverage (Real.log t) (compactDerivativeVelocity f hf)),
    ae_physicalBoxAverage (Real.log t) (compactDerivativeVelocity f hf)] with u hs ht' hshift hsource hm hb
  simp only [Pi.sub_apply] at hs
  simp only [Pi.smul_apply, smul_eq_mul] at hm
  rw [hs, ht', hshift, hsource, hm, hb, physicalBoxProfile, Real.exp_log ht,
    primitive_compactDerivativeVelocity, primitive_compactDerivativeVelocity]
  field_simp [ht.ne']
  ring

private theorem norm_compactSource_translation_sub_le_pos (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {t : ℝ} (ht : 0 < t) :
    ‖physicalTranslation t (compactSourceVelocity f) - compactSourceVelocity f‖ ≤
      t * ‖compactDerivativeVelocity f hf‖ := by
  rw [physicalTranslation_compactSource_sub_eq_box f hf ht, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left (physicalBoxAverage_norm_le _ _) ht.le

/-- Every signed lag obeys the exact derivative-norm translation bound. -/
theorem norm_compactSource_translation_sub_le (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (t : ℝ) :
    ‖physicalTranslation t (compactSourceVelocity f) - compactSourceVelocity f‖ ≤
      |t| * ‖compactDerivativeVelocity f hf‖ := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have he : ‖physicalTranslation t (compactSourceVelocity f) - compactSourceVelocity f‖ =
        ‖physicalTranslation (-t) (compactSourceVelocity f) - compactSourceVelocity f‖ := by
      calc
        _ = ‖physicalTranslation (-t)
            (physicalTranslation t (compactSourceVelocity f) - compactSourceVelocity f)‖ :=
          (physicalTranslation_norm _ _).symm
        _ = ‖compactSourceVelocity f - physicalTranslation (-t) (compactSourceVelocity f)‖ := by
          rw [map_sub, physicalTranslation_inverse]
        _ = _ := norm_sub_rev _ _
    rw [he, abs_of_neg ht]
    exact norm_compactSource_translation_sub_le_pos f hf (neg_pos.mpr ht)
  · subst t
    rw [physicalTranslation_zero, sub_self, norm_zero, abs_zero, zero_mul]
  · rw [abs_of_pos ht]
    exact norm_compactSource_translation_sub_le_pos f hf ht

/-- The norm of the constructed translated class equals the literal source difference integral. -/
theorem integral_compactSource_translation_sq_eq_norm (f : C_c(ℝ, ℝ)) (t : ℝ) :
    (∫ u, (f (u + t) - f u) ^ 2) =
      ‖physicalTranslation t (compactSourceVelocity f) - compactSourceVelocity f‖ ^ 2 := by
  rw [norm_sq_velocity]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (physicalTranslation t (compactSourceVelocity f)) (compactSourceVelocity f),
    ae_physicalTranslation t (compactSourceVelocity f),
    ae_physicalTranslate_pullback t (ae_compactSourceVelocity f), ae_compactSourceVelocity f]
    with u hs ht hshift hsource
  simp only [Pi.sub_apply] at hs
  rw [hs, ht, hshift, hsource]

/-- The actual smooth source has translation error at most its derivative energy times squared lag. -/
theorem integral_compactSource_translation_sq_le (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (t : ℝ) :
    (∫ u, (f (u + t) - f u) ^ 2) ≤ t ^ 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  rw [integral_compactSource_translation_sq_eq_norm]
  have hs := pow_le_pow_left₀ (norm_nonneg _)
    (norm_compactSource_translation_sub_le f hf t) 2
  simpa only [mul_pow, sq_abs, norm_sq_compactDerivativeVelocity] using hs

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
