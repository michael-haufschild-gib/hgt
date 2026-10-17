import GaloisForLFunctions.BiScaleUncertainty.SharpPairedCollarAsymptotics
import GaloisForLFunctions.BiScaleUncertainty.FourthRootCutoffNormalization
import GaloisForLFunctions.BiScaleUncertainty.StrictPairedCollarLimit

/-!
# Exact fourth-root saturation of the delayed paired hierarchy

The paired branch eventually wins. Its sharp physical tail, together with a
quantitative floor-square-root comparison, gives leading coefficient four at
the fourth-root scale of the source cutoff. The same estimate supplies an
unconditional lower certificate for every actual smooth grid source.
-/

set_option autoImplicit false
open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem eventually_productCoupled_sharp_leading_error :
    ∀ᶠ n : ℕ in atTop,
      |limitingProductCoupledCoefficient - productCoupledCollarCoefficient n -
        4 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ))| ≤
        24586 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
  filter_upwards [eventually_productCoupled_eq_paired, eventually_ge_atTop 62] with n he hn
  have hn2 : 2 ≤ n := by omega
  have hp := pairedOptimalCoefficient_sharp_leading_error (productAdmittedCutoff_ge_six hn)
  rw [productAdmittedCutoff_add_two hn2, ← he] at hp
  have hm := inverse_sqrt_floor_cutoff_error hn2
  have hinv : 0 ≤ (Nat.sqrt (n + 2) : ℝ)⁻¹ := by positivity
  have hmid :
      |limitingProductCoupledCoefficient - productCoupledCollarCoefficient n -
        4 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ))| ≤
        12293 / (Nat.sqrt (n + 2) : ℝ) := by
    have hp' := abs_le.mp hp
    apply abs_le.mpr
    simp only [div_eq_mul_inv] at hp' hm ⊢
    constructor <;> nlinarith only [hp'.1, hp'.2, hm.1, hm.2, hinv]
  apply hmid.trans
  have hk := mul_le_mul_of_nonneg_left (floorSqrtCutoff_inverse_le hn2)
    (by norm_num : (0 : ℝ) ≤ 12293)
  calc
    12293 / (Nat.sqrt (n + 2) : ℝ) = 12293 * (1 / (Nat.sqrt (n + 2) : ℝ)) := by ring
    _ ≤ 12293 * (2 / Real.sqrt ((n + 2 : ℕ) : ℝ)) := hk
    _ = 24586 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by ring

theorem eventually_productCoupled_scaled_leading_error :
    ∀ᶠ n : ℕ in atTop,
      |Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) *
        (limitingProductCoupledCoefficient - productCoupledCollarCoefficient n) - 4| ≤
        24586 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) := by
  filter_upwards [eventually_productCoupled_sharp_leading_error] with n hn
  have hs : 0 < Real.sqrt ((n + 2 : ℕ) : ℝ) := by positivity
  have ht : 0 < Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hs
  have h := mul_le_mul_of_nonneg_left hn ht.le
  have hl : Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) *
      |limitingProductCoupledCoefficient - productCoupledCollarCoefficient n -
        4 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ))| =
      |Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) *
        (limitingProductCoupledCoefficient - productCoupledCollarCoefficient n) - 4| := by
    calc
      _ = |Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) *
          (limitingProductCoupledCoefficient - productCoupledCollarCoefficient n -
            4 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)))| := by
        rw [abs_mul, abs_of_nonneg ht.le]
      _ = _ := by
        congr 1
        field_simp [ht.ne']
  have hr : Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) *
      (24586 / Real.sqrt ((n + 2 : ℕ) : ℝ)) =
      24586 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) := by
    field_simp [hs.ne', ht.ne']
    nlinarith only [Real.sq_sqrt hs.le]
  rw [hl, hr] at h
  exact h

/-- The delayed hierarchy has exact fourth-root leading coefficient four. -/
theorem productCoupled_sharp_saturation_limit :
    Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) *
      (limitingProductCoupledCoefficient - productCoupledCollarCoefficient n))
      atTop (𝓝 4) := by
  have herr : Tendsto
      (fun n : ℕ => 24586 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_inverse_fourthRoot_collarCutoff.const_mul 24586)
  have hlo : Tendsto
      (fun n : ℕ => 4 - 24586 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)))
      atTop (𝓝 4) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub herr)
  have hhi : Tendsto
      (fun n : ℕ => 4 + 24586 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)))
      atTop (𝓝 4) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herr)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_productCoupled_scaled_leading_error] with n hn
    have h := (abs_le.mp hn).1
    linarith only [h]
  · filter_upwards [eventually_productCoupled_scaled_leading_error] with n hn
    have h := (abs_le.mp hn).2
    linarith only [h]

/-- The fourth-root law gives a uniform certificate on actual source energy. -/
theorem eventually_sharpProductCoupled_source_lower_bound :
    ∀ᶠ n : ℕ in atTop, ∀ f : SmoothLogarithmicGridSource n,
      limitingProductCoupledCoefficient - 4 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) -
        24586 / Real.sqrt ((n + 2 : ℕ) : ℝ) ≤
        biScaleLevyEnergy f.1.1 / RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  filter_upwards [eventually_productCoupled_sharp_leading_error] with n hn
  intro f
  have h := (abs_le.mp hn).2
  have hf := productCoupledCollarCoefficient_le_normalized_energy n f
  linarith only [h, hf]

end
end GaloisForLFunctions.BiScaleUncertainty
