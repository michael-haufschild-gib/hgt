import GaloisForLFunctions.RHTower.HedenmalmGaussianHankelRH

/-!
# Gaussian-window moment rescaling and the cooling limit

Strong Gaussian cooling `tau -> infinity` concentrates the window at the origin.  Two exact scalar
laws drive the moment-defect recession.

* `weightedMoment_gaussianWindow_rescale` is the change of variables `x = y / sqrt tau`, writing the
  `m`-th Gaussian-windowed moment of a density `J` as `(sqrt tau)⁻¹ ^ (m+1)` times the *cooled
  moment* `∫ y^m exp(-y^2) J(y / sqrt tau) dy`.

* `tendsto_gaussianCooledMoment` is the dominated-convergence limit of the cooled moment: as
  `tau -> infinity` the rescaled density `J(y / sqrt tau)` converges to the constant `J 0`, so the
  cooled moment tends to `J 0` times the fixed Gaussian moment `∫ y^m exp(-y^2) dy`.

Together these are the diagonal-congruence factor and the entrywise Hankel limit `K_tau -> J(0) G`
underlying eventual positive-definiteness of every finite Gaussian Hankel section.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace RHTower

/-- Every real monomial is integrable against the standard Gaussian weight `exp(-y^2)`. -/
theorem integrable_pow_mul_exp_neg_sq (m : ℕ) :
    Integrable (fun y : ℝ => y ^ m * Real.exp (-y ^ 2)) := by
  letI := gaussianWindowMeasure_finite (tau := 1) one_pos
  have hmu := gaussianWindowMeasure_hasEntireExponentialMoments (tau := 1) one_pos
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (gaussianWindowMeasure 1) := memLp_top_const 1
  have h1 : Integrable (fun x : ℝ => x ^ m) (gaussianWindowMeasure 1) := by
    have := integrable_monomial_mul_of_entireExponentialMoments hmu (fun _ => (1 : ℝ)) hconst m
    simpa using this
  rw [gaussianWindowMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      (by fun_prop : AEMeasurable
        (fun x : ℝ => ENNReal.ofReal (Real.exp (-(1 : ℝ) * x ^ 2))) volume)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
  simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] at h1
  have hcomm : (fun x : ℝ => Real.exp (-(1 : ℝ) * x ^ 2) * x ^ m)
      = fun y : ℝ => y ^ m * Real.exp (-y ^ 2) := by
    funext x; rw [neg_one_mul]; ring
  rwa [hcomm] at h1

/-- **Gaussian moment rescaling.**  The `m`-th Gaussian-windowed moment of `J` equals
`(sqrt tau)⁻¹ ^ (m+1)` times the cooled moment `∫ y^m exp(-y^2) J(y / sqrt tau) dy`, by the change
of variables `x = y / sqrt tau`.  Holds for every density `J`. -/
theorem weightedMoment_gaussianWindow_rescale {tau : ℝ} (htau : 0 < tau) (J : ℝ → ℝ) (m : ℕ) :
    weightedMoment (gaussianWindowMeasure tau) J m
      = (Real.sqrt tau)⁻¹ ^ (m + 1) *
          ∫ y, y ^ m * Real.exp (-y ^ 2) * J ((Real.sqrt tau)⁻¹ * y) := by
  have hsqrt : (0 : ℝ) < Real.sqrt tau := Real.sqrt_pos.mpr htau
  set c : ℝ := (Real.sqrt tau)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr hsqrt
  have hτc : tau * c ^ 2 = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt htau.le, mul_inv_cancel₀ htau.ne']
  have hunfold : weightedMoment (gaussianWindowMeasure tau) J m
      = ∫ x, Real.exp (-tau * x ^ 2) * (x ^ m * J x) := by
    rw [weightedMoment, gaussianWindowMeasure,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    simp_rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [hunfold]
  have hcv := Measure.integral_comp_mul_left
    (fun x => Real.exp (-tau * x ^ 2) * (x ^ m * J x)) c
  rw [abs_of_pos (inv_pos.mpr hcpos), smul_eq_mul] at hcv
  have hmain : (∫ x, Real.exp (-tau * x ^ 2) * (x ^ m * J x))
      = c * ∫ y, Real.exp (-tau * (c * y) ^ 2) * ((c * y) ^ m * J (c * y)) := by
    rw [hcv, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  rw [hmain]
  have hinner : (∫ y, Real.exp (-tau * (c * y) ^ 2) * ((c * y) ^ m * J (c * y)))
      = c ^ m * ∫ y, y ^ m * Real.exp (-y ^ 2) * J (c * y) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hexp : Real.exp (-tau * (c * y) ^ 2) = Real.exp (-y ^ 2) := by
      congr 1; linear_combination (-y ^ 2) * hτc
    rw [hexp, mul_pow]
    ring
  rw [hinner, ← mul_assoc, ← pow_succ']

/-- **Cooling limit of the cooled moment.**  For a bounded continuous density, the cooled moment
`∫ y^m exp(-y^2) J(y / sqrt tau) dy` converges as `tau -> infinity` to `J 0` times the fixed Gaussian
moment `∫ y^m exp(-y^2) dy`, by dominated convergence with dominating function `C * ‖y^m exp(-y^2)‖`. -/
theorem tendsto_gaussianCooledMoment (J : ℝ → ℝ) (hJc : Continuous J)
    {C : ℝ} (hJb : ∀ x, |J x| ≤ C) (m : ℕ) :
    Tendsto (fun tau : ℝ => ∫ y, y ^ m * Real.exp (-y ^ 2) * J ((Real.sqrt tau)⁻¹ * y)) atTop
      (𝓝 ((∫ y, y ^ m * Real.exp (-y ^ 2)) * J 0)) := by
  set g : ℝ → ℝ := fun y => y ^ m * Real.exp (-y ^ 2) with hg
  have hgc : Continuous g :=
    (continuous_pow m).mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
  have hgint : Integrable g := integrable_pow_mul_exp_neg_sq m
  rw [← integral_mul_const]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => C * ‖g y‖)
  · filter_upwards with tau
    exact (hgc.mul (hJc.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards with tau
    filter_upwards with y
    rw [norm_mul]
    calc ‖g y‖ * ‖J ((Real.sqrt tau)⁻¹ * y)‖ ≤ ‖g y‖ * C := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [Real.norm_eq_abs]; exact hJb _
      _ = C * ‖g y‖ := mul_comm _ _
  · exact hgint.norm.const_mul C
  · filter_upwards with y
    have hpt : Tendsto (fun tau : ℝ => J ((Real.sqrt tau)⁻¹ * y)) atTop (𝓝 (J 0)) := by
      have h0 : Tendsto (fun tau : ℝ => (Real.sqrt tau)⁻¹ * y) atTop (𝓝 (0 * y)) :=
        Tendsto.mul_const y ((Real.tendsto_sqrt_atTop.comp tendsto_id).inv_tendsto_atTop)
      rw [zero_mul] at h0
      exact (hJc.tendsto 0).comp h0
    exact hpt.const_mul (g y)

end RHTower
