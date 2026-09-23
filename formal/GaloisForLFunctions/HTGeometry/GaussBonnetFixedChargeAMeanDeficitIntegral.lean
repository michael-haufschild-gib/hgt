import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitIntegrand

/-!
# Exact sixth-order integral identity for the actual mean deficit

The fundamental theorem of calculus along the positive short path
identifies the physical energy difference with the normalized integrand.
Its limiting line integrates to the explicit positive coefficient.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

private theorem mean_deficit_path_normalized_hasDerivAt (w φ τ l : ℝ) :
    ∀ u ∈ Icc (0 : ℝ) 1,
    HasDerivAt (fun x => egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMeanDeficitPathRadius w φ τ x) /
        egbCoexistenceASymmetricRatio τ ^ (6 : ℕ))
      (egbFixedChargeAMeanDeficitIntegrand w φ τ u) u := by
  intro u hu
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  have hscale := (egbFixedChargeAMeanDeficitPathScale_mapsTo τ φ hu).1
  have hv : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ * u := by linarith [hd.2]
  have hg := egbFixedChargeA_mean_gibbs_derivative w φ τ l
    (log (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ * u))
  rw [exp_log hv, ← egbFixedChargeAMeanDeficitPathRadius_mean_formula] at hg
  have h := (hg.comp u (egbFixedChargeAMeanDeficitPathRadius_hasDerivAt w φ τ u)).div_const
    (egbCoexistenceASymmetricRatio τ ^ (6 : ℕ))
  apply h.congr_deriv
  unfold egbFixedChargeAMeanDeficitIntegrand
  rw [egbFixedChargeAMeanDeficitForce_polynomial_formula]
  have hdpos := hd.1
  field_simp <;> ring

theorem egbFixedChargeAMeanGibbsDeficit_integral (w φ τ l : ℝ) :
    egbFixedChargeAMeanGibbsDeficit w φ τ l / egbCoexistenceASymmetricRatio τ ^ (6 : ℕ) =
      ∫ u in (0 : ℝ)..1, egbFixedChargeAMeanDeficitIntegrand w φ τ u := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMeanDeficitPathRadius w φ τ x) /
          egbCoexistenceASymmetricRatio τ ^ (6 : ℕ))
        (egbFixedChargeAMeanDeficitIntegrand w φ τ u) u := by
    intro u hu
    apply mean_deficit_path_normalized_hasDerivAt w φ τ l u
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (egbFixedChargeAMeanDeficitIntegrand_intervalIntegrable w φ τ)
  rw [egbFixedChargeAMeanDeficitPathRadius_end, egbFixedChargeAMeanDeficitPathRadius_start] at h
  rw [h]
  unfold egbFixedChargeAMeanGibbsDeficit
  ring

theorem egbFixedChargeAMeanGibbsDeficit_reference_independent (w φ τ l₁ l₂ : ℝ) :
    egbFixedChargeAMeanGibbsDeficit w φ τ l₁ = egbFixedChargeAMeanGibbsDeficit w φ τ l₂ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd6 : egbCoexistenceASymmetricRatio τ ^ (6 : ℕ) ≠ 0 := by positivity
  calc
    _ = (∫ u in (0 : ℝ)..1, egbFixedChargeAMeanDeficitIntegrand w φ τ u) * egbCoexistenceASymmetricRatio τ ^ (6 : ℕ) :=
      (div_eq_iff hd6).1 (egbFixedChargeAMeanGibbsDeficit_integral w φ τ l₁)
    _ = _ := ((div_eq_iff hd6).1 (egbFixedChargeAMeanGibbsDeficit_integral w φ τ l₂)).symm

theorem egbFixedChargeAMeanDeficitLimitIntegrand_antiderivative (w φ u : ℝ) :
    HasDerivAt (fun x : ℝ => egbFixedChargeAMeanDeficitCoefficient w φ * (2 * x - x ^ (2 : ℕ)))
      (egbFixedChargeAMeanDeficitLimitIntegrand w φ u) u := by
  have h := (((hasDerivAt_id u).const_mul 2).sub ((hasDerivAt_id u).pow 2)).const_mul
    (egbFixedChargeAMeanDeficitCoefficient w φ)
  apply h.congr_deriv
  unfold egbFixedChargeAMeanDeficitLimitIntegrand
  simp only [id_eq]
  ring

theorem egbFixedChargeAMeanDeficitLimitIntegrand_integral (w φ : ℝ) :
    (∫ u in (0 : ℝ)..1, egbFixedChargeAMeanDeficitLimitIntegrand w φ u) = egbFixedChargeAMeanDeficitCoefficient w φ := by
  have hint : IntervalIntegrable (egbFixedChargeAMeanDeficitLimitIntegrand w φ) volume 0 1 := by
    have hc : Continuous (egbFixedChargeAMeanDeficitLimitIntegrand w φ) := by
      unfold egbFixedChargeAMeanDeficitLimitIntegrand
      fun_prop
    exact hc.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => egbFixedChargeAMeanDeficitLimitIntegrand_antiderivative w φ u) hint
  norm_num at h
  exact h

end GaloisForLFunctions.HTGeometry
