import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsIntegrand

/-!
# Exact integral representation of every interior Gibbs gap

All paths stay within the positive phase-radius interval. Applying the
fundamental theorem of calculus to the actual Gibbs function identifies
the normalized gap with the constructed rational integral.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

private theorem interior_path_normalized_hasDerivAt (w φ τ l ψ : ℝ) :
    ∀ u ∈ Icc (0 : ℝ) 1,
    HasDerivAt (fun x => egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorPathRadius w φ τ ψ x) /
        egbCoexistenceASymmetricRatio τ ^ 4)
      (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u) u := by
  intro u hu
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  have hscale := (egbFixedChargeAInteriorPathScale_mapsTo τ ψ hu).1
  have hv : 0 < 1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeAInteriorPathCoordinate ψ u := by linarith [hd.2]
  have hg := egbFixedChargeA_mean_gibbs_derivative w φ τ l
    (log (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeAInteriorPathCoordinate ψ u))
  rw [exp_log hv, ← egbFixedChargeAInteriorPathRadius_mean_formula] at hg
  have h := (hg.comp u (egbFixedChargeAInteriorPathRadius_hasDerivAt w φ τ ψ u)).div_const
    (egbCoexistenceASymmetricRatio τ ^ 4)
  apply h.congr_deriv
  unfold egbFixedChargeAInteriorGibbsIntegrand
  rw [egbFixedChargeAGibbsKernel_polynomial_formula]
  have hdpos := hd.1
  field_simp <;> ring

theorem egbFixedChargeAInteriorGibbsGap_integral (w φ τ l ψ : ℝ) :
    egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbCoexistenceASymmetricRatio τ ^ 4 =
      ∫ u in (0 : ℝ)..1, egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorPathRadius w φ τ ψ x) /
          egbCoexistenceASymmetricRatio τ ^ 4)
        (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u) u := by
    intro u hu
    apply interior_path_normalized_hasDerivAt w φ τ l ψ u
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (egbFixedChargeAInteriorGibbsIntegrand_intervalIntegrable w φ τ ψ)
  rw [egbFixedChargeAInteriorPathRadius_end, egbFixedChargeAInteriorPathRadius_start] at h
  rw [h]
  unfold egbFixedChargeAInteriorGibbsGap
  ring

theorem egbFixedChargeAInteriorGibbsGap_reference_independent (w φ τ l₁ l₂ ψ : ℝ) :
    egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ = egbFixedChargeAInteriorGibbsGap w φ τ l₂ ψ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd4 : egbCoexistenceASymmetricRatio τ ^ 4 ≠ 0 := by positivity
  calc
    _ = (∫ u in (0 : ℝ)..1, egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u) * egbCoexistenceASymmetricRatio τ ^ 4 :=
      (div_eq_iff hd4).1 (egbFixedChargeAInteriorGibbsGap_integral w φ τ l₁ ψ)
    _ = _ := ((div_eq_iff hd4).1 (egbFixedChargeAInteriorGibbsGap_integral w φ τ l₂ ψ)).symm

theorem egbFixedChargeAInteriorGibbsLimitIntegrand_antiderivative (w φ ψ u : ℝ) :
    HasDerivAt (fun x => egbFixedChargeAGibbsBarrierCoefficient w φ *
      (egbFixedChargeAInteriorPathCoordinate ψ x ^ 2 - 1) ^ 2)
      (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ u) u := by
  have h := ((((egbFixedChargeAInteriorPathCoordinate_hasDerivAt ψ u).pow 2).sub_const 1).pow 2).const_mul
    (egbFixedChargeAGibbsBarrierCoefficient w φ)
  apply h.congr_deriv
  unfold egbFixedChargeAInteriorGibbsLimitIntegrand
  simp only [Pi.pow_apply]
  ring

theorem egbFixedChargeAInteriorGibbsLimitIntegrand_integral (w φ ψ : ℝ) :
    (∫ u in (0 : ℝ)..1, egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ u) =
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ 4 := by
  have hint : IntervalIntegrable (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ) volume 0 1 := by
    have hc : Continuous (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ) := by
      unfold egbFixedChargeAInteriorGibbsLimitIntegrand egbFixedChargeAInteriorPathCoordinate
      fun_prop
    exact hc.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => egbFixedChargeAInteriorGibbsLimitIntegrand_antiderivative w φ ψ u) hint
  have hs : sin ψ ^ 2 - 1 = -(cos ψ ^ 2) := by linarith [sin_sq_add_cos_sq ψ]
  calc
    _ = egbFixedChargeAGibbsBarrierCoefficient w φ * (sin ψ ^ 2 - 1) ^ 2 := by
      simpa only [egbFixedChargeAInteriorPathCoordinate_end, egbFixedChargeAInteriorPathCoordinate_start,
        one_pow, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero] using h
    _ = _ := by rw [hs]; ring

end GaloisForLFunctions.HTGeometry
