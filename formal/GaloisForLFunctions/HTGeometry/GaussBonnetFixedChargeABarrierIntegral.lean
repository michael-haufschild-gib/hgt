import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierIntegrand

/-!
# Exact integral representation of the physical Gibbs barrier

The affine path stays between two positive constructed radii. Its actual
Gibbs derivative equals the normalized rational integrand. The fundamental
theorem of calculus therefore expresses the barrier divided by d⁴ as an
integral on the fixed unit interval.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeABarrierPath_displacement (w φ τ : ℝ) :
    egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeALargeRadius w φ τ =
      egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ * (egbFixedChargeAMiddleGapCoordinate τ φ - 1) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMiddleRadius_mean_formula, egbFixedChargeA_large_radius_mean]
  unfold egbFixedChargeAMiddleGapCoordinate
  field_simp <;> ring

private theorem barrier_path_normalized_hasDerivAt (w φ τ l : ℝ) :
    ∀ u ∈ Icc (0 : ℝ) 1,
    HasDerivAt (fun x => egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeABarrierPathRadius w φ τ x) / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ))
      (egbFixedChargeABarrierIntegrand w φ τ u) u := by
  intro u hu
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  have hscale := (egbFixedChargeABarrierPathScale_mapsTo τ φ hu).1
  have hv : 0 < 1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u := by linarith [hd.2]
  have hg := egbFixedChargeA_mean_gibbs_derivative w φ τ l
    (log (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u))
  rw [exp_log hv, ← egbFixedChargeABarrierPathRadius_mean_formula] at hg
  have hpath : HasDerivAt (egbFixedChargeABarrierPathRadius w φ τ)
      (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeALargeRadius w φ τ) u := by
    unfold egbFixedChargeABarrierPathRadius
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id u).const_mul (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeALargeRadius w φ τ)).const_add
        (egbFixedChargeALargeRadius w φ τ)
  have h := (hg.comp u hpath).div_const (egbCoexistenceASymmetricRatio τ ^ (4 : ℕ))
  apply h.congr_deriv
  rw [egbFixedChargeABarrierPath_displacement]
  have hdpos := hd.1
  calc
    _ = egbFixedChargeAMeanRadius w φ τ * (egbFixedChargeAMiddleGapCoordinate τ φ - 1) *
      (egbFixedChargeAMeanStationaryPolynomial τ φ
        (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u) / egbCoexistenceASymmetricRatio τ ^ (3 : ℕ)) /
      (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) *
        (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u) ^ (2 : ℕ)) := by
      field_simp <;> ring
    _ = _ := by
      rw [egbFixedChargeAMeanStationaryPolynomial_scaled]
      unfold egbFixedChargeABarrierIntegrand egbFixedChargeABarrierPolynomial
      ring

theorem egbFixedChargeAGibbsBarrier_integral (w φ τ l : ℝ) :
    egbFixedChargeAGibbsBarrier w φ τ l / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) =
      ∫ u in (0 : ℝ)..1, egbFixedChargeABarrierIntegrand w φ τ u := by
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeABarrierPathRadius w φ τ x) / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ))
        (egbFixedChargeABarrierIntegrand w φ τ u) u := by
    intro u hu
    apply barrier_path_normalized_hasDerivAt w φ τ l u
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (egbFixedChargeABarrierIntegrand_intervalIntegrable w φ τ)
  rw [egbFixedChargeABarrierPathRadius_end, egbFixedChargeABarrierPathRadius_start] at h
  rw [h]
  unfold egbFixedChargeAGibbsBarrier
  ring

theorem egbFixedChargeAGibbsBarrier_reference_independent (w φ τ l₁ l₂ : ℝ) :
    egbFixedChargeAGibbsBarrier w φ τ l₁ = egbFixedChargeAGibbsBarrier w φ τ l₂ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd4 : egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) ≠ 0 := by positivity
  calc
    _ = (∫ u in (0 : ℝ)..1, egbFixedChargeABarrierIntegrand w φ τ u) * egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) :=
      (div_eq_iff hd4).1 (egbFixedChargeAGibbsBarrier_integral w φ τ l₁)
    _ = _ := ((div_eq_iff hd4).1 (egbFixedChargeAGibbsBarrier_integral w φ τ l₂)).symm

theorem egbFixedChargeABarrierLimitIntegrand_integral (w φ : ℝ) :
    (∫ u in (0 : ℝ)..1, egbFixedChargeABarrierLimitIntegrand w φ u) = egbFixedChargeAGibbsBarrierCoefficient w φ := by
  have hderiv (u : ℝ) : HasDerivAt (fun x : ℝ => x ^ (2 : ℕ) - x ^ (3 : ℕ) + x ^ (4 : ℕ) / 4) (2 * u - 3 * u ^ (2 : ℕ) + u ^ (3 : ℕ)) u := by
    have h := (((hasDerivAt_id u).pow 2).sub ((hasDerivAt_id u).pow 3)).add (((hasDerivAt_id u).pow 4).div_const 4)
    apply h.congr_deriv
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable (fun u : ℝ => 2 * u - 3 * u ^ (2 : ℕ) + u ^ (3 : ℕ)) volume 0 1 := by
    have hc : Continuous (fun u : ℝ => 2 * u - 3 * u ^ (2 : ℕ) + u ^ (3 : ℕ)) := by fun_prop
    exact hc.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint
  norm_num at h
  unfold egbFixedChargeABarrierLimitIntegrand
  rw [intervalIntegral.integral_const_mul, h]
  ring

end GaloisForLFunctions.HTGeometry
