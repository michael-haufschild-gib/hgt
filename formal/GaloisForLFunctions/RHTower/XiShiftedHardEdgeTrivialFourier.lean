import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeCone

/-!
# Integrability and the trivial Fourier bound of the rational hard-edge test

The Cayley chart turns the square of the rational hard-edge test into a bounded continuous function
on a bounded interval, so the test is square integrable on the whole line.  Its Fourier transform is
therefore defined and obeys the trivial bound

`|ĝ²(L)| ≤ ‖g‖₂²`,

which is what the prime sum uses below the aperture threshold, where the exponential cone gives
nothing.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- **The rational hard-edge test is square integrable.**  Its square transports to a bounded
continuous function on a bounded angular interval. -/
theorem integrable_routeUHardEdgeRationalTest_sq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => routeUHardEdgeRationalTest a p x ^ 2) := by
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Ioo (-Real.pi) Real.pi)
    (f := routeUHardEdgeAngularChart a) (f' := routeUHardEdgeAngularJacobian a)
    measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_routeUHardEdgeAngularChart
      (ne_of_gt (cos_half_pos_of_mem_Ioo hθ))).hasDerivWithinAt)
    (injOn_routeUHardEdgeAngularChart ha)
    (fun x : ℝ => routeUHardEdgeRationalTest a p x ^ 2)
  rw [image_routeUHardEdgeAngularChart ha] at hiff
  rw [← MeasureTheory.integrableOn_univ]
  refine hiff.2 ?_
  have hcongr : ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
      |routeUHardEdgeAngularJacobian a θ|
          • routeUHardEdgeRationalTest a p (routeUHardEdgeAngularChart a θ) ^ 2
        = a / 2 * ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ 2 := by
    intro θ hθ
    have hcos := cos_half_pos_of_mem_Ioo hθ
    have hcosne : Real.cos (θ / 2) ≠ 0 := ne_of_gt hcos
    have hjac : |routeUHardEdgeAngularJacobian a θ|
        = a * (1 / Real.cos (θ / 2) ^ 2 * (1 / 2)) := by
      rw [routeUHardEdgeAngularJacobian, abs_of_pos (by positivity)]
    have hval : routeUHardEdgeRationalTest a p (routeUHardEdgeAngularChart a θ)
        = Real.cos (θ / 2) * (routeUHardEdgeAngularPoly a p).eval (Real.cos θ) :=
      routeUHardEdgeRationalTest_tan ha p hcos
    rw [smul_eq_mul, hjac, hval, mul_pow]
    field_simp
  refine MeasureTheory.IntegrableOn.congr_fun ?_ (fun θ hθ => (hcongr θ hθ).symm) measurableSet_Ioo
  refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioo_subset_Icc_self
  exact (continuous_const.mul
    (((Polynomial.continuous _).comp Real.continuous_cos).pow 2)).integrableOn_Icc

/-- The oscillatory integrand of the hard-edge Fourier transform is integrable. -/
theorem integrable_routeUHardEdgeFourierSq_integrand {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    (L : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => ((routeUHardEdgeRationalTest a p x ^ 2 : ℝ) : ℂ)
      * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)) := by
  have hbase := integrable_routeUHardEdgeRationalTest_sq ha p
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => ((routeUHardEdgeRationalTest a p x ^ 2 : ℝ) : ℂ)
        * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)) volume := by
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hbase.aestronglyMeasurable)).mul ?_
    refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id).neg).mul
        continuous_const)
  refine ⟨hmeas, ?_⟩
  have hbound : ∀ x : ℝ, ‖((routeUHardEdgeRationalTest a p x ^ 2 : ℝ) : ℂ)
      * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)‖
      = ‖routeUHardEdgeRationalTest a p x ^ 2‖ := by
    intro x
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : ((((-(L * x) : ℝ) : ℂ) * Complex.I)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
  have := hbase.hasFiniteIntegral
  refine MeasureTheory.HasFiniteIntegral.congr' this ?_
  filter_upwards with x
  rw [hbound x]

/-- **(CSHC.12) The trivial Fourier bound.**  Below the aperture threshold the transform of the
squared test is at most its `L²` mass. -/
theorem norm_routeUHardEdgeFourierSq_le_l2 (a : ℝ) (p : Polynomial ℝ) (L : ℝ) :
    ‖routeUHardEdgeFourierSq a p L‖
      ≤ ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := by
  have hnorm : ∀ x : ℝ, ‖((routeUHardEdgeRationalTest a p x ^ 2 : ℝ) : ℂ)
      * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)‖
      = routeUHardEdgeRationalTest a p x ^ 2 := by
    intro x
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : ((((-(L * x) : ℝ) : ℂ) * Complex.I)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [routeUHardEdgeFourierSq]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) (le_of_eq ?_)
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnorm)

end RHTower

end
