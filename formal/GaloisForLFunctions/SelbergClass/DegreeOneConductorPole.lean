import GaloisForLFunctions.SelbergClass.DiskContinuationCoefficientDecay
import GaloisForLFunctions.RHTower.SelbergCuspExpansion
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!+# The degree-one conductor and the pole at one

The cusp disk has radius `m₀/q` at degree one. If the continuation has no pole
at one and `q < 2m₀`, this disk crosses a full exponential period. Fourier
transport then forces absolute Dirichlet convergence at zero, contradicting
positive degree. Meromorphic order makes the conclusion independent of the
chosen pole-clearing exponent and the totalized value at one.
-/

noncomputable section
open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

private theorem cuspPolarPart_zero_of_order_nonneg (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) (horder : 0 ≤ meromorphicOrderAt F 1)
    {ζ : ℂ} (hζ : 0 < ζ.im) : F.cuspPolarPart 0 ζ = 0 := by
  obtain ⟨g, hg, hfg⟩ := (F.meromorphic_value 1).meromorphicOrderAt_nonneg_iff.mp horder
  let x : ℂ := -2 * Real.pi * I * ζ
  have hx : x ≠ 0 := neg_two_pi_I_mul_ne_zero hζ
  have han : AnalyticAt ℂ (fun u : ℂ => x ^ (-u) * (Complex.Gamma u * g u)) 1 :=
    (analyticAt_cpow_neg hx 1).mul
      ((_root_.HTGeometry.analyticAt_Gamma_of_re_pos (by norm_num)).mul hg)
  have heq : F.cuspMellinIntegrand 0 x =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun u : ℂ => x ^ (-u) * (Complex.Gamma u * g u)) := by
    filter_upwards [hfg] with u hu
    simp only [ExtendedSelbergClass.cuspMellinIntegrand, hd, Complex.ofReal_one,
      div_one, zero_add, hu]
  have hp : F.cuspPole 0 = 1 := by simp [ExtendedSelbergClass.cuspPole, hd]
  rw [ExtendedSelbergClass.cuspPolarPart, hp,
    laurentCoeff_congr (F.meromorphicAt_cuspMellinIntegrand 0 hx 1) heq (-1)]
  exact laurentCoeff_eq_zero_of_analyticAt han (by norm_num)

private def cuspCoordinate (z : ℂ) : ℂ := I * z / ((2 * Real.pi : ℝ) : ℂ)

private theorem cuspCoordinate_norm (z : ℂ) :
    ‖cuspCoordinate z‖ = ‖z‖ / (2 * Real.pi) := by
  rw [cuspCoordinate, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]

private theorem cuspCoordinate_im (z : ℂ) :
    (cuspCoordinate z).im = z.re / (2 * Real.pi) := by
  rw [cuspCoordinate, Complex.div_ofReal_im]
  simp

private theorem theta_cuspCoordinate (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) (z : ℂ) :
    F.theta 0 (cuspCoordinate z) = ordinaryExponentialSeries F z := by
  unfold ExtendedSelbergClass.theta thetaSeries ordinaryExponentialSeries
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaTerm, ordinaryExponentialTerm]
  · rw [thetaTerm, if_neg hn.ne']
    simp only [ExtendedSelbergClass.presentationDegree, hd, neg_zero, Complex.cpow_zero,
      mul_one, one_div_one, Real.rpow_one]
    rw [ordinaryExponentialTerm]
    congr 1
    congr 1
    unfold cuspCoordinate
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Absence of a pole gives a holomorphic ordinary generating function on the
disk of radius `2πm₀/q`. -/
theorem exists_degreeOne_disk_extension_of_order_nonneg (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) (horder : 0 ≤ meromorphicOrderAt F 1) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball 0 (2 * Real.pi * Metric.infDist 0 F.shiftSpectrum)) ∧
      ∀ z, ‖z‖ < 2 * Real.pi * Metric.infDist 0 F.shiftSpectrum → 0 < z.re →
        g z = ordinaryExponentialSeries F z := by
  have hdpos : 0 < F.gammaData.degree := by rw [hd]; norm_num
  let Δ := Metric.infDist 0 F.shiftSpectrum
  let p := FormalMultilinearSeries.ofScalars ℂ (F.cuspExpansionCoeff 0)
  have hΔ : 0 < Δ := F.infDist_zero_shiftSpectrum_pos hdpos
  have hrad : p.radius = ENNReal.ofReal Δ := F.radius_cuspExpansion hdpos 0
  have hps := p.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.ofReal_pos.mpr hΔ)
  have hmem : ∀ z : ℂ, ‖z‖ < 2 * Real.pi * Δ →
      cuspCoordinate z ∈ Metric.eball 0 p.radius := by
    intro z hz
    rw [hrad, Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    apply (ENNReal.ofReal_lt_ofReal_iff hΔ).mpr
    rw [cuspCoordinate_norm, div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    simpa only [mul_comm Δ] using hz
  refine ⟨fun z => p.sum (cuspCoordinate z), ?_, ?_⟩
  · intro z hz
    have hz' : ‖z‖ < 2 * Real.pi * Δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact (hps.analyticAt_of_mem (hmem z hz')).comp (by unfold cuspCoordinate; fun_prop)
  · intro z hz hzr
    have hzi : 0 < (cuspCoordinate z).im := by
      rw [cuspCoordinate_im]
      exact div_pos hzr (by positivity)
    have hzΔ : ‖cuspCoordinate z‖ < Δ := by
      rw [cuspCoordinate_norm, div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
      simpa only [mul_comm Δ] using hz
    have hs : ∀ k : ℕ, F.cuspPole 0 ≠ -(k : ℂ) := by
      intro k hk
      have hre := congrArg Complex.re hk
      simp [ExtendedSelbergClass.cuspPole, hd] at hre
      have := Nat.cast_nonneg (R := ℝ) k
      linarith
    have h1 := F.hasSum_cuspExpansion hdpos 0 hs hzi hzΔ
    have h2 := hps.hasSum (hmem z hz)
    simp only [zero_add, p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h2
    rw [cuspPolarPart_zero_of_order_nonneg F hd horder hzi, sub_zero,
      theta_cuspCoordinate F hd z] at h1
    exact h2.unique h1

/-- A degree-one Selberg function either has conductor at least twice its
first nonzero coefficient index, or has a genuine pole at one. -/
theorem degreeOne_conductor_bound_or_pole (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) :
    2 * (F.firstIndex : ℝ) ≤ F.gammaData.conductor ∨ meromorphicOrderAt F 1 < 0 := by
  by_cases hq : 2 * (F.firstIndex : ℝ) ≤ F.gammaData.conductor
  · exact Or.inl hq
  right
  by_contra horder
  have hord : 0 ≤ meromorphicOrderAt F 1 := le_of_not_gt horder
  obtain ⟨g, hg, heq⟩ := exists_degreeOne_disk_extension_of_order_nonneg F hd hord
  have hΔ : Metric.infDist 0 F.shiftSpectrum = (F.firstIndex : ℝ) / F.gammaData.conductor := by
    rw [F.infDist_zero_shiftSpectrum_eq (by rw [hd]; norm_num), hd]
    simp only [one_div_one, Real.rpow_one, one_mul]
  have hhalf : 1 / 2 < Metric.infDist 0 F.shiftSpectrum := by
    rw [hΔ, lt_div_iff₀ F.gammaData.conductor_pos]
    linarith [lt_of_not_ge hq]
  have hR : Real.pi < 2 * Real.pi * Metric.infDist 0 F.shiftSpectrum := by
    nlinarith only [hhalf, Real.pi_pos]
  have hzero := degree_eq_zero_of_disk_extension F hR hg heq
  rw [hd] at hzero
  exact one_ne_zero hzero

/-- In the normalized full class the first coefficient is one, so conductor
below two forces a genuine pole at one. -/
theorem full_degreeOne_conductor_bound_or_pole (F : RHTower.SelbergClass)
    (hd : F.gammaData.degree = 1) :
    2 ≤ F.gammaData.conductor ∨ meromorphicOrderAt F.toExtendedSelbergClass 1 < 0 := by
  have h := degreeOne_conductor_bound_or_pole F.toExtendedSelbergClass hd
  simpa only [F.firstIndex_eq_one, Nat.cast_one, mul_one] using h

end GaloisForLFunctions.SelbergClass
