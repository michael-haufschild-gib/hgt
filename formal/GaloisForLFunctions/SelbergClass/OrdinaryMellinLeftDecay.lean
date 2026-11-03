import GaloisForLFunctions.SelbergClass.OrdinaryMellinLeftBound
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Vanishing of the ordinary far-left Mellin integrals

Below degree one, the Gamma root limit beats every fixed positive Mellin base.
The surviving exponential in height supplies an integrable majorant.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

theorem analyticAt_ordinaryMellinIntegrand (F : ExtendedSelbergClass) (s : ℂ)
    {z : ℂ} (hz : z ≠ 0) {u : ℂ} (hΓ : ∀ k : ℕ, u ≠ -(k : ℂ))
    (hu : s + u ≠ 1) : AnalyticAt ℂ (ordinaryMellinIntegrand F s z) u :=
  (analyticAt_cpow_neg hz u).mul ((HTGeometry.analyticAt_Gamma_off_poles hΓ).mul
    ((F.continuation.analyticAt_value_of_ne_one hu).comp (by fun_prop)))

theorem meromorphicAt_ordinaryMellinIntegrand (F : ExtendedSelbergClass) (s : ℂ)
    {z : ℂ} (hz : z ≠ 0) (u : ℂ) : MeromorphicAt (ordinaryMellinIntegrand F s z) u :=
  (analyticAt_cpow_neg hz u).meromorphicAt.mul ((Meromorphic.Gamma u).mul
    ((F.meromorphic_value _).comp_analyticAt (by fun_prop)))

/-- The ordinary far-left majorant tends to zero for every positive base. -/
theorem tendsto_ordinaryLeftMajorant (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree < 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (ordinaryLeftMajorant F s x) atTop (𝓝 0) := by
  have hxroot : Tendsto (fun k : ℕ => (x ^ k) ^ (1 / (k : ℝ))) atTop (𝓝 x) := by
    simpa only [zero_add, one_mul, Real.rpow_natCast, Real.rpow_one] using
      (tendsto_rpow_linear_rpow_inv (a := 0) (b := 1) hx)
  have hQroot := tendsto_rpow_linear_rpow_inv
    (a := 1 - 2 * (s - 1 / 2).re) (b := 2) F.gammaData.Q_pos
  have hP := ordinaryGammaProduct_div_Gamma_root_tendsto_zero F.gammaData hd s
  have hroot := (hxroot.mul hQroot).mul hP
  simp only [mul_zero] at hroot
  apply tendsto_zero_of_tendsto_rpow_inv_lt_one
    (Filter.Eventually.of_forall (ordinaryLeftMajorant_nonneg F s hx.le)) (by norm_num : (0 : ℝ) < 1)
  refine hroot.congr fun k => ?_
  have hΓ : 0 < Real.Gamma ((k : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [ordinaryLeftMajorant,
    Real.mul_rpow (mul_nonneg (pow_nonneg hx.le _) (Real.rpow_nonneg F.gammaData.Q_pos.le _))
      (div_nonneg (ordinaryGammaProduct_nonneg _ _ _) hΓ.le),
    Real.mul_rpow (pow_nonneg hx.le _) (Real.rpow_nonneg F.gammaData.Q_pos.le _)]

/-- The far-left ordinary Mellin integrals are absolutely convergent and their
norms are bounded by a constant times the vanishing majorant. -/
theorem eventually_integrable_ordinaryMellinIntegrand_left
    (F : ExtendedSelbergClass) (hd0 : 0 < F.gammaData.degree)
    (hd1 : F.gammaData.degree < 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      Integrable (fun t : ℝ => ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)) ∧
      ‖∫ t : ℝ, ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)‖ ≤
        B * ordinaryLeftMajorant F s x k := by
  obtain ⟨C, hC, hev⟩ := eventually_norm_ordinaryMellinIntegrand_left_le F hd0 s hx
  set c : ℝ := Real.pi * (1 - F.gammaData.degree) / 2 with hc
  have hcpos : 0 < c := div_pos (mul_pos Real.pi_pos (sub_pos.mpr hd1)) (by norm_num)
  have hprof : Integrable (fun t : ℝ => Real.exp (-(c * |t|))) :=
    integrable_exp_neg_mul_abs' hcpos
  refine ⟨C * ∫ t : ℝ, Real.exp (-(c * |t|)),
    mul_nonneg hC (integral_nonneg fun t => (Real.exp_pos _).le), ?_⟩
  filter_upwards [hev, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop s.re] with k hk hks
  have hcont : Continuous (fun t : ℝ => ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hΓ : ∀ n : ℕ, leftLine k t ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp [leftLine] at hre
      have h2 : (2 : ℝ) * ((n : ℝ) - k) = 1 := by linarith
      have h3 : (2 : ℤ) * ((n : ℤ) - k) = 1 := by exact_mod_cast h2
      omega
    have hne : s + leftLine k t ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp [leftLine] at hre
      linarith
    exact (analyticAt_ordinaryMellinIntegrand F s (Complex.ofReal_ne_zero.mpr hx.ne')
      hΓ hne).continuousAt.comp (by unfold leftLine; fun_prop)
  have hbound : ∀ t : ℝ, ‖ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)‖ ≤
      (C * ordinaryLeftMajorant F s x k) * Real.exp (-(c * |t|)) := by
    intro t
    convert hk t using 1
    congr 2
    rw [hc]
    ring
  have hint := Integrable.mono' (hprof.const_mul (C * ordinaryLeftMajorant F s x k))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine ⟨hint, ?_⟩
  calc ‖∫ t : ℝ, ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)‖
      ≤ ∫ t : ℝ, ‖ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (C * ordinaryLeftMajorant F s x k) * Real.exp (-(c * |t|)) :=
        integral_mono hint.norm (hprof.const_mul _) hbound
    _ = _ := by rw [integral_const_mul]; ring

/-- No restriction on the positive base remains below degree one. -/
theorem tendsto_integral_ordinaryMellinIntegrand_left
    (F : ExtendedSelbergClass) (hd0 : 0 < F.gammaData.degree)
    (hd1 : F.gammaData.degree < 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k : ℕ => ∫ t : ℝ,
      ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)) atTop (𝓝 0) := by
  obtain ⟨B, _, hev⟩ := eventually_integrable_ordinaryMellinIntegrand_left F hd0 hd1 s hx
  have hlim := (tendsto_ordinaryLeftMajorant F hd1 s hx).const_mul B
  rw [mul_zero] at hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg _)
    (hev.mono fun k hk => hk.2) hlim

end GaloisForLFunctions.SelbergClass
