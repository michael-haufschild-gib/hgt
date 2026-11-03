import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.RHTower.SelbergClass.FunctionalEquationLocal
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Gamma decay between the quarter lines

Every positive Gamma scale contributes a vanishing ratio between the lines at
one quarter and three quarters. A nonempty Selberg Gamma product therefore has
a vanishing ratio. Both lines lie in the positive Gamma half-plane.
-/

noncomputable section
open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

private theorem tendsto_norm_Gamma_ratio_zero {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ /
      ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (t : ℂ) * I)‖) atTop (𝓝 0) := by
  have h := (gamma_vertical_ratio_norm_rpow_tendsto ha hδ.le).mul (tendsto_rpow_neg_atTop hδ)
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hA : 0 < ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero ht a)
  have hB : 0 < ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero ht (a + δ))
  rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one,
    Real.exp_sub, Real.exp_log hA, Real.exp_log hB]

private theorem gammaAffine_re_pos (D : SelbergGammaData) {s : ℂ} (hs : 0 < s.re)
    (j : Fin D.rank) : 0 < ((D.lambda j : ℂ) * s + D.mu j).re := by
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using add_pos_of_pos_of_nonneg (mul_pos (D.lambda_pos j) hs)
      (D.mu_re_nonneg j)

theorem gammaFactor_analyticAt_of_re_pos (D : SelbergGammaData) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ D.gammaFactor s := by
  rw [SelbergGammaData.gammaFactor]
  apply AnalyticAt.mul
  · exact (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr D.Q_pos.ne'))).analyticAt s
  · apply Finset.univ.analyticAt_prod
    intro j _
    exact AnalyticAt.comp (g := Complex.Gamma)
      (f := fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) (x := s)
      (HTGeometry.analyticAt_Gamma_of_re_pos (gammaAffine_re_pos D hs j)) (by fun_prop)

theorem gammaFactor_ne_zero_of_re_pos (D : SelbergGammaData) {s : ℂ} (hs : 0 < s.re) :
    D.gammaFactor s ≠ 0 := by
  simp only [SelbergGammaData.gammaFactor, Pi.mul_apply, Finset.prod_apply]
  apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr
    (.inl (Complex.ofReal_ne_zero.mpr D.Q_pos.ne')))
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply Complex.Gamma_ne_zero
  intro n hn
  have hp := gammaAffine_re_pos D hs j
  rw [hn, Complex.neg_re, Complex.natCast_re] at hp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem norm_gammaFactor_vertical (D : SelbergGammaData) (σ t : ℝ) :
    ‖D.gammaFactor ((σ : ℂ) + (t : ℂ) * I)‖ = D.Q ^ σ *
      ∏ j, ‖Complex.Gamma (((D.lambda j * σ + (D.mu j).re : ℝ) : ℂ) +
        ((D.lambda j * t + (D.mu j).im : ℝ) : ℂ) * I)‖ := by
  simp only [SelbergGammaData.gammaFactor, Pi.mul_apply, Finset.prod_apply, norm_mul, norm_prod]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos D.Q_pos]
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  rw [hre]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- A positive-degree Gamma product has vanishing quarter-line ratio. -/
theorem tendsto_gammaFactor_quarter_ratio (D : SelbergGammaData) (hd : 0 < D.degree) :
    Tendsto (fun t : ℝ => ‖D.gammaFactor ((1 / 4 : ℂ) + (t : ℂ) * I)‖ /
      ‖D.gammaFactor ((3 / 4 : ℂ) + (t : ℂ) * I)‖) atTop (𝓝 0) := by
  classical
  have hr : 0 < D.rank := by
    by_contra h
    have hr0 : D.rank = 0 := by omega
    have hempty : (Finset.univ : Finset (Fin D.rank)) = ∅ := by
      rw [Finset.univ_eq_empty_iff, hr0]
      infer_instance
    have hzero : D.degree = 0 := by rw [SelbergGammaData.degree, hempty, Finset.sum_empty, mul_zero]
    linarith
  have hfac : ∀ j : Fin D.rank, Tendsto (fun t : ℝ =>
      ‖Complex.Gamma (((D.lambda j * (1 / 4) + (D.mu j).re : ℝ) : ℂ) +
        ((D.lambda j * t + (D.mu j).im : ℝ) : ℂ) * I)‖ /
      ‖Complex.Gamma (((D.lambda j * (3 / 4) + (D.mu j).re : ℝ) : ℂ) +
        ((D.lambda j * t + (D.mu j).im : ℝ) : ℂ) * I)‖) atTop (𝓝 0) := by
    intro j
    have ha : 0 ≤ D.lambda j * (1 / 4) + (D.mu j).re :=
      add_nonneg (mul_nonneg (D.lambda_pos j).le (by norm_num)) (D.mu_re_nonneg j)
    have hδ : 0 < D.lambda j / 2 := div_pos (D.lambda_pos j) (by norm_num)
    have hτ : Tendsto (fun t : ℝ => D.lambda j * t + (D.mu j).im) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (D.lambda_pos j))
    have hlim := (tendsto_norm_Gamma_ratio_zero ha hδ).comp hτ
    have he : D.lambda j * (1 / 4) + (D.mu j).re + D.lambda j / 2 =
        D.lambda j * (3 / 4) + (D.mu j).re := by ring
    simpa only [Function.comp_def, he] using hlim
  have hprod := tendsto_finsetProd Finset.univ (fun j _ => hfac j)
  have hz : (∏ _j : Fin D.rank, (0 : ℝ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hr⟩ : Fin D.rank))
    rfl
  rw [hz] at hprod
  have hlim := hprod.const_mul (D.Q ^ (1 / 4 : ℝ) / D.Q ^ (3 / 4 : ℝ))
  rw [mul_zero] at hlim
  refine hlim.congr fun t => ?_
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl,
    show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by push_cast; rfl,
    norm_gammaFactor_vertical, norm_gammaFactor_vertical, Finset.prod_div_distrib]
  exact div_mul_div_comm _ _ _ _

end GaloisForLFunctions.SelbergClass
