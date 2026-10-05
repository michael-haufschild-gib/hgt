import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareRightLine
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareContour

/-!
# Exact BAG divisor-square sum to the normalized moving contour

Every actual divisor-square coefficient is retained in Mellin inversion.
A complete summable majorant justifies the integral-series exchange.
The full original line is continuous and absolutely integrable. For X≥1,
the physical window kills n=1 exactly; removing that term and dividing by
ε² yields the literal normalized contour integrand with no interchange
or integrability premise. The uniform joint-limit estimates remain open.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private def squareMellinLine (X σ t : ℝ) : ℂ :=
  dampedSquareWindowMellin ((σ : ℂ)+t*I)*(X : ℂ)^((σ : ℂ)+t*I)

private theorem squareMellinLine_norm {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖squareMellinLine X σ t‖ = X^σ*‖dampedSquareWindowMellin ((σ : ℂ)+t*I)‖ := by
  rw [squareMellinLine,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp [mul_comm]

private theorem squareMellinLine_continuous {X : ℝ} (hX : 0 < X) (σ : ℝ) :
    Continuous (squareMellinLine X σ) := by
  have hM : Continuous (fun t : ℝ => dampedSquareWindowMellin ((σ : ℂ)+t*I)) :=
    differentiable_dampedSquareWindowMellin.continuous.comp (by fun_prop)
  exact hM.mul (Continuous.const_cpow (by fun_prop)
    (.inl (Complex.ofReal_ne_zero.mpr hX.ne')))

private theorem squareMellinLine_integrable {X : ℝ} (hX : 0 < X) (σ : ℝ) :
    Integrable (squareMellinLine X σ) := by
  apply ((integrable_dampedSquareWindowMellin_vertical σ).norm.const_mul (X^σ)).mono'
    (squareMellinLine_continuous hX σ).aestronglyMeasurable
  exact ae_of_all _ (fun t => (squareMellinLine_norm hX σ t).le)

private theorem square_perron_term {X : ℝ} (hX : 0 < X) (σ : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (∫ t : ℝ,(n : ℂ)^(-((σ : ℂ)+t*I))*squareMellinLine X σ t) =
      (2*Real.pi : ℂ)*(bagPhysicalHeightWindow (n/X) : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv := mellinInv_dampedSquareWindowMellin σ (div_pos hnR hX)
  have hscale : ∀ s : ℂ, (n : ℂ)^(-s)*(X : ℂ)^s = ((n/X : ℝ) : ℂ)^(-s) := by
    intro s
    have hm := Complex.mul_cpow_ofReal_nonneg (div_nonneg hnR.le hX.le) hX.le (-s)
    rw [← Complex.ofReal_mul,div_mul_cancel₀ _ hX.ne',Complex.ofReal_natCast] at hm
    have hc : (X : ℂ)^(-s)*(X : ℂ)^s = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
      simp
    rw [hm,mul_assoc,hc,mul_one]
  have he : (∫ t : ℝ,(n : ℂ)^(-((σ : ℂ)+t*I))*squareMellinLine X σ t) =
      ∫ t : ℝ,((n/X : ℝ) : ℂ)^(-((σ : ℂ)+t*I))*
        dampedSquareWindowMellin ((σ : ℂ)+t*I) := by
    apply integral_congr_ae (ae_of_all _ (fun t => ?_))
    rw [squareMellinLine]
    calc _ = ((n : ℂ)^(-((σ : ℂ)+t*I))*(X : ℂ)^((σ : ℂ)+t*I))*
        dampedSquareWindowMellin ((σ : ℂ)+t*I) := by ring
      _ = _ := by rw [hscale]
  rw [he,← hinv,mellinInv,Complex.real_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  have hp : (2*Real.pi : ℂ)*((1/(2*Real.pi) : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [hp,one_mul]

private theorem square_perron_of_bounded {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    (ha0 : a 0 = 0) {X σ : ℝ} (hX : 0 < X) (hσ : 1 < σ) :
    (2*Real.pi : ℂ)*(∑' n : ℕ,a n*(bagPhysicalHeightWindow (n/X) : ℂ)) =
      ∫ t : ℝ,(∑' n : ℕ,a n*(n : ℂ)^(-((σ : ℂ)+t*I)))*squareMellinLine X σ t := by
  let W := squareMellinLine X σ
  let F : ℕ → ℝ → ℂ := fun n t => a n*(n : ℂ)^(-((σ : ℂ)+t*I))*W t
  have hW : Integrable W := squareMellinLine_integrable hX σ
  have hnorm : ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      ‖F n t‖ = ‖a n‖*(n : ℝ)^(-σ)*‖W t‖ := by
    intro n hn t
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hint : ∀ n, Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F,ha0]
    have hc : Continuous (F n) :=
      (continuous_const.mul (Continuous.const_cpow (by fun_prop)
        (.inl (Nat.cast_ne_zero.mpr hn.ne')))).mul (squareMellinLine_continuous hX σ)
    apply (hW.norm.const_mul (‖a n‖*(n : ℝ)^(-σ))).mono' hc.aestronglyMeasurable
    exact ae_of_all _ (fun t => (hnorm n hn t).le)
  let V : ℝ := ∫ t : ℝ,‖W t‖
  have hV : 0 ≤ V := integral_nonneg (fun _ => norm_nonneg _)
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ,‖F n t‖) := by
    have hs : Summable (fun n : ℕ => (n : ℝ)^(-σ)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun t => norm_nonneg (F n t))) ?_ (hs.mul_right V)
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F,ha0,Real.zero_rpow (by linarith : -σ ≠ 0)]
    rw [integral_congr_ae (ae_of_all _ (hnorm n hn)),integral_const_mul]
    simpa only [mul_assoc] using mul_le_of_le_one_left
      (by positivity : 0 ≤ (n : ℝ)^(-σ)*V) (ha n)
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  have hterm : ∀ n : ℕ, (∫ t : ℝ,F n t) =
      (2*Real.pi : ℂ)*(a n*(bagPhysicalHeightWindow (n/X) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F,ha0]
    have he : F n = fun t : ℝ => a n*((n : ℂ)^(-((σ : ℂ)+t*I))*squareMellinLine X σ t) := by
      funext t
      dsimp [F,W]
      ring
    rw [he,integral_const_mul,square_perron_term hX σ hn]
    ring
  calc _ = ∑' n : ℕ,(2*Real.pi : ℂ)*(a n*(bagPhysicalHeightWindow (n/X) : ℂ)) :=
      tsum_mul_left.symm
    _ = ∑' n : ℕ,∫ t : ℝ,F n t := tsum_congr (fun n => (hterm n).symm)
    _ = ∫ t : ℝ,∑' n : ℕ,F n t := hHS.tsum_eq
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ (fun t => ?_))
      exact tsum_mul_right

/-- Exact summed Mellin inversion for every actual divisor-square coefficient. -/
theorem dampedSquare_weighted_sum_eq_integral {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hX : 0 < X) (hσ : 1 < σ) :
    (2*Real.pi : ℂ)*(∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*
        (bagPhysicalHeightWindow (n/X) : ℂ)) =
      ∫ t : ℝ,dampedSquareDirichlet ε ((σ : ℂ)+t*I)*
        dampedSquareWindowMellin ((σ : ℂ)+t*I)*(X : ℂ)^((σ : ℂ)+t*I) := by
  have ha : ∀ n : ℕ, ‖(pmPowerDampedDivisorCoeff ε n : ℂ)^2‖ ≤ 1 := by
    intro n
    rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε n)]
    exact pow_le_one₀ (pmPowerDampedDivisorCoeff_nonneg hε n)
      (pmPowerDampedDivisorCoeff_le_one hε n)
  have h := square_perron_of_bounded ha (by simp [pmPowerDampedDivisorCoeff_zero]) hX hσ
  simpa only [dampedSquareDirichlet,squareMellinLine,mul_assoc] using h

private theorem square_dirichlet_term_norm_le {ε σ : ℝ} (hε : 0 ≤ ε)
    (n : ℕ) (t : ℝ) :
    ‖(pmPowerDampedDivisorCoeff ε n : ℂ)^2*(n : ℂ)^(-((σ : ℂ)+t*I))‖ ≤
      (n : ℝ)^(-σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pmPowerDampedDivisorCoeff_zero,Complex.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0),
      zero_mul,norm_zero,Nat.cast_zero]
    exact Real.rpow_nonneg (by norm_num) _
  have hc : pmPowerDampedDivisorCoeff ε n^2 ≤ 1 :=
    pow_le_one₀ (pmPowerDampedDivisorCoeff_nonneg hε n) (pmPowerDampedDivisorCoeff_le_one hε n)
  rw [norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε n),
    Complex.norm_natCast_cpow_of_pos hn]
  simp only [Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hc

/-- The actual full original Dirichlet line is continuous by its full uniform majorant. -/
theorem continuous_dampedSquareDirichlet_vertical {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 1 < σ) :
    Continuous (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)) := by
  unfold dampedSquareDirichlet
  apply continuous_tsum (u := fun n : ℕ => (n : ℝ)^(-σ)) ?_
    (Real.summable_nat_rpow.mpr (by linarith)) (square_dirichlet_term_norm_le hε)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa only [pmPowerDampedDivisorCoeff_zero,Complex.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0),
      zero_mul] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop)
    (.inl (Nat.cast_ne_zero.mpr hn.ne')))

/-- Absolute integrability of the actual full source line used in Mellin inversion. -/
theorem integrable_dampedSquareDirichlet_window {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hX : 0 < X) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*
      dampedSquareWindowMellin ((σ : ℂ)+t*I)*(X : ℂ)^((σ : ℂ)+t*I)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbound : ∀ t : ℝ, ‖dampedSquareDirichlet ε ((σ : ℂ)+t*I)‖ ≤ ∑' n : ℕ,(n : ℝ)^(-σ) := by
    intro t
    have hh : 1 < ((σ : ℂ)+t*I).re := by simpa using hσ
    exact (norm_tsum_le_tsum_norm (summable_dampedSquareDirichlet hε hh).norm).trans
      ((summable_dampedSquareDirichlet hε hh).norm.tsum_le_tsum
        (fun n => square_dirichlet_term_norm_le hε n t) hs)
  have hint : Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*squareMellinLine X σ t) := by
    apply ((squareMellinLine_integrable hX σ).norm.const_mul
      (∑' n : ℕ,(n : ℝ)^(-σ))).mono'
      ((continuous_dampedSquareDirichlet_vertical hε hσ).mul
        (squareMellinLine_continuous hX σ)).aestronglyMeasurable
    filter_upwards with t
    rw [Pi.mul_apply,norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)
  simpa only [squareMellinLine,mul_assoc] using hint

private theorem physical_window_inverse_zero {X : ℝ} (hX : 1 ≤ X) :
    bagPhysicalHeightWindow (1/X) = 0 := by
  have hX0 : 0 < X := by linarith
  have hx : 1/X ≤ 1 := (div_le_one hX0).mpr hX
  by_contra hn
  have hm : 1/X ∈ Metric.ball (3/2 : ℝ) bagPhysicalHeightWindow.rOut := by
    rw [← bagPhysicalHeightWindow.support_eq]
    exact hn
  have ha : |1/X-3/2| < (1/2 : ℝ) := by
    simpa only [Metric.mem_ball,Real.dist_eq,bagPhysicalHeightWindow] using hm
  linarith [(abs_lt.mp ha).1]

private theorem squareMellinLine_integral_zero {X : ℝ} (hX : 1 ≤ X) (σ : ℝ) :
    (∫ t : ℝ,squareMellinLine X σ t) = 0 := by
  have h := square_perron_term (by linarith : 0 < X) σ (n := 1) (by omega)
  simpa only [Nat.cast_one,Complex.one_cpow,one_mul,physical_window_inverse_zero hX,
    Complex.ofReal_zero,mul_zero] using h

private theorem squareContour_on_original_line {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1/16)
    {σ : ℝ} (hσ : 1 < σ) (X t : ℝ) :
    dampedSquareContourIntegrand ε X ((σ : ℂ)+t*I) =
      (dampedSquareDirichlet ε ((σ : ℂ)+t*I)*squareMellinLine X σ t-
        squareMellinLine X σ t)/(ε : ℂ)^2 := by
  rw [dampedSquareContourIntegrand,
    ← dampedSquareDirichlet_eq_continuation hε hε1 (by simpa using hσ),squareMellinLine]
  ring

/-- The literal normalized contour line is absolutely integrable. -/
theorem integrable_dampedSquareContour_original_line {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε < 1/16) (hX : 0 < X) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => dampedSquareContourIntegrand ε X ((σ : ℂ)+t*I)) := by
  have hS : Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*squareMellinLine X σ t) := by
    simpa only [squareMellinLine,mul_assoc] using integrable_dampedSquareDirichlet_window hε hX hσ
  have h := (hS.sub (squareMellinLine_integrable hX σ)).div_const ((ε : ℂ)^2)
  simpa only [squareContour_on_original_line hε hε1 hσ X,Pi.sub_apply] using h

/-- Exact source-to-contour passage after removing n=1, with damping squared retained. -/
theorem dampedSquare_weighted_sum_normalized_eq_integral {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε < 1/16) (hX : 1 ≤ X) (hσ : 1 < σ) :
    (2*Real.pi : ℂ)*(∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*
        (bagPhysicalHeightWindow (n/X) : ℂ))/(ε : ℂ)^2 =
      ∫ t : ℝ,dampedSquareContourIntegrand ε X ((σ : ℂ)+t*I) := by
  have hX0 : 0 < X := by linarith
  have hS : Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*squareMellinLine X σ t) := by
    simpa only [squareMellinLine,mul_assoc] using integrable_dampedSquareDirichlet_window hε hX0 hσ
  simp_rw [squareContour_on_original_line hε hε1 hσ X]
  rw [integral_div,integral_sub hS (squareMellinLine_integrable hX0 σ),
    squareMellinLine_integral_zero hX,sub_zero]
  congr 1
  simpa only [squareMellinLine,mul_assoc] using dampedSquare_weighted_sum_eq_integral hε hX0 hσ

end RHTower.BAGTrace
