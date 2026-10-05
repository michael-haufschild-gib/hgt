import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquarePerron
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindow

/-!
# Divisor-square sum to the normalized moving contour for an arbitrary smooth window

For `W` smooth with support in `[a,b] ⊂ (0,∞)`, every divisor-square coefficient is retained in
Mellin inversion; a complete summable majorant justifies the integral-series exchange. When
`a X ≥ 1` the window kills `n = 1`, and removing that term and dividing by `ε²` gives the
normalized contour integrand on every line `Re s = σ > 1`.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.TestFunctionPerron
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

variable {W : ℝ → ℂ} {a b : ℝ}

private def testSquareMellinLine (W : ℝ → ℂ) (X σ t : ℝ) : ℂ :=
  dampedSquareTestMellin W ((σ : ℂ)+t*I)*(X : ℂ)^((σ : ℂ)+t*I)

private theorem testSquareMellinLine_norm (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖testSquareMellinLine W X σ t‖ = X^σ*‖dampedSquareTestMellin W ((σ : ℂ)+t*I)‖ := by
  rw [testSquareMellinLine,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp [mul_comm]

private theorem testSquareMellinLine_continuous (hW : IsTest W a b) {X : ℝ} (hX : 0 < X) (σ : ℝ) :
    Continuous (testSquareMellinLine W X σ) := by
  have hM : Continuous (fun t : ℝ => dampedSquareTestMellin W ((σ : ℂ)+t*I)) :=
    (differentiable_dampedSquareTestMellin hW).continuous.comp (by fun_prop)
  exact hM.mul (Continuous.const_cpow (by fun_prop)
    (.inl (Complex.ofReal_ne_zero.mpr hX.ne')))

private theorem testSquareMellinLine_integrable (hW : IsTest W a b) {X : ℝ} (hX : 0 < X) (σ : ℝ) :
    Integrable (testSquareMellinLine W X σ) := by
  apply ((integrable_dampedSquareTestMellin_vertical hW σ).norm.const_mul (X^σ)).mono'
    (testSquareMellinLine_continuous hW hX σ).aestronglyMeasurable
  exact ae_of_all _ (fun t => (testSquareMellinLine_norm W hX σ t).le)

private theorem test_square_perron_term (hW : IsTest W a b) {X : ℝ} (hX : 0 < X) (σ : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (∫ t : ℝ,(n : ℂ)^(-((σ : ℂ)+t*I))*testSquareMellinLine W X σ t) =
      (2*Real.pi : ℂ)*W (n/X) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv := mellinInv_dampedSquareTestMellin hW σ (div_pos hnR hX)
  have hscale : ∀ s : ℂ, (n : ℂ)^(-s)*(X : ℂ)^s = ((n/X : ℝ) : ℂ)^(-s) := by
    intro s
    have hm := Complex.mul_cpow_ofReal_nonneg (div_nonneg hnR.le hX.le) hX.le (-s)
    rw [← Complex.ofReal_mul,div_mul_cancel₀ _ hX.ne',Complex.ofReal_natCast] at hm
    have hc : (X : ℂ)^(-s)*(X : ℂ)^s = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
      simp
    rw [hm,mul_assoc,hc,mul_one]
  have he : (∫ t : ℝ,(n : ℂ)^(-((σ : ℂ)+t*I))*testSquareMellinLine W X σ t) =
      ∫ t : ℝ,((n/X : ℝ) : ℂ)^(-((σ : ℂ)+t*I))*
        dampedSquareTestMellin W ((σ : ℂ)+t*I) := by
    apply integral_congr_ae (ae_of_all _ (fun t => ?_))
    rw [testSquareMellinLine]
    calc _ = ((n : ℂ)^(-((σ : ℂ)+t*I))*(X : ℂ)^((σ : ℂ)+t*I))*
        dampedSquareTestMellin W ((σ : ℂ)+t*I) := by ring
      _ = _ := by rw [hscale]
  rw [he,← hinv,mellinInv,Complex.real_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  have hp : (2*Real.pi : ℂ)*((1/(2*Real.pi) : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [hp,one_mul]

private theorem test_square_perron_of_bounded (hW : IsTest W a b) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    (ha0 : a 0 = 0) {X σ : ℝ} (hX : 0 < X) (hσ : 1 < σ) :
    (2*Real.pi : ℂ)*(∑' n : ℕ,a n*W (n/X)) =
      ∫ t : ℝ,(∑' n : ℕ,a n*(n : ℂ)^(-((σ : ℂ)+t*I)))*testSquareMellinLine W X σ t := by
  let Lm := testSquareMellinLine W X σ
  let F : ℕ → ℝ → ℂ := fun n t => a n*(n : ℂ)^(-((σ : ℂ)+t*I))*Lm t
  have hLm : Integrable Lm := testSquareMellinLine_integrable hW hX σ
  have hnorm : ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      ‖F n t‖ = ‖a n‖*(n : ℝ)^(-σ)*‖Lm t‖ := by
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
        (.inl (Nat.cast_ne_zero.mpr hn.ne')))).mul (testSquareMellinLine_continuous hW hX σ)
    apply (hLm.norm.const_mul (‖a n‖*(n : ℝ)^(-σ))).mono' hc.aestronglyMeasurable
    exact ae_of_all _ (fun t => (hnorm n hn t).le)
  let V : ℝ := ∫ t : ℝ,‖Lm t‖
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
      (2*Real.pi : ℂ)*(a n*W (n/X)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F,ha0]
    have he : F n = fun t : ℝ => a n*((n : ℂ)^(-((σ : ℂ)+t*I))*testSquareMellinLine W X σ t) := by
      funext t
      dsimp [F,Lm]
      ring
    rw [he,integral_const_mul,test_square_perron_term hW hX σ hn]
    ring
  calc _ = ∑' n : ℕ,(2*Real.pi : ℂ)*(a n*W (n/X)) :=
      tsum_mul_left.symm
    _ = ∑' n : ℕ,∫ t : ℝ,F n t := tsum_congr (fun n => (hterm n).symm)
    _ = ∫ t : ℝ,∑' n : ℕ,F n t := hHS.tsum_eq
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ (fun t => ?_))
      exact tsum_mul_right

/-- Exact summed Mellin inversion for every actual divisor-square coefficient. -/
theorem dampedSquareTest_weighted_sum_eq_integral (hW : IsTest W a b) {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hX : 0 < X) (hσ : 1 < σ) :
    (2*Real.pi : ℂ)*(∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*
        W (n/X)) =
      ∫ t : ℝ,dampedSquareDirichlet ε ((σ : ℂ)+t*I)*
        dampedSquareTestMellin W ((σ : ℂ)+t*I)*(X : ℂ)^((σ : ℂ)+t*I) := by
  have ha : ∀ n : ℕ, ‖(pmPowerDampedDivisorCoeff ε n : ℂ)^2‖ ≤ 1 := by
    intro n
    rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε n)]
    exact pow_le_one₀ (pmPowerDampedDivisorCoeff_nonneg hε n)
      (pmPowerDampedDivisorCoeff_le_one hε n)
  have h := test_square_perron_of_bounded hW ha (by simp [pmPowerDampedDivisorCoeff_zero]) hX hσ
  simpa only [dampedSquareDirichlet,testSquareMellinLine,mul_assoc] using h

private theorem test_square_dirichlet_term_norm_le {ε σ : ℝ} (hε : 0 ≤ ε)
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

/-- Absolute integrability of the actual full source line used in Mellin inversion. -/
theorem integrable_dampedSquareDirichlet_testWindow (hW : IsTest W a b) {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hX : 0 < X) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*
      dampedSquareTestMellin W ((σ : ℂ)+t*I)*(X : ℂ)^((σ : ℂ)+t*I)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbound : ∀ t : ℝ, ‖dampedSquareDirichlet ε ((σ : ℂ)+t*I)‖ ≤ ∑' n : ℕ,(n : ℝ)^(-σ) := by
    intro t
    have hh : 1 < ((σ : ℂ)+t*I).re := by simpa using hσ
    exact (norm_tsum_le_tsum_norm (summable_dampedSquareDirichlet hε hh).norm).trans
      ((summable_dampedSquareDirichlet hε hh).norm.tsum_le_tsum
        (fun n => test_square_dirichlet_term_norm_le hε n t) hs)
  have hint : Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*testSquareMellinLine W X σ t) := by
    apply ((testSquareMellinLine_integrable hW hX σ).norm.const_mul
      (∑' n : ℕ,(n : ℝ)^(-σ))).mono'
      ((continuous_dampedSquareDirichlet_vertical hε hσ).mul
        (testSquareMellinLine_continuous hW hX σ)).aestronglyMeasurable
    filter_upwards with t
    rw [Pi.mul_apply,norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)
  simpa only [testSquareMellinLine,mul_assoc] using hint

private theorem test_window_inverse_zero (hW : IsTest W a b) {X : ℝ} (hX : 0 < X)
    (haX : 1 ≤ a*X) : W (1/X) = 0 :=
  hW.eq_zero_of_le ((div_le_iff₀ hX).mpr (by linarith))

private theorem testSquareMellinLine_integral_zero (hW : IsTest W a b) {X : ℝ} (hX : 1 ≤ X)
    (haX : 1 ≤ a*X) (σ : ℝ) :
    (∫ t : ℝ,testSquareMellinLine W X σ t) = 0 := by
  have h := test_square_perron_term hW (by linarith : 0 < X) σ (n := 1) (by omega)
  simpa only [Nat.cast_one,Complex.one_cpow,one_mul,test_window_inverse_zero hW (by linarith) haX,
    Complex.ofReal_zero,mul_zero] using h

private theorem testSquareContour_on_original_line {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1/16)
    {σ : ℝ} (hσ : 1 < σ) (X t : ℝ) :
    dampedSquareTestContourIntegrand W ε X ((σ : ℂ)+t*I) =
      (dampedSquareDirichlet ε ((σ : ℂ)+t*I)*testSquareMellinLine W X σ t-
        testSquareMellinLine W X σ t)/(ε : ℂ)^2 := by
  rw [dampedSquareTestContourIntegrand,
    ← dampedSquareDirichlet_eq_continuation hε hε1 (by simpa using hσ),testSquareMellinLine]
  ring

/-- The literal normalized contour line is absolutely integrable. -/
theorem integrable_dampedSquareTestContour_original_line (hW : IsTest W a b) {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε < 1/16) (hX : 0 < X) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => dampedSquareTestContourIntegrand W ε X ((σ : ℂ)+t*I)) := by
  have hS : Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*testSquareMellinLine W X σ t) := by
    simpa only [testSquareMellinLine,mul_assoc] using integrable_dampedSquareDirichlet_testWindow hW hε hX hσ
  have h := (hS.sub (testSquareMellinLine_integrable hW hX σ)).div_const ((ε : ℂ)^2)
  simpa only [testSquareContour_on_original_line hε hε1 hσ X,Pi.sub_apply] using h

/-- Exact source-to-contour passage after removing n=1, with damping squared retained. -/
theorem dampedSquareTest_weighted_sum_normalized_eq_integral (hW : IsTest W a b) {ε X σ : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε < 1/16) (hX : 1 ≤ X) (haX : 1 ≤ a*X) (hσ : 1 < σ) :
    (2*Real.pi : ℂ)*(∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*
        W (n/X))/(ε : ℂ)^2 =
      ∫ t : ℝ,dampedSquareTestContourIntegrand W ε X ((σ : ℂ)+t*I) := by
  have hX0 : 0 < X := by linarith
  have hS : Integrable (fun t : ℝ => dampedSquareDirichlet ε ((σ : ℂ)+t*I)*testSquareMellinLine W X σ t) := by
    simpa only [testSquareMellinLine,mul_assoc] using integrable_dampedSquareDirichlet_testWindow hW hε hX0 hσ
  simp_rw [testSquareContour_on_original_line hε hε1 hσ X]
  rw [integral_div,integral_sub hS (testSquareMellinLine_integrable hW hX0 σ),
    testSquareMellinLine_integral_zero hW hX haX,sub_zero]
  congr 1
  simpa only [testSquareMellinLine,mul_assoc] using dampedSquareTest_weighted_sum_eq_integral hW hε hX0 hσ

end RHTower.BAGTrace
