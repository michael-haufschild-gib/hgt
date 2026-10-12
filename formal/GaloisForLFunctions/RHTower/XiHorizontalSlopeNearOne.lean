import GaloisForLFunctions.RHTower.XiHorizontalLogDerivativeModel
import GaloisForLFunctions.RHTower.ZetaPoleBoundExplicit

/-!
# The horizontal slope of `ξ` down to the line `Re s = 1`

The corpus slope model (`norm_logDeriv_xi_sub_horizontalSlope_le`) works on `5 ≤ σ ≤ X/32`, where
`‖ζ'/ζ‖ ≤ π⁴/90 − 1`. Below `σ = 5` the only change is the size of `ζ'/ζ`. The Dirichlet series
`−ζ'/ζ = Σ Λ(n) n^{−s}` has nonnegative coefficients, so

`‖ζ'/ζ(σ + iX)‖ ≤ −ζ'/ζ(σ) ≤ 1/(σ − 1) + 2`   for every `σ > 1`

(`norm_logDeriv_riemannZeta_le_inv_sub_one_add_two`), using the pole bound
`−ζ'/ζ(σ) ≤ 1/(σ − 1) + 1` on `(1, 2]` and monotonicity in `σ` beyond `2`. Hence on `1 < σ ≤ X/32`,
`X ≥ 200`:

`‖ξ'/ξ(σ + iX) − (½ log(X/2π) + iπ/4)‖ ≤ 1/(σ − 1) + 3`

(`norm_logDeriv_xi_sub_horizontalSlope_le_near`). This is the slope input that lets a Gaussian window
start just right of `σ = 1` instead of at `σ = 5`.
-/

open Complex

namespace RHTower.DeBruijn

noncomputable section

/-- The von Mangoldt `L`-series term at a real point is real. -/
theorem term_vonMangoldt_ofReal (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n =
      ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    ring

/-- `−ζ'/ζ(σ) = Σ Λ(n) n^{−σ}` for real `σ > 1`. -/
theorem re_neg_logDeriv_riemannZeta_real_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, LSeries]
  simp_rw [term_vonMangoldt_ofReal]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

/-- Summability of `Λ(n) n^{−σ}` for `σ > 1`. -/
private theorem summable_vonMangoldt_div_rpow_near {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  have h2 := h.mapL Complex.reCLM
  refine h2.congr fun n => ?_
  simp only [Complex.reCLM_apply]
  rw [term_vonMangoldt_ofReal, Complex.ofReal_re]

/-- `‖ζ'/ζ(σ + iX)‖ ≤ Σ Λ(n) n^{−σ}`. -/
theorem norm_logDeriv_riemannZeta_le_tsum {σ : ℝ} (hσ : 1 < σ) (X : ℝ) :
    ‖logDeriv riemannZeta ((σ : ℂ) + X * I)‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  set s : ℂ := (σ : ℂ) + X * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hre : 1 < s.re := by rw [hsre]; exact hσ
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hlog : logDeriv riemannZeta s =
      -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    rw [hL, logDeriv_apply]; ring
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
    intro n
    rw [LSeries.norm_term_eq, hsre]
    split_ifs with h0
    · subst h0; simp
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hsum := summable_vonMangoldt_div_rpow_near hσ
  have hnorm : Summable fun n =>
      ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ := by
    simp_rw [hterm]; exact hsum
  rw [hlog, norm_neg, LSeries]
  calc ‖∑' n, LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ = _ := by simp_rw [hterm]

/-- **`‖ζ'/ζ(σ + iX)‖ ≤ 1/(σ − 1) + 2`** for every `σ > 1`. -/
theorem norm_logDeriv_riemannZeta_le_inv_sub_one_add_two {σ : ℝ} (hσ : 1 < σ) (X : ℝ) :
    ‖logDeriv riemannZeta ((σ : ℂ) + X * I)‖ ≤ 1 / (σ - 1) + 2 := by
  refine (norm_logDeriv_riemannZeta_le_tsum hσ X).trans ?_
  have hinv : 0 < 1 / (σ - 1) := by have : 0 < σ - 1 := by linarith
                                    positivity
  rcases le_or_gt σ 2 with h2 | h2
  · rw [← re_neg_logDeriv_riemannZeta_real_eq_tsum hσ]
    linarith [neg_re_logDeriv_riemannZeta_real_le hσ h2]
  · -- monotonicity in `σ`, then the value at `2`
    have hmono : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ ≤
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 : ℝ) := by
      refine (summable_vonMangoldt_div_rpow_near hσ).tsum_le_tsum (fun n => ?_)
        (summable_vonMangoldt_div_rpow_near (by norm_num))
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (by positivity)
          (Real.rpow_le_rpow_of_exponent_le hn1 h2.le)
    have h2v := neg_re_logDeriv_riemannZeta_real_le (σ := 2) (by norm_num) le_rfl
    rw [re_neg_logDeriv_riemannZeta_real_eq_tsum (by norm_num)] at h2v
    have e2 : (1 : ℝ) / (2 - 1) + 1 = 2 := by norm_num
    rw [e2] at h2v
    linarith

/-- **The slope model near `σ = 1`.** On `1 < σ ≤ X/32`, `X ≥ 200`,
`‖ξ'/ξ(σ + iX) − a‖ ≤ 1/(σ − 1) + 3`. -/
theorem norm_logDeriv_xi_sub_horizontalSlope_le_near {σ X : ℝ} (hσ : 1 < σ) (hσX : σ ≤ X / 32)
    (hX : 200 ≤ X) :
    ‖logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X‖ ≤ 1 / (σ - 1) + 3 := by
  have hX0 : 0 < X := by linarith
  set s : ℂ := (σ : ℂ) + X * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = X := by simp [hs]
  have hsX : X ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    rwa [hsim, abs_of_pos hX0] at this
  have hs1X : X ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rwa [Complex.sub_im, hsim, Complex.one_im, sub_zero, abs_of_pos hX0] at this
  have hs2 : X / 2 ≤ ‖s / 2‖ := by
    rw [norm_div, Complex.norm_ofNat]; linarith
  have h1 : ‖1 / s‖ ≤ 1 / X := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hX0 hsX
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / X := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hX0 hs1X
  have h3 : ‖1 / (2 * s)‖ ≤ 1 / (2 * X) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hD := GaloisForLFunctions.HTGeometry.norm_digammaStirlingDefect_le
    (z := s / 2) (by simp [hsre]; linarith) (by linarith)
  have h4 : ‖GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2‖ ≤ 12 / X ^ 2 := by
    rw [norm_div, Complex.norm_ofNat]
    have hsq : (X / 2) ^ 2 ≤ ‖s / 2‖ ^ 2 := by gcongr
    have : 6 / ‖s / 2‖ ^ (2 : ℕ) ≤ 6 / (X / 2) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    calc ‖GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2)‖ / 2
        ≤ 6 / (X / 2) ^ 2 / 2 := by gcongr; exact hD.trans this
      _ = 12 / X ^ 2 := by field_simp; ring
  have h5 := norm_logDeriv_riemannZeta_le_inv_sub_one_add_two hσ X
  have hsmall : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 ≤ 1 / 64 := by
    have e : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 = (5 * X + 24) / (2 * X ^ 2) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg X]
  -- the remainder after the logarithmic term
  have hrem : ‖logDeriv xi s - horizontalSlope X - Complex.log (1 - I * (σ / X : ℝ)) / 2‖ ≤
      1 / 64 + (1 / (σ - 1) + 2) := by
    rw [logDeriv_xi_sub_horizontalSlope_eq hσ hX0, add_sub_cancel_left]
    calc ‖1 / s + 1 / (s - 1) - 1 / (2 * s) +
          GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2 +
            logDeriv riemannZeta s‖
        ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / (2 * s)‖ +
            ‖GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2‖ +
            ‖logDeriv riemannZeta s‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 + (1 / (σ - 1) + 2) := by gcongr
      _ ≤ 1 / 64 + (1 / (σ - 1) + 2) := by linarith
  -- the logarithmic term
  set z : ℂ := -(I * (σ / X : ℝ)) with hz
  have hzn : ‖z‖ = σ / X := by
    rw [hz, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have : 0 < σ := by linarith
                        positivity)]
  have hzle : ‖z‖ ≤ 1 / 32 := by
    rw [hzn, div_le_iff₀ hX0]; linarith
  have hlog := Complex.norm_log_one_add_le (z := z) (by linarith)
  have hlog' : ‖Complex.log (1 - I * (σ / X : ℝ))‖ ≤ 1 / 30 := by
    rw [sub_eq_add_neg, ← hz]
    refine hlog.trans ?_
    have h0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖z‖)]
  calc ‖logDeriv xi s - horizontalSlope X‖
      ≤ ‖logDeriv xi s - horizontalSlope X - Complex.log (1 - I * (σ / X : ℝ)) / 2‖ +
          ‖Complex.log (1 - I * (σ / X : ℝ)) / 2‖ := by
        have h := norm_add_le
          (logDeriv xi s - horizontalSlope X - Complex.log (1 - I * (σ / X : ℝ)) / 2)
          (Complex.log (1 - I * (σ / X : ℝ)) / 2)
        rwa [sub_add_cancel] at h
    _ ≤ (1 / 64 + (1 / (σ - 1) + 2)) + 1 / 30 / 2 := by
        refine add_le_add hrem ?_
        rw [norm_div, Complex.norm_ofNat]
        gcongr
    _ ≤ 1 / (σ - 1) + 3 := by linarith

end

end RHTower.DeBruijn
