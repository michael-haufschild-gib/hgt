import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# The logarithmic derivative of `ξ` along a horizontal line deep in the Euler region

Fix a height `X ≥ 200` and put `α = ½ log(X/2π)`, `a = α + iπ/4`. For `s = σ + iX` with `σ ≥ 5`,
the four-factor formula `ξ'/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ'/ζ(s)`, Stirling's
`ψ(z) = log z − 1/(2z) + O(6/|z|²)` and the factorization `s/2 = (iX/2)(1 − iσ/X)` give

`ξ'/ξ(s) − a = ½ log(1 − iσ/X) + r(s)`,   `‖r(s)‖ ≤ 5/(2X) + 12/X² + π⁴/90 − 1 ≤ 1/10`

(`norm_logDeriv_xi_sub_horizontalSlope_le`). The prime part uses `Λ(n) ≤ log n ≤ n − 1`, so
`‖ζ'/ζ(s)‖ ≤ Σ_{n≥2} n^{−4} = π⁴/90 − 1` on `Re s ≥ 5`. Consequently:

* on `5 ≤ σ ≤ X/20` the slope is nearly constant: `‖ξ'/ξ(s) − a‖ ≤ 1/8`;
* on `σ ≥ 5` it grows at most logarithmically: `‖ξ'/ξ(s)‖ ≤ α + 2 + σ/(2X)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The horizontal slope `a = ½ log(X/2π) + iπ/4` of `log ξ` at height `X`. -/
def horizontalSlope (X : ℝ) : ℂ := ((Real.log (X / (2 * Real.pi)) / 2 : ℝ) : ℂ) + Real.pi / 4 * I

theorem horizontalSlope_re (X : ℝ) : (horizontalSlope X).re = Real.log (X / (2 * Real.pi)) / 2 := by
  simp [horizontalSlope]

theorem pi_pow_four_div_ninety_sub_one_le : Real.pi ^ 4 / 90 - 1 ≤ 1 / 12 := by
  have h := Real.pi_lt_d4
  have h0 := Real.pi_pos
  have : Real.pi ^ 4 < 3.1416 ^ 4 := by gcongr
  norm_num at this ⊢
  linarith

/-- `‖ζ'/ζ(s)‖ ≤ π⁴/90 − 1` on `Re s ≥ 5`. -/
theorem norm_logDeriv_riemannZeta_le_of_five_le_re {s : ℂ} (hs : 5 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ Real.pi ^ 4 / 90 - 1 := by
  have hre : 1 < s.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hlog : logDeriv riemannZeta s =
      -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    rw [hL, logDeriv_apply]; ring
  rw [hlog, norm_neg, LSeries]
  set f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re with hf
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 4 - if n = 1 then 1 else 0 with hg
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ = f n := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · subst h0; simp [hf]
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    simp only [hf, hg]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hn1 : n ≠ 1 := by omega
      rw [if_neg hn1, sub_zero]
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
      have hpow : (n : ℝ) ^ (5 : ℝ) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hs
      have h5 : (n : ℝ) ^ (5 : ℝ) = (n : ℝ) ^ 5 := by norm_cast
      rw [h5] at hpow
      have hpos : 0 < (n : ℝ) ^ 5 := by positivity
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      calc ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ 4 ≤ (n : ℝ) * (n : ℝ) ^ 4 := by
            gcongr
        _ = 1 * (n : ℝ) ^ 5 := by ring
        _ ≤ 1 * (n : ℝ) ^ s.re := by linarith
  have hg_sum : HasSum g (Real.pi ^ 4 / 90 - 1) :=
    hasSum_zeta_four.sub (hasSum_ite_eq 1 (1 : ℝ))
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hf_sum : Summable f := Summable.of_nonneg_of_le hf0 hfg hg_sum.summable
  have hnorm_sum : Summable fun n =>
      ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ := by
    simp_rw [hterm]; exact hf_sum
  calc ‖∑' n, LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ = ∑' n, f n := by simp_rw [hterm]
    _ ≤ Real.pi ^ 4 / 90 - 1 := hasSum_le hfg hf_sum.hasSum hg_sum

/-- `log(s/2) = log(X/2) + iπ/2 + log(1 − iσ/X)` for `s = σ + iX`, `X > 0`. -/
theorem log_horizontalPoint_half_eq {σ X : ℝ} (hX : 0 < X) :
    Complex.log (((σ : ℂ) + X * I) / 2) =
      (Real.log (X / 2) : ℂ) + Real.pi / 2 * I + Complex.log (1 - I * (σ / X : ℝ)) := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hfac : ((σ : ℂ) + X * I) / 2 = ((X / 2 : ℝ) : ℂ) * (I * (1 - I * (σ / X : ℝ))) := by
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hre : (1 - I * (σ / X : ℝ)).re = 1 := by simp
  have hne : (1 - I * (σ / X : ℝ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
  have harg := (Complex.abs_arg_lt_pi_div_two_iff (z := 1 - I * (σ / X : ℝ))).mpr
    (Or.inl (by rw [hre]; norm_num))
  rw [abs_lt] at harg
  rw [hfac, Complex.log_ofReal_mul (by positivity) (mul_ne_zero I_ne_zero hne),
    Complex.log_mul I_ne_zero hne, Complex.log_I]
  · ring
  · rw [Complex.arg_I]
    constructor <;> linarith [Real.pi_pos]

/-- **The horizontal slope decomposition.** For `s = σ + iX` with `σ > 1`, `X > 0`,
`ξ'/ξ(s) − a = ½ log(1 − iσ/X) + 1/s + 1/(s−1) − 1/(2s) + ½D(s/2) + ζ'/ζ(s)` where `D` is the
Stirling defect of the digamma function. -/
theorem logDeriv_xi_sub_horizontalSlope_eq {σ X : ℝ} (hσ : 1 < σ) (hX : 0 < X) :
    logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X =
      Complex.log (1 - I * (σ / X : ℝ)) / 2 +
        (1 / ((σ : ℂ) + X * I) + 1 / ((σ : ℂ) + X * I - 1) - 1 / (2 * ((σ : ℂ) + X * I)) +
          GaloisForLFunctions.HTGeometry.digammaStirlingDefect (((σ : ℂ) + X * I) / 2) / 2 +
          logDeriv riemannZeta ((σ : ℂ) + X * I)) := by
  set s : ℂ := (σ : ℂ) + X * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  rw [logDeriv_xi_fourFactor (by rw [hsre]; exact hσ)]
  have hdig : Complex.digamma (s / 2) =
      GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) + Complex.log (s / 2) -
        1 / (2 * (s / 2)) := by
    rw [GaloisForLFunctions.HTGeometry.digammaStirlingDefect]
    ring
  rw [hdig, hs, log_horizontalPoint_half_eq hX, horizontalSlope,
    Real.log_div (by positivity) (by positivity), Real.log_div hX.ne' (by norm_num),
    Real.log_mul (by norm_num) Real.pi_pos.ne']
  rw [← hs]
  have h2 : (2 : ℂ) * (s / 2) = s := by ring
  rw [h2]
  push_cast
  ring_nf

/-- The remainder of the slope decomposition is at most `1/12 + 1/64` from height `200` on. -/
theorem norm_logDeriv_xi_sub_horizontalSlope_sub_log_le {σ X : ℝ} (hσ : 5 ≤ σ) (hX : 200 ≤ X) :
    ‖logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X -
        Complex.log (1 - I * (σ / X : ℝ)) / 2‖ ≤ 1 / 12 + 1 / 64 := by
  have hX0 : 0 < X := by linarith
  rw [logDeriv_xi_sub_horizontalSlope_eq (by linarith) hX0, add_sub_cancel_left]
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
  have h5 := norm_logDeriv_riemannZeta_le_of_five_le_re (s := s) (by rw [hsre]; exact hσ)
  have h6 := pi_pow_four_div_ninety_sub_one_le
  have hsmall : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 ≤ 1 / 64 := by
    have e : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 = (5 * X + 24) / (2 * X ^ 2) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg X]
  calc ‖1 / s + 1 / (s - 1) - 1 / (2 * s) +
        GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2 + logDeriv riemannZeta s‖
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
    _ ≤ 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 + (Real.pi ^ 4 / 90 - 1) := by gcongr
    _ ≤ 1 / 12 + 1 / 64 := by linarith

/-- **Nearly constant slope** on `5 ≤ σ ≤ X/32`: `‖ξ'/ξ(σ + iX) − a‖ ≤ 1/8`. -/
theorem norm_logDeriv_xi_sub_horizontalSlope_le {σ X : ℝ} (hσ : 5 ≤ σ) (hσX : σ ≤ X / 32)
    (hX : 200 ≤ X) :
    ‖logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X‖ ≤ 1 / 8 := by
  have hX0 : 0 < X := by linarith
  have hr := norm_logDeriv_xi_sub_horizontalSlope_sub_log_le hσ hX
  set z : ℂ := -(I * (σ / X : ℝ)) with hz
  have hzn : ‖z‖ = σ / X := by
    rw [hz, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
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
  calc ‖logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X‖
      ≤ ‖logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X -
          Complex.log (1 - I * (σ / X : ℝ)) / 2‖ + ‖Complex.log (1 - I * (σ / X : ℝ)) / 2‖ := by
        refine (norm_sub_le_norm_sub_add_norm_sub _ (Complex.log (1 - I * (σ / X : ℝ)) / 2 +
          horizontalSlope X) _).trans (le_of_eq ?_)
        congr 1
        · congr 1; ring
        · rw [show Complex.log (1 - I * (σ / X : ℝ)) / 2 + horizontalSlope X - horizontalSlope X =
            Complex.log (1 - I * (σ / X : ℝ)) / 2 by ring]
    _ ≤ (1 / 12 + 1 / 64) + 1 / 30 / 2 := by
        gcongr
        rw [norm_div, Complex.norm_ofNat]
        gcongr
    _ ≤ 1 / 8 := by norm_num

/-- `‖log z‖ ≤ |log ‖z‖| + |arg z|`. -/
theorem norm_log_le_abs_log_norm_add_abs_arg (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + |Complex.arg z| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]

/-- **Logarithmic growth of the slope** on `σ ≥ 5`: `‖ξ'/ξ(σ + iX)‖ ≤ α + 2 + σ/(2X)`. -/
theorem norm_logDeriv_xi_horizontal_le {σ X : ℝ} (hσ : 5 ≤ σ) (hX : 200 ≤ X) :
    ‖logDeriv xi ((σ : ℂ) + X * I)‖ ≤ Real.log (X / (2 * Real.pi)) / 2 + 2 + σ / (2 * X) := by
  have hX0 : 0 < X := by linarith
  have hr := norm_logDeriv_xi_sub_horizontalSlope_sub_log_le hσ hX
  set c : ℝ := σ / X with hc
  have hc0 : 0 ≤ c := by positivity
  have hα : 0 ≤ Real.log (X / (2 * Real.pi)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d2]
  have hslope : ‖horizontalSlope X‖ ≤ Real.log (X / (2 * Real.pi)) / 2 + Real.pi / 4 := by
    unfold horizontalSlope
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Complex.norm_I, mul_one]
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hlog : ‖Complex.log (1 - I * (c : ℂ))‖ ≤ c + Real.pi / 2 := by
    refine (norm_log_le_abs_log_norm_add_abs_arg _).trans ?_
    have hre : 0 ≤ (1 - I * (c : ℂ)).re := by simp
    have harg := Complex.abs_arg_le_pi_div_two_iff.mpr hre
    have hn1 : 1 ≤ ‖1 - I * (c : ℂ)‖ := by
      have := Complex.re_le_norm (1 - I * (c : ℂ))
      simp at this ⊢
      linarith
    have hn2 : ‖1 - I * (c : ℂ)‖ ≤ 1 + c := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc0]
    have hl0 : 0 ≤ Real.log ‖1 - I * (c : ℂ)‖ := Real.log_nonneg hn1
    have hl1 : Real.log ‖1 - I * (c : ℂ)‖ ≤ c := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖1 - I * (c : ℂ)‖)
      linarith
    rw [abs_of_nonneg hl0]
    linarith
  have hsplit : logDeriv xi ((σ : ℂ) + X * I) =
      (logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X - Complex.log (1 - I * (c : ℂ)) / 2) +
        horizontalSlope X + Complex.log (1 - I * (c : ℂ)) / 2 := by ring
  rw [hsplit]
  calc ‖(logDeriv xi ((σ : ℂ) + X * I) - horizontalSlope X - Complex.log (1 - I * (c : ℂ)) / 2) +
        horizontalSlope X + Complex.log (1 - I * (c : ℂ)) / 2‖
      ≤ (1 / 12 + 1 / 64) + (Real.log (X / (2 * Real.pi)) / 2 + Real.pi / 4) +
          (c + Real.pi / 2) / 2 := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        · refine (norm_add_le _ _).trans ?_
          gcongr
        · rw [norm_div, Complex.norm_ofNat]
          gcongr
    _ ≤ Real.log (X / (2 * Real.pi)) / 2 + 2 + σ / (2 * X) := by
        have : c / 2 = σ / (2 * X) := by rw [hc]; field_simp
        nlinarith [Real.pi_lt_d2]

end

end RHTower
