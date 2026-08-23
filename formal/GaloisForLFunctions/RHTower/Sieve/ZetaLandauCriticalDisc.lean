import GaloisForLFunctions.RHTower.Sieve.LandauLemma
import GaloisForLFunctions.RHTower.Sieve.ZetaWideDisc
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# The Landau disc that reaches the critical line

Landau's lemma applied at the centre `9/8 + iγ` with radius `5` places the zeros within `5/2` and
gives the partial-fraction identity within `5/8` — and `9/8 − 5/8 = 1/2`, so the identity is
available on the whole segment from the critical line to the centre.  The growth input is the
polynomial bound for `ζ` on a vertical strip, which is what makes a disc of this size affordable.
-/

namespace RHTower.Sieve

open Complex Metric

noncomputable section

/-- The centre of the critical Landau disc. -/
def critCentre (γ : ℝ) : ℂ := ((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I

theorem critCentre_re (γ : ℝ) : (critCentre γ).re = 9 / 8 := by
  rw [critCentre]; simp

theorem critCentre_im (γ : ℝ) : (critCentre γ).im = γ := by
  rw [critCentre]; simp

/-- Real and imaginary parts on the critical Landau disc. -/
theorem crit_disc_parts {γ : ℝ} (hγ : 7 ≤ |γ|) {w : ℂ} (hw : ‖w - critCentre γ‖ < 6) :
    |w.re| ≤ 8 ∧ 1 ≤ |w.im| ∧ |w.im| ≤ 2 * |γ| := by
  have hre : |w.re - 9 / 8| ≤ ‖w - critCentre γ‖ := by
    have h := Complex.abs_re_le_norm (w - critCentre γ)
    rwa [Complex.sub_re, critCentre_re] at h
  have him : |w.im - γ| ≤ ‖w - critCentre γ‖ := by
    have h := Complex.abs_im_le_norm (w - critCentre γ)
    rwa [Complex.sub_im, critCentre_im] at h
  refine ⟨?_, ?_, ?_⟩
  · have h1 : |w.re - 9 / 8| < 6 := lt_of_le_of_lt hre hw
    rw [abs_lt] at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  · have h1 : |w.im - γ| < 6 := lt_of_le_of_lt him hw
    have h2 : |γ| - |w.im| ≤ |γ - w.im| := abs_sub_abs_le_abs_sub γ w.im
    have h3 : |γ - w.im| = |w.im - γ| := abs_sub_comm γ w.im
    rw [h3] at h2
    linarith
  · have h1 : |w.im - γ| < 6 := lt_of_le_of_lt him hw
    have h2 : |w.im| - |γ| ≤ |w.im - γ| := abs_sub_abs_le_abs_sub w.im γ
    linarith

/-- **The growth bound on the critical Landau disc.** -/
theorem exists_crit_disc_bound :
    ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ γ : ℝ, 7 ≤ |γ| → ∀ w : ℂ, ‖w - critCentre γ‖ < 6 →
      ‖riemannZeta w‖ ≤ C * |γ| ^ N := by
  obtain ⟨C₀, N, hC₀, hb⟩ := RHTower.exists_bound_norm_riemannZeta_strip 8
  refine ⟨(C₀ + 1) * 2 ^ N, N, ?_, ?_⟩
  · have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  · intro γ hγ w hw
    obtain ⟨hre, him1, him2⟩ := crit_disc_parts hγ hw
    have hw' : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im w).symm
    have h := hb w.re w.im hre him1
    rw [← hw'] at h
    refine h.trans ?_
    have hmono : |w.im| ^ N ≤ (2 * |γ|) ^ N := pow_le_pow_left₀ (abs_nonneg _) him2 N
    have hexp : (2 * |γ|) ^ N = 2 ^ N * |γ| ^ N := by rw [mul_pow]
    rw [hexp] at hmono
    have hγ0 : (0 : ℝ) ≤ |γ| ^ N := by positivity
    nlinarith [hmono, hC₀, hγ0, pow_nonneg (abs_nonneg (w.im)) N]

/-- The value at the centre is not zero. -/
theorem zeta_critCentre_ne_zero (γ : ℝ) : riemannZeta (critCentre γ) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  rw [critCentre_re]
  norm_num

/-- The critical Landau disc avoids the pole. -/
theorem crit_disc_ne_one {γ : ℝ} (hγ : 7 ≤ |γ|) {w : ℂ} (hw : ‖w - critCentre γ‖ < 6) :
    w ≠ 1 := by
  intro hcon
  have him : |w.im - γ| ≤ ‖w - critCentre γ‖ := by
    have h := Complex.abs_im_le_norm (w - critCentre γ)
    rwa [Complex.sub_im, critCentre_im] at h
  have h1 : w.im = 0 := by rw [hcon]; simp
  rw [h1] at him
  simp only [zero_sub, abs_neg] at him
  linarith

/-- **Analyticity on the critical Landau disc.** -/
theorem zeta_analytic_crit {γ : ℝ} (hγ : 7 ≤ |γ|) :
    AnalyticOnNhd ℂ riemannZeta (ball (critCentre γ) 6) :=
  (differentiableOn_riemannZeta_of_ne_one fun _ hw =>
    crit_disc_ne_one hγ (by simpa [dist_eq_norm] using hw)).analyticOnNhd isOpen_ball

/-- **Landau's data on the critical disc.**  The zeros are collected within `5/2` of the centre and
the partial-fraction identity holds within `5/8`, which reaches the critical line exactly. -/
theorem exists_crit_landau_data :
    ∃ D : ℝ, 0 < D ∧ ∀ γ : ℝ, 7 ≤ |γ| →
      ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
        (∀ ρ ∈ Z, ‖ρ - critCentre γ‖ ≤ 5 / 2) ∧
        (∀ ρ ∈ Z, riemannZeta ρ = 0) ∧
        (∀ w : ℂ, ‖w - critCentre γ‖ ≤ 5 / 2 → riemannZeta w = 0 → w ∈ Z) ∧
        (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
        ∀ z : ℂ, ‖z - critCentre γ‖ ≤ 5 / 8 → riemannZeta z ≠ 0 →
          ‖logDeriv riemannZeta z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ D * Real.log |γ| := by
  obtain ⟨C, N, hC1, hbnd⟩ := exists_crit_disc_bound
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have h11 : (0 : ℝ) ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  refine ⟨16 / 5 * (Real.log 2 + Real.log C + 3 / 4 * Real.log 9 + 1 / 4 * Real.log 11
      + (N : ℝ) + 1 / 4), by nlinarith, ?_⟩
  intro γ hγ
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hlogγ : (1 : ℝ) ≤ Real.log |γ| := by
    have he : Real.exp 1 < 7 := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ |γ|)
    rwa [Real.log_exp] at h
  have hcz : riemannZeta (critCentre γ) ≠ 0 := zeta_critCentre_ne_zero γ
  have hcpos : (0 : ℝ) < ‖riemannZeta (critCentre γ)‖ := norm_pos_iff.mpr hcz
  have hbc : ‖riemannZeta (critCentre γ)‖ ≤ C * |γ| ^ N := by
    refine hbnd γ hγ (critCentre γ) ?_
    rw [sub_self, norm_zero]
    norm_num
  have hX1 : (1 : ℝ) ≤ C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖ := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hM1 : (1 : ℝ) < 1 + C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖ := by linarith
  have hMbound : ∀ w ∈ ball (critCentre γ) 6,
      ‖riemannZeta w‖
        ≤ (1 + C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖) * ‖riemannZeta (critCentre γ)‖ := by
    intro w hw
    have hwn : ‖w - critCentre γ‖ < 6 := by simpa [dist_eq_norm] using hw
    refine (hbnd γ hγ w hwn).trans ?_
    have hid : (C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖) * ‖riemannZeta (critCentre γ)‖
        = C * |γ| ^ N := by field_simp
    rw [add_mul, one_mul, hid]
    linarith
  obtain ⟨Z, m, h1, h2z, h3, h4, h5⟩ :=
    landau_logDeriv (f := riemannZeta) (c := critCentre γ) (R := 5) (R₀ := 6)
      (M := 1 + C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖)
      (by norm_num) (by norm_num) hM1 (zeta_analytic_crit hγ) hcz hMbound
  refine ⟨Z, m, fun ρ hρ => by linarith [h1 ρ hρ], h2z,
    fun w hw hz => h3 w (by linarith) hz, h4, ?_⟩
  intro z hz hzne
  refine (h5 z (by linarith) hzne).trans ?_
  have hMle : (1 : ℝ) + C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖
      ≤ 2 * (C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖) := by linarith
  have hlogM : Real.log (1 + C * |γ| ^ N / ‖riemannZeta (critCentre γ)‖)
      ≤ Real.log 2 + Real.log C + (N : ℝ) * Real.log |γ|
        - Real.log ‖riemannZeta (critCentre γ)‖ := by
    have hstep := Real.log_le_log (by linarith) hMle
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_div (by positivity) hcpos.ne',
      Real.log_mul (by linarith) (by positivity), Real.log_pow] at hstep
    linarith
  have hneg : -Real.log ‖riemannZeta (critCentre γ)‖
      ≤ 3 / 4 * Real.log 9 + 1 / 4 * Real.log 11 + 1 / 4 * Real.log |γ| := by
    have hbase := neg_log_norm_riemannZeta_le (σ := 9 / 8) (t := γ)
      (by norm_num) (by norm_num) (by linarith)
    have hval : (1 : ℝ) + 1 / (9 / 8 - 1) = 9 := by norm_num
    rw [hval] at hbase
    have hfour : Real.log (7 + 4 * |γ|) ≤ Real.log 11 + Real.log |γ| := by
      have hle : (7 : ℝ) + 4 * |γ| ≤ 11 * |γ| := by linarith
      have h := Real.log_le_log (by linarith : (0:ℝ) < 7 + 4 * |γ|) hle
      rwa [Real.log_mul (by norm_num) hγ0.ne'] at h
    rw [critCentre]
    linarith
  nlinarith [hlogM, hneg, hlogγ, hlogC, h2, h9, h11, hN]

end

end RHTower.Sieve
