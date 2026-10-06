import GaloisForLFunctions.RHTower.ZetaNotchCriticalAFE
import GaloisForLFunctions.RHTower.ZetaChiConductorLogSlope

/-!
# Stirling for the critical carrier

At the critical pair the product `χ`-ratio of the approximate functional equation is
`G_t(−w) = χ(½+it−w) χ(½−it−w)` (`critCarrier_neg_eq`).  Against the conductor power
`(t/2π)^{2w}` it satisfies, for `t ≥ 4`, `|Re w| ≤ 1` and `2|Im w| ≤ t`,

`‖G_t(−w) − (t/2π)^{2w}‖ ≤ (t/2π)^{2 Re w} (exp(‖w‖(20‖w‖/t + 52/t²)) − 1)`
(`norm_critCarrier_neg_sub_conductorPow_le`).

**Proof.**  `P(u) = G_t(−u)(t/2π)^{−2u}` has `P(0) = 1` and `P'/P = −Σ_± (χ'/χ(½ ± it − u) + log(t/2π))`.
Each bracket is at most `10‖u‖/t + 26/t²`: the increment of `χ'/χ` across a short shift and the
conductor law `χ'/χ(½+it) = −log(t/2π) + O(t^{−2})` (conjugated for `−t`).  Grönwall along the
segment `σ ↦ P(σw)` gives `‖P(w) − 1‖ ≤ e^ε − 1`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex Set Filter Topology RHTower

/-! ## The `χ`-slope at conjugate heights -/

theorem hasDerivAt_zetaChi {z : ℂ} (hz : Gammaℝ (1 - z) ≠ 0) :
    HasDerivAt zetaChi (deriv zetaChi z) z :=
  (zetaChi_analyticAt hz).differentiableAt.hasDerivAt

theorem gammaR_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Gammaℝ z ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  apply hz
  rw [hn]
  simp

theorem zetaChi_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : zetaChi z ≠ 0 := by
  unfold zetaChi
  refine div_ne_zero (gammaR_ne_zero_of_im_ne_zero ?_) (gammaR_ne_zero_of_im_ne_zero hz)
  simpa using hz

theorem logDeriv_zetaChi_conj {z : ℂ} (hz : Gammaℝ (1 - z) ≠ 0) :
    logDeriv zetaChi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv zetaChi z) := by
  have h := (hasDerivAt_zetaChi hz).conj_conj
  have hfun : (⇑(starRingEnd ℂ) ∘ zetaChi ∘ ⇑(starRingEnd ℂ)) = zetaChi := by
    funext s
    simp [Function.comp_def, zetaChi_conj]
  rw [hfun] at h
  rw [logDeriv_apply, logDeriv_apply, h.deriv, zetaChi_conj, map_div₀]

/-- `χ'/χ(½+iτ+u) = −log(|τ|/2π) + O(‖u‖/|τ| + τ^{−2})` at either sign of the height. -/
theorem norm_logDeriv_zetaChi_linePt_add_log_le {τ : ℝ} (hτ : 4 ≤ |τ|) {u : ℂ}
    (hre₁ : -1 ≤ u.re) (hre₂ : u.re ≤ 1) (him : 2 * |u.im| ≤ |τ|) :
    ‖logDeriv zetaChi (linePt τ + u) + (Real.log (|τ| / (2 * Real.pi)) : ℂ)‖ ≤
      10 * ‖u‖ / |τ| + 26 / τ ^ 2 := by
  have hinc := norm_logDeriv_zetaChi_increment_le hτ him hre₁ hre₂
  have hline : ‖logDeriv zetaChi (linePt τ) + (Real.log (|τ| / (2 * Real.pi)) : ℂ)‖ ≤
      26 / τ ^ 2 := by
    rcases le_or_gt 0 τ with h0 | h0
    · rw [abs_of_nonneg h0] at hτ ⊢
      exact norm_logDeriv_zetaChi_line_add_log_conductor_le hτ
    · have hτ' : 4 ≤ -τ := by rw [abs_of_neg h0] at hτ; exact hτ
      have hb := norm_logDeriv_zetaChi_line_add_log_conductor_le hτ'
      have hconj : linePt τ = (starRingEnd ℂ) (linePt (-τ)) := by
        rw [← linePt_neg_eq_conj, neg_neg]
      have hG : Gammaℝ (1 - linePt (-τ)) ≠ 0 := gammaR_one_sub_linePt_ne_zero (-τ)
      rw [hconj, logDeriv_zetaChi_conj hG, abs_of_neg h0]
      rw [neg_sq] at hb
      have hc : (starRingEnd ℂ) (logDeriv zetaChi (linePt (-τ))) +
          (Real.log (-τ / (2 * Real.pi)) : ℂ) = (starRingEnd ℂ)
            (logDeriv zetaChi (linePt (-τ)) + (Real.log (-τ / (2 * Real.pi)) : ℂ)) := by
        rw [map_add, Complex.conj_ofReal]
      rw [hc, RCLike.norm_conj]
      exact hb
  calc ‖logDeriv zetaChi (linePt τ + u) + (Real.log (|τ| / (2 * Real.pi)) : ℂ)‖
      = ‖(logDeriv zetaChi (linePt τ + u) - logDeriv zetaChi (linePt τ)) +
          (logDeriv zetaChi (linePt τ) + (Real.log (|τ| / (2 * Real.pi)) : ℂ))‖ := by
        congr 1; ring
    _ ≤ 10 * ‖u‖ / |τ| + 26 / τ ^ 2 := (norm_add_le _ _).trans (add_le_add hinc hline)

/-! ## The conductor quotient -/

/-- `P_t(u) = χ(½+it−u) χ(½−it−u) e^{−2u log(t/2π)}`. -/
def critConductorQuot (t : ℝ) (u : ℂ) : ℂ :=
  zetaChi (linePt t - u) * zetaChi (linePt (-t) - u) *
    Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ))

theorem critCarrier_neg_eq (t : ℝ) (u : ℂ) :
    critCarrier t (-u) = zetaChi (linePt t - u) * zetaChi (linePt (-t) - u) := by
  have h1 := zetaChi_mul_zetaChi_line t
  have hne1 := zetaChi_line_ne_zero t
  have hne2 := zetaChi_line_ne_zero (-t)
  unfold critCarrier smoothAFEZetaChiShiftRatio
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, div_mul_div_comm, h1, div_one]

theorem critConductorQuot_zero (t : ℝ) : critConductorQuot t 0 = 1 := by
  unfold critConductorQuot
  rw [sub_zero, sub_zero, zetaChi_mul_zetaChi_line]
  simp

theorem critCarrier_neg_eq_quot_mul {t : ℝ} (ht : 0 < t) (u : ℂ) :
    critCarrier t (-u) = critConductorQuot t u * ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * u) := by
  have hL : (0 : ℝ) < t / (2 * Real.pi) := by positivity
  rw [critCarrier_neg_eq, critConductorQuot, Complex.cpow_def_of_ne_zero (by exact_mod_cast hL.ne'),
    ← Complex.ofReal_log hL.le, mul_assoc, ← Complex.exp_add]
  rw [show -(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ) +
      (Real.log (t / (2 * Real.pi)) : ℂ) * (2 * u) = 0 by ring, Complex.exp_zero, mul_one]

/-- The slope of the conductor quotient. -/
def critConductorSlope (t : ℝ) (u : ℂ) : ℂ :=
  -(logDeriv zetaChi (linePt t - u) + (Real.log (t / (2 * Real.pi)) : ℂ)) -
    (logDeriv zetaChi (linePt (-t) - u) + (Real.log (t / (2 * Real.pi)) : ℂ))

theorem hasDerivAt_critConductorQuot {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : 2 * |u.im| ≤ t) :
    HasDerivAt (critConductorQuot t) (critConductorQuot t u * critConductorSlope t u) u := by
  have him₁ : (linePt t - u).im ≠ 0 := by
    simp [linePt_im]
    intro h; have := le_abs_self u.im; linarith
  have him₂ : (linePt (-t) - u).im ≠ 0 := by
    simp [linePt_im]
    intro h; have := neg_abs_le u.im; linarith
  have hG₁ : Gammaℝ (1 - (linePt t - u)) ≠ 0 := by
    refine gammaR_ne_zero_of_im_ne_zero ?_
    rw [show (1 - (linePt t - u)).im = -((linePt t - u).im) by simp]
    exact neg_ne_zero.mpr him₁
  have hG₂ : Gammaℝ (1 - (linePt (-t) - u)) ≠ 0 := by
    refine gammaR_ne_zero_of_im_ne_zero ?_
    rw [show (1 - (linePt (-t) - u)).im = -((linePt (-t) - u).im) by simp]
    exact neg_ne_zero.mpr him₂
  have hχ₁ : zetaChi (linePt t - u) ≠ 0 := zetaChi_ne_zero_of_im_ne_zero him₁
  have hχ₂ : zetaChi (linePt (-t) - u) ≠ 0 := zetaChi_ne_zero_of_im_ne_zero him₂
  have hd₁ : HasDerivAt (fun u => zetaChi (linePt t - u))
      (deriv zetaChi (linePt t - u) * (-1)) u := by
    have := (hasDerivAt_zetaChi hG₁).comp u ((hasDerivAt_id u).const_sub (linePt t))
    simpa [Function.comp_def] using this
  have hd₂ : HasDerivAt (fun u => zetaChi (linePt (-t) - u))
      (deriv zetaChi (linePt (-t) - u) * (-1)) u := by
    have := (hasDerivAt_zetaChi hG₂).comp u ((hasDerivAt_id u).const_sub (linePt (-t)))
    simpa [Function.comp_def] using this
  have hde : HasDerivAt (fun u : ℂ => Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ)))
      (Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ)) *
        (-(2 * (Real.log (t / (2 * Real.pi)) : ℂ)))) u := by
    have := ((hasDerivAt_id u).const_mul (2 : ℂ)).neg.mul_const
      ((Real.log (t / (2 * Real.pi)) : ℂ))
    simpa using this.cexp
  have h := (hd₁.mul hd₂).mul hde
  have key : HasDerivAt (critConductorQuot t)
      ((deriv zetaChi (linePt t - u) * (-1) * zetaChi (linePt (-t) - u) +
          zetaChi (linePt t - u) * (deriv zetaChi (linePt (-t) - u) * (-1))) *
          Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ)) +
        zetaChi (linePt t - u) * zetaChi (linePt (-t) - u) *
          (Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ)) *
            (-(2 * (Real.log (t / (2 * Real.pi)) : ℂ))))) u := h
  refine key.congr_deriv ?_
  unfold critConductorQuot critConductorSlope
  rw [logDeriv_apply, logDeriv_apply]
  have e₁ := mul_inv_cancel₀ hχ₁
  have e₂ := mul_inv_cancel₀ hχ₂
  linear_combination (deriv zetaChi (linePt t - u) * zetaChi (linePt (-t) - u) *
      Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ))) * e₁ +
    (zetaChi (linePt t - u) * deriv zetaChi (linePt (-t) - u) *
      Complex.exp (-(2 * u) * (Real.log (t / (2 * Real.pi)) : ℂ))) * e₂

/-- The slope is `O(‖u‖/t + t^{−2})`. -/
theorem norm_critConductorSlope_le {t : ℝ} (ht : 4 ≤ t) {u : ℂ} (hre₁ : -1 ≤ u.re)
    (hre₂ : u.re ≤ 1) (him : 2 * |u.im| ≤ t) :
    ‖critConductorSlope t u‖ ≤ 20 * ‖u‖ / t + 52 / t ^ 2 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hu₁ := norm_logDeriv_zetaChi_linePt_add_log_le (τ := t) (u := -u)
    (by rw [abs_of_nonneg ht0]; exact ht) (by simp; linarith) (by simp; linarith)
    (by rw [abs_of_nonneg ht0]; simpa using him)
  have hu₂ := norm_logDeriv_zetaChi_linePt_add_log_le (τ := -t) (u := -u)
    (by rw [abs_neg, abs_of_nonneg ht0]; exact ht) (by simp; linarith) (by simp; linarith)
    (by rw [abs_neg, abs_of_nonneg ht0]; simpa using him)
  rw [abs_of_nonneg ht0] at hu₁
  rw [abs_neg, abs_of_nonneg ht0, neg_sq, norm_neg] at hu₂
  rw [norm_neg] at hu₁
  rw [← sub_eq_add_neg] at hu₁ hu₂
  unfold critConductorSlope
  calc ‖-(logDeriv zetaChi (linePt t - u) + (Real.log (t / (2 * Real.pi)) : ℂ)) -
        (logDeriv zetaChi (linePt (-t) - u) + (Real.log (t / (2 * Real.pi)) : ℂ))‖
      ≤ ‖logDeriv zetaChi (linePt t - u) + (Real.log (t / (2 * Real.pi)) : ℂ)‖ +
          ‖logDeriv zetaChi (linePt (-t) - u) + (Real.log (t / (2 * Real.pi)) : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ (10 * ‖u‖ / t + 26 / t ^ 2) + (10 * ‖u‖ / t + 26 / t ^ 2) := add_le_add hu₁ hu₂
    _ = 20 * ‖u‖ / t + 52 / t ^ 2 := by ring

/-- **Grönwall for the conductor quotient.** -/
theorem norm_critConductorQuot_sub_one_le {t : ℝ} (ht : 4 ≤ t) {w : ℂ} (hre : |w.re| ≤ 1)
    (him : 2 * |w.im| ≤ t) :
    ‖critConductorQuot t w - 1‖ ≤ Real.exp (‖w‖ * (20 * ‖w‖ / t + 52 / t ^ 2)) - 1 := by
  set ε : ℝ := ‖w‖ * (20 * ‖w‖ / t + 52 / t ^ 2) with hε
  have ht0 : 0 < t := by linarith
  have hε0 : 0 ≤ ε := by positivity
  set f : ℝ → ℂ := fun σ => critConductorQuot t ((σ : ℂ) * w) - 1 with hf
  have hseg : ∀ σ ∈ Icc (0 : ℝ) 1, 2 * |((σ : ℂ) * w).im| ≤ t ∧ -1 ≤ ((σ : ℂ) * w).re ∧
      ((σ : ℂ) * w).re ≤ 1 ∧ ‖(σ : ℂ) * w‖ ≤ ‖w‖ := by
    intro σ hσ
    have hσ0 := hσ.1
    have hσ1 := hσ.2
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.mul_re, sub_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg hσ0]; nlinarith [abs_nonneg w.im]
    · have := abs_le.mp hre; nlinarith
    · have := abs_le.mp hre; nlinarith
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0]
      exact mul_le_of_le_one_left (norm_nonneg _) hσ1
  have hderiv : ∀ σ ∈ Icc (0 : ℝ) 1, HasDerivAt f
      (w * (critConductorQuot t ((σ : ℂ) * w) * critConductorSlope t ((σ : ℂ) * w))) σ := by
    intro σ hσ
    have hlin : HasDerivAt (fun σ : ℝ => (σ : ℂ) * w) w σ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := σ)).mul_const w
    have hP := hasDerivAt_critConductorQuot ht0 (hseg σ hσ).1
    have h2 := HasDerivAt.comp σ hP hlin
    refine (h2.sub_const 1).congr_deriv ?_
    ring
  have hcont : ContinuousOn f (Icc 0 1) := fun σ hσ => (hderiv σ hσ).continuousAt.continuousWithinAt
  have hbound : ∀ σ ∈ Ico (0 : ℝ) 1,
      ‖w * (critConductorQuot t ((σ : ℂ) * w) * critConductorSlope t ((σ : ℂ) * w))‖ ≤
        ε * ‖f σ‖ + ε := by
    intro σ hσ
    have hσ' : σ ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hσ
    obtain ⟨him', hre₁, hre₂, hnorm⟩ := hseg σ hσ'
    have hs := norm_critConductorSlope_le ht hre₁ hre₂ him'
    have hs' : ‖critConductorSlope t ((σ : ℂ) * w)‖ ≤ 20 * ‖w‖ / t + 52 / t ^ 2 := by
      refine hs.trans ?_
      gcongr
    have hP : ‖critConductorQuot t ((σ : ℂ) * w)‖ ≤ ‖f σ‖ + 1 := by
      have : critConductorQuot t ((σ : ℂ) * w) = f σ + 1 := by simp [hf]
      rw [this]
      exact (norm_add_le _ _).trans (by simp)
    rw [norm_mul, norm_mul]
    calc ‖w‖ * (‖critConductorQuot t ((σ : ℂ) * w)‖ * ‖critConductorSlope t ((σ : ℂ) * w)‖)
        ≤ ‖w‖ * ((‖f σ‖ + 1) * (20 * ‖w‖ / t + 52 / t ^ 2)) := by
          gcongr
    _ = ε * ‖f σ‖ + ε := by rw [hε]; ring
  have hf0 : ‖f 0‖ ≤ 0 := by simp [hf, critConductorQuot_zero]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun σ hσ => (hderiv σ (Ico_subset_Icc_self hσ)).hasDerivWithinAt) hf0 hbound 1
    ⟨zero_le_one, le_rfl⟩
  have hf1 : f 1 = critConductorQuot t w - 1 := by simp [hf]
  rw [hf1, sub_zero] at hg
  refine hg.trans (le_of_eq ?_)
  rcases eq_or_lt_of_le hε0 with h0 | hpos
  · rw [← h0]
    simp [gronwallBound]
  · rw [gronwallBound_of_K_ne_0 hpos.ne']
    field_simp
    ring

/-- **Stirling for the critical carrier.** -/
theorem norm_critCarrier_neg_sub_conductorPow_le {t : ℝ} (ht : 4 ≤ t) {w : ℂ}
    (hre : |w.re| ≤ 1) (him : 2 * |w.im| ≤ t) :
    ‖critCarrier t (-w) - ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * w)‖ ≤
      (t / (2 * Real.pi)) ^ (2 * w.re) *
        (Real.exp (‖w‖ * (20 * ‖w‖ / t + 52 / t ^ 2)) - 1) := by
  have ht0 : 0 < t := by linarith
  have hL : (0 : ℝ) < t / (2 * Real.pi) := by positivity
  rw [critCarrier_neg_eq_quot_mul ht0, ← sub_one_mul, norm_mul, mul_comm,
    Complex.norm_cpow_eq_rpow_re_of_pos hL]
  have hre2 : (2 * w).re = 2 * w.re := by simp
  rw [hre2]
  exact mul_le_mul_of_nonneg_left (norm_critConductorQuot_sub_one_le ht hre him)
    (Real.rpow_nonneg hL.le _)

end RHTower.ZetaNotch
