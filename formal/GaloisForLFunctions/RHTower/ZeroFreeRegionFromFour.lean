import GaloisForLFunctions.RHTower.ZetaPoleBoundExplicit

/-!
# The archimedean factor: a real-part bound with coefficient one half

`norm_logDeriv_Gammaℝ_le` bounds the modulus of `Γ_ℝ'/Γ_ℝ` by `log t + C`.  Only the real part is
ever used, and it is half as large: with `z = s/2` the first-order asymptotic
`‖ψ(z) − log z‖ ≤ 3/‖z‖` gives `Re ψ(z) ≤ log ‖z‖ + 3/‖z‖`, and on `1 ≤ σ ≤ 2`, `t ≥ 4` one has
`2 ≤ ‖z‖ ≤ t`, so

```text
Re (Γ_ℝ'/Γ_ℝ)(σ + it) = Re ψ(s/2)/2 − (log π)/2 ≤ (log t)/2 + 3/4 − 1/2 .
```

Halving the coefficient of `log t` halves the coefficient in the de la Vallée Poussin inequality,
from `5` to `5/2`.
-/

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **The archimedean real-part bound.** -/
theorem re_logDeriv_Gammaℝ_le_half_log {σ t : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t) :
    (logDeriv Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      ≤ Real.log t / 2 + 1 / 4 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have ht0 : (0 : ℝ) < t := by linarith
  have hhalfre : (s / 2).re = σ / 2 := by rw [Complex.div_ofNat_re, hsre]
  have hnsq : Complex.normSq (s / 2) = (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) / 4 := by
    rw [Complex.normSq_apply, Complex.div_ofNat_re, Complex.div_ofNat_im, hsre, hsim]
    ring
  have hnorm2 : ‖s / 2‖ ^ (2 : ℕ) = (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, hnsq]
  have hnn : (0 : ℝ) ≤ ‖s / 2‖ := norm_nonneg _
  have hge2 : (2 : ℝ) ≤ ‖s / 2‖ := by nlinarith [hnorm2, hnn, ht, hσ1]
  have hlet : ‖s / 2‖ ≤ t := by nlinarith [hnorm2, hnn, ht, hσ2, ht0]
  have hpos : (0 : ℝ) < ‖s / 2‖ := by linarith
  -- the first-order asymptotic
  have hstir := norm_digamma_sub_log_le_of_re_pos (z := s / 2)
    (by rw [hhalfre]; linarith) hge2
  have hlogre : (Complex.log (s / 2)).re = Real.log ‖s / 2‖ := Complex.log_re _
  have hpsi : (Complex.digamma (s / 2)).re ≤ Real.log ‖s / 2‖ + 3 / ‖s / 2‖ := by
    have hle : (Complex.digamma (s / 2) - Complex.log (s / 2)).re ≤ 3 / ‖s / 2‖ :=
      le_trans (Complex.re_le_norm _) hstir
    rw [Complex.sub_re, hlogre] at hle
    linarith
  have hlogle : Real.log ‖s / 2‖ ≤ Real.log t := Real.log_le_log hpos hlet
  have hthree : (3 : ℝ) / ‖s / 2‖ ≤ 3 / 2 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  -- the `log π` term
  have hpi : (1 : ℝ) ≤ Real.log Real.pi := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h3 : Real.exp 1 < Real.pi := lt_trans he Real.pi_gt_three
    have h := Real.log_lt_log (Real.exp_pos 1) h3
    rw [Real.log_exp] at h
    exact h.le
  have hG : logDeriv Complex.Gammaℝ s
      = Complex.digamma (s / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 :=
    logDeriv_Gammaℝ_digamma (by rw [hsre]; linarith)
  rw [hG]
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  linarith [hpsi, hlogle, hthree, hpi]

/-- **The Landau bound with coefficient one half.** -/
theorem neg_re_logDeriv_riemannZeta_le_half {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      ≤ Real.log t / 2 + 1 / 2 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have h1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hxi : 0 < (logDeriv xi s).re := re_logDeriv_xi_pos_of_one_le_re h1.le
  have hfour := logDeriv_xi_fourFactor h1
  have hG : logDeriv Complex.Gammaℝ s
      = Complex.digamma (s / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 :=
    logDeriv_Gammaℝ_digamma (by rw [hsre]; linarith)
  have hzeta : logDeriv riemannZeta s
      = logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
    rw [hG, hfour]; ring
  rw [hzeta]
  have hre : (logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s).re
      = (logDeriv xi s).re - (1 / s).re - (1 / (s - 1)).re
        - (logDeriv Complex.Gammaℝ s).re := by
    simp only [Complex.sub_re]
  rw [hre]
  have hnormSq : Complex.normSq s = σ ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hsre, hsim]; ring
  have hnormSq1 : Complex.normSq (s - 1) = (σ - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre, hsim]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hA : (1 / s).re ≤ 2 / 17 := by
    rw [one_div, Complex.inv_re, hsre, hnormSq]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hB : (1 / (s - 1)).re ≤ 1 / 16 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, hsre, hnormSq1]
    simp only [Complex.one_re]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hC : (logDeriv Complex.Gammaℝ s).re ≤ Real.log t / 2 + 1 / 4 := by
    rw [hsdef]
    exact re_logDeriv_Gammaℝ_le_half_log hσ1.le hσ2 ht
  linarith [hxi, hA, hB, hC]

/-- **The Landau bound with coefficient one half, with the zero retained.** -/
theorem neg_re_logDeriv_riemannZeta_le_half_sub {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (ht : 4 ≤ t) (q₀ : XiZeroCopy) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      ≤ Real.log t / 2 + 1 / 2
        - (σ - (q₀.1 : ℂ).re)
            / Complex.normSq (((σ : ℂ) + (t : ℂ) * Complex.I) - (q₀.1 : ℂ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have h1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hxine : xi s ≠ 0 := xi_ne_zero_of_one_le_re h1.le
  have hres := resolventTerm_le_re_logDeriv_xi hxine h1.le q₀
  rw [hsre] at hres
  have hfour := logDeriv_xi_fourFactor h1
  have hG : logDeriv Complex.Gammaℝ s
      = Complex.digamma (s / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 :=
    logDeriv_Gammaℝ_digamma (by rw [hsre]; linarith)
  have hzeta : logDeriv riemannZeta s
      = logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
    rw [hG, hfour]; ring
  rw [hzeta]
  have hre : (logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s).re
      = (logDeriv xi s).re - (1 / s).re - (1 / (s - 1)).re
        - (logDeriv Complex.Gammaℝ s).re := by
    simp only [Complex.sub_re]
  rw [hre]
  have hnormSq : Complex.normSq s = σ ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hsre, hsim]; ring
  have hnormSq1 : Complex.normSq (s - 1) = (σ - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre, hsim]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hA : (1 / s).re ≤ 2 / 17 := by
    rw [one_div, Complex.inv_re, hsre, hnormSq]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hB : (1 / (s - 1)).re ≤ 1 / 16 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, hsre, hnormSq1]
    simp only [Complex.one_re]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hC : (logDeriv Complex.Gammaℝ s).re ≤ Real.log t / 2 + 1 / 4 := by
    rw [hsdef]
    exact re_logDeriv_Gammaℝ_le_half_log hσ1.le hσ2 ht
  linarith [hres, hA, hB, hC]

/-- The de la Vallée Poussin constant at coefficient one half. -/
def dlvpHalfConstant (A : ℝ) : ℝ := 3 * A + 5 / 2 + Real.log 2 / 2

/-- **The de la Vallée Poussin inequality with coefficient `5/2`.** -/
theorem dlvp_half {A σ : ℝ}
    (hA : ∀ u : ℝ, 1 < u → u ≤ 2 →
      (-deriv riemannZeta (u : ℂ) / riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + A)
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (q₀ : XiZeroCopy) (hγ : 4 ≤ (q₀.1 : ℂ).im) :
    4 / (σ - (q₀.1 : ℂ).re)
      ≤ 3 / (σ - 1) + 5 / 2 * Real.log ((q₀.1 : ℂ).im) + dlvpHalfConstant A := by
  set β : ℝ := (q₀.1 : ℂ).re with hβ
  set γ : ℝ := (q₀.1 : ℂ).im with hγdef
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q₀
  have hσβ : 0 < σ - β := by linarith
  have hmain := neg_re_logDeriv_riemannZeta_le_half_sub hσ1 hσ2 hγ q₀
  have hnormSq : Complex.normSq (((σ : ℂ) + (γ : ℂ) * Complex.I) - (q₀.1 : ℂ))
      = (σ - β) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, ← hβ, ← hγdef]
    ring
  rw [hnormSq] at hmain
  have hdiv : (σ - β) / (σ - β) ^ (2 : ℕ) = 1 / (σ - β) := by
    rw [pow_two]; field_simp
  rw [hdiv] at hmain
  have hB0 := neg_re_logDeriv_riemannZeta_le_half (σ := σ) (t := 2 * γ) hσ1 hσ2 (by linarith)
  have hcast : ((2 * γ : ℝ) : ℂ) = (2 * γ : ℂ) := by push_cast; ring
  rw [hcast] at hB0
  have hconvB : (-deriv riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)
      / riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)).re
      ≤ Real.log (2 * γ) / 2 + 1 / 2 := by
    rw [Sieve.neg_div_re_eq_neg_logDeriv_re]
    exact hB0
  have hshift := Sieve.re_logDeriv_shift_le (σ := σ) (t := γ) hσ1 (hA σ hσ1 hσ2) hconvB
  rw [Sieve.neg_div_re_eq_neg_logDeriv_re] at hshift
  have hlog2 : Real.log (2 * γ) = Real.log 2 + Real.log γ := by
    rw [Real.log_mul (by norm_num) hγ0.ne']
  rw [hlog2] at hshift
  have hchain : 1 / (σ - β)
      ≤ Real.log γ / 2 + 1 / 2
        + (3 * (1 / (σ - 1) + A)
            + ((Real.log 2 + Real.log γ) / 2 + 1 / 2)) / 4 := by
    linarith [hmain, hshift]
  have hgoal4 : (4 : ℝ) / (σ - β) = 4 * (1 / (σ - β)) := by ring
  have hgoal3 : (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
  rw [hgoal4, hgoal3]
  unfold dlvpHalfConstant
  linarith [hchain]

/-- **The zero-free region of width `1/(100 log γ)`, valid from ordinate `4`.** -/
theorem xiZeroCopy_zero_free_from_four {q : XiZeroCopy} (hq : 4 ≤ (q.1 : ℂ).im) :
    (q.1 : ℂ).re ≤ 1 - 1 / 100 / Real.log ((q.1 : ℂ).im) := by
  have hA : ∀ u : ℝ, 1 < u → u ≤ 2 →
      (-deriv riemannZeta (u : ℂ) / riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + 1 :=
    fun u h1 h2 => neg_re_logDeriv_riemannZeta_real_le h1 h2
  set β : ℝ := (q.1 : ℂ).re with hβdef
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hL4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hLge : Real.log 4 ≤ Real.log γ := Real.log_le_log (by norm_num) hq
  have hLpos : (0 : ℝ) < Real.log γ := by
    rw [hL4] at hLge
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set σ : ℝ := 1 + 1 / (16 * Real.log γ) with hσdef
  have hδpos : (0 : ℝ) < 1 / (16 * Real.log γ) := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hL1 : (1 : ℝ) ≤ Real.log γ := by rw [hL4] at hLge; linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have : 1 / (16 * Real.log γ) ≤ 1 / 16 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q
  have hsb0 : (0 : ℝ) < σ - β := by linarith
  have hdlvp := dlvp_half hA hσ1 hσ2 q hq
  rw [← hβdef, ← hγdef] at hdlvp
  have hpole : (3 : ℝ) / (σ - 1) = 48 * Real.log γ := by
    have hs1 : σ - 1 = 1 / (16 * Real.log γ) := by rw [hσdef]; ring
    rw [hs1]
    field_simp
    ring
  have hcon' : 1 - 1 / (100 * Real.log γ) < β := by
    rw [div_div] at hcon
    convert hcon using 3
  have hsb : σ - β < 29 / (400 * Real.log γ) := by
    have hsplit : (1 : ℝ) / (16 * Real.log γ) + 1 / (100 * Real.log γ)
        = 29 / (400 * Real.log γ) := by
      field_simp
      norm_num
    rw [hσdef]
    linarith [hcon', hsplit]
  have hlow : 1600 * Real.log γ / 29 < 4 / (σ - β) := by
    rw [lt_div_iff₀ hsb0]
    have hpos : (0 : ℝ) < 1600 * Real.log γ / 29 := by positivity
    have hmul := mul_lt_mul_of_pos_left hsb hpos
    have hval : 1600 * Real.log γ / 29 * (29 / (400 * Real.log γ)) = 4 := by
      field_simp
      ring
    linarith [hmul, hval]
  have hfinal : 1600 * Real.log γ / 29
      < 48 * Real.log γ + 5 / 2 * Real.log γ + dlvpHalfConstant 1 := by
    rw [← hpole]
    linarith [hlow, hdlvp]
  unfold dlvpHalfConstant at hfinal
  rw [hL4] at hLge
  linarith [hfinal, hLge, hlog2, hlog2']

end

end RHTower
