import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour

/-!
# `ψ(y) ≤ log y` on the positive reals

The recurrence `ψ(z+1) = ψ(z) + 1/z` moves the argument to `y + n`, where the first-order
asymptotic `‖ψ(z) − log z‖ ≤ 3/‖z‖` applies, and the harmonic sum that is subtracted dominates the
logarithm it has to beat:

```text
Re ψ(y) = Re ψ(y+n) − Σ_{k<n} 1/(y+k) ≤ log(y+n) + 3/(y+n) − (log(y+n) − log y) = log y + 3/(y+n).
```

Letting `n → ∞` gives `Re ψ(y) ≤ log y` for every `y > 0`.  The bound is sharp in order: the true
asymptotic is `log y − 1/(2y)`.
-/

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The `n`-fold digamma recurrence, in real parts. -/
theorem re_digamma_shift {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (Complex.digamma ((y : ℝ) : ℂ)).re
      = (Complex.digamma (((y + (n : ℝ)) : ℝ) : ℂ)).re
        - ∑ k ∈ Finset.range n, 1 / (y + (k : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyn : (0 : ℝ) < y + (n : ℝ) := by positivity
    have hne : ∀ m : ℕ, (((y + (n : ℝ)) : ℝ) : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have hc := congrArg Complex.re hm
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hc
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hrec := Complex.digamma_apply_add_one ((((y + (n : ℝ)) : ℝ) : ℂ)) hne
    have hcast : (((y + (n : ℝ)) : ℝ) : ℂ) + 1 = (((y + ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hrec
    have hinv : ((((y + (n : ℝ)) : ℝ) : ℂ))⁻¹.re = 1 / (y + (n : ℝ)) := by
      rw [Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      have hne0 : y + (n : ℝ) ≠ 0 := hyn.ne'
      field_simp
      ring
    have hre := congrArg Complex.re hrec
    rw [Complex.add_re, hinv] at hre
    rw [Finset.sum_range_succ, ih, hre]
    ring

/-- The harmonic sum dominates the logarithm it telescopes against. -/
theorem log_sub_log_le_harmonic {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.log (y + (n : ℝ)) - Real.log y ≤ ∑ k ∈ Finset.range n, 1 / (y + (k : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyn : (0 : ℝ) < y + (n : ℝ) := by positivity
    have hstep : Real.log (y + ((n + 1 : ℕ) : ℝ)) - Real.log (y + (n : ℝ))
        ≤ 1 / (y + (n : ℝ)) := by
      have hcast : y + ((n + 1 : ℕ) : ℝ) = (y + (n : ℝ)) * (1 + 1 / (y + (n : ℝ))) := by
        field_simp
        push_cast
        ring
      rw [hcast, Real.log_mul hyn.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (y + (n : ℝ))) (by positivity)
      linarith
    rw [Finset.sum_range_succ]
    linarith [ih, hstep]

/-- **`Re ψ(y) ≤ log y` for every `y > 0`.** -/
theorem re_digamma_le_log {y : ℝ} (hy : 0 < y) :
    (Complex.digamma ((y : ℝ) : ℂ)).re ≤ Real.log y := by
  have hstep : ∀ n : ℕ, 2 ≤ (y + (n : ℝ)) →
      (Complex.digamma ((y : ℝ) : ℂ)).re ≤ Real.log y + 3 / (y + (n : ℝ)) := by
    intro n hn
    have hyn : (0 : ℝ) < y + (n : ℝ) := by linarith
    have hznorm : ‖(((y + (n : ℝ)) : ℝ) : ℂ)‖ = y + (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyn]
    have hstir := norm_digamma_sub_log_le_of_re_pos
      (z := (((y + (n : ℝ)) : ℝ) : ℂ)) (by simp; linarith) (by rw [hznorm]; exact hn)
    rw [hznorm] at hstir
    have hlogre : (Complex.log ((((y + (n : ℝ)) : ℝ) : ℂ))).re = Real.log (y + (n : ℝ)) := by
      rw [Complex.log_re, hznorm]
    have hsh : (Complex.digamma ((((y + (n : ℝ)) : ℝ) : ℂ))).re
        ≤ Real.log (y + (n : ℝ)) + 3 / (y + (n : ℝ)) := by
      have hle : (Complex.digamma ((((y + (n : ℝ)) : ℝ) : ℂ))
          - Complex.log ((((y + (n : ℝ)) : ℝ) : ℂ))).re ≤ 3 / (y + (n : ℝ)) :=
        le_trans (Complex.re_le_norm _) hstir
      rw [Complex.sub_re, hlogre] at hle
      linarith
    have hrec := re_digamma_shift hy n
    have hharm := log_sub_log_le_harmonic hy n
    linarith [hsh, hrec, hharm]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 - y) (3 / ε))
  have hn1 : (2 : ℝ) - y < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn2 : (3 : ℝ) / ε < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hyn : (2 : ℝ) ≤ y + (n : ℝ) := by linarith
  have hyn0 : (0 : ℝ) < y + (n : ℝ) := by linarith
  have hsmall : 3 / (y + (n : ℝ)) ≤ ε := by
    rw [div_le_iff₀ hyn0]
    have h3 : (3 : ℝ) < ε * (n : ℝ) := by
      rw [div_lt_iff₀ hε] at hn2
      linarith
    nlinarith [hε, hy]
  linarith [hstep n hyn, hsmall]

/-- `log (π/2) ≥ 2/5`, from `exp (1/10) ≤ 10/9`. -/
theorem two_fifths_le_log_pi_sub_log_two : (2 : ℝ) / 5 ≤ Real.log Real.pi - Real.log 2 := by
  have h1 : Real.exp (1 / 10) ≤ 10 / 9 := by
    have h := Real.add_one_le_exp (-(1 / 10 : ℝ))
    have hexp : Real.exp (-(1 / 10 : ℝ)) = (Real.exp (1 / 10))⁻¹ := by
      rw [Real.exp_neg]
    rw [hexp] at h
    have hpos : (0 : ℝ) < Real.exp (1 / 10) := Real.exp_pos _
    rw [le_inv_comm₀ (by norm_num) hpos] at h
    calc Real.exp (1 / 10) ≤ (-(1 / 10) + 1)⁻¹ := h
      _ = 10 / 9 := by norm_num
  have h4 : Real.exp (2 / 5) ≤ (10 / 9 : ℝ) ^ (4 : ℕ) := by
    have hpow : Real.exp (2 / 5) = Real.exp (1 / 10) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hpow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 4
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hlt : Real.exp (2 / 5) < Real.pi / 2 := by
    have hnum : ((10 : ℝ) / 9) ^ (4 : ℕ) < 3.14 / 2 := by norm_num
    linarith [h4, hnum, hpi]
  have hlog := Real.log_lt_log (Real.exp_pos (2 / 5)) hlt
  rw [Real.log_exp, Real.log_div (by positivity) (by norm_num)] at hlog
  linarith

/-- **The pole bound with a negative constant.** -/
theorem neg_re_logDeriv_riemannZeta_real_le_neg {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + -(1 / 5) := by
  rw [Sieve.neg_div_re_eq_neg_logDeriv_re]
  set s : ℂ := ((σ : ℝ) : ℂ) with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
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
  have hA : (1 / s).re = 1 / σ := by
    rw [hsdef, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have hσne : σ ≠ 0 := by linarith
    field_simp
    ring
  have hB : (1 / (s - 1)).re = 1 / (σ - 1) := by
    have hc : s - 1 = (((σ - 1 : ℝ)) : ℂ) := by rw [hsdef]; push_cast; ring
    rw [hc, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have hσ1ne : σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  -- one shift of the digamma argument
  have hhalf : s / 2 = (((σ / 2 : ℝ)) : ℂ) := by rw [hsdef]; push_cast; ring
  have hx0 : (0 : ℝ) < σ / 2 := by linarith
  have hne : ∀ m : ℕ, (((σ / 2 : ℝ)) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hc := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hc
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one ((((σ / 2 : ℝ)) : ℂ)) hne
  have hcast : (((σ / 2 : ℝ)) : ℂ) + 1 = (((σ / 2 + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast] at hrec
  have hinv : ((((σ / 2 : ℝ)) : ℂ))⁻¹.re = 2 / σ := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have hσne : σ ≠ 0 := by linarith
    field_simp
    ring
  have hrecre := congrArg Complex.re hrec
  rw [Complex.add_re, hinv] at hrecre
  have hshiftbound : (Complex.digamma ((((σ / 2 + 1 : ℝ)) : ℂ))).re ≤ Real.log 2 := by
    refine le_trans (re_digamma_le_log (by linarith)) ?_
    exact Real.log_le_log (by linarith) (by linarith)
  have hGre : (logDeriv Complex.Gammaℝ s).re
      ≤ (Real.log 2 - 2 / σ) / 2 - Real.log Real.pi / 2 := by
    rw [hG]
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
    rw [hhalf]
    linarith [hrecre, hshiftbound]
  rw [hA, hB]
  have hkey := two_fifths_le_log_pi_sub_log_two
  have hGre' : (logDeriv Complex.Gammaℝ s).re
      ≤ Real.log 2 / 2 - 1 / σ - Real.log Real.pi / 2 := by
    have h2 : (Real.log 2 - 2 / σ) / 2 = Real.log 2 / 2 - 1 / σ := by
      field_simp
    rw [h2] at hGre
    exact hGre
  linarith [hxi, hGre', hkey]

/-- **The zero-free region of width `1/(58 log γ)`, valid from ordinate `4`.** -/
theorem xiZeroCopy_zero_free_fiftyEight {q : XiZeroCopy} (hq : 4 ≤ (q.1 : ℂ).im) :
    (q.1 : ℂ).re ≤ 1 - 1 / 58 / Real.log ((q.1 : ℂ).im) := by
  have hA : ∀ u : ℝ, 1 < u → u ≤ 2 →
      (-deriv riemannZeta (u : ℂ) / riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + -(1 / 5) :=
    fun u h1 h2 => neg_re_logDeriv_riemannZeta_real_le_neg h1 h2
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
  rw [hL4] at hLge
  have hLpos : (0 : ℝ) < Real.log γ := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log γ := by linarith
  by_contra hcon
  rw [not_le] at hcon
  set σ : ℝ := 1 + 1 / (9 * Real.log γ) with hσdef
  have hδpos : (0 : ℝ) < 1 / (9 * Real.log γ) := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have : 1 / (9 * Real.log γ) ≤ 1 / 9 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q
  have hsb0 : (0 : ℝ) < σ - β := by linarith
  have hdlvp := dlvp_half hA hσ1 hσ2 q hq
  rw [← hβdef, ← hγdef] at hdlvp
  have hpole : (3 : ℝ) / (σ - 1) = 27 * Real.log γ := by
    have hs1 : σ - 1 = 1 / (9 * Real.log γ) := by rw [hσdef]; ring
    rw [hs1]
    field_simp
    ring
  have hcon' : 1 - 1 / (58 * Real.log γ) < β := by
    rw [div_div] at hcon
    convert hcon using 3
  have hsb : σ - β < 67 / (522 * Real.log γ) := by
    have hsplit : (1 : ℝ) / (9 * Real.log γ) + 1 / (58 * Real.log γ)
        = 67 / (522 * Real.log γ) := by
      field_simp
      norm_num
    rw [hσdef]
    linarith [hcon', hsplit]
  have hlow : 2088 * Real.log γ / 67 < 4 / (σ - β) := by
    rw [lt_div_iff₀ hsb0]
    have hpos : (0 : ℝ) < 2088 * Real.log γ / 67 := by positivity
    have hmul := mul_lt_mul_of_pos_left hsb hpos
    have hval : 2088 * Real.log γ / 67 * (67 / (522 * Real.log γ)) = 4 := by
      field_simp
      ring
    linarith [hmul, hval]
  have hfinal : 2088 * Real.log γ / 67
      < 27 * Real.log γ + 5 / 2 * Real.log γ + dlvpHalfConstant (-(1 / 5)) := by
    rw [← hpole]
    linarith [hlow, hdlvp]
  unfold dlvpHalfConstant at hfinal
  linarith [hfinal, hLge, hlog2, hlog2']

end

end RHTower
