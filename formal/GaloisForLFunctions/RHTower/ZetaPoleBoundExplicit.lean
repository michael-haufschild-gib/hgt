import GaloisForLFunctions.RHTower.ZeroFreeRegionSharp
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# An explicit pole bound

`Sieve.exists_pole_bound` is a compactness argument, so its constant is not explicit.  The
four-factor identity at a real point gives one directly:

```text
−ζ'/ζ(σ) ≤ 1/σ + 1/(σ−1) + Re ψ(σ/2)/2 − (log π)/2 ,
```

because `Re (ξ'/ξ)` is positive right of the strip.  On `1 < σ ≤ 2` the argument `σ/2` lies in
`(1/2, 1]`, where two steps of `ψ(z+1) = ψ(z) + 1/z` and the first-order asymptotic
`‖ψ(z) − log z‖ ≤ 3/‖z‖` give `Re ψ(σ/2) ≤ log 3 − 3/10`.  Since `3 ≤ π`, the archimedean term is
negative and `A = 1` works.
-/

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **The digamma bound on `(1/2, 1]`.** -/
theorem re_digamma_ofReal_le {x : ℝ} (hx0 : 1 / 2 < x) (hx1 : x ≤ 1) :
    (Complex.digamma ((x : ℝ) : ℂ)).re ≤ Real.log 3 - 3 / 10 := by
  have hx0' : (0 : ℝ) < x := by linarith
  have hne : ∀ m : ℕ, ((x : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hne1 : ∀ m : ℕ, ((x : ℝ) : ℂ) + 1 ≠ -(m : ℂ) := by
    intro m hm
    have hc := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hc
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h1 := Complex.digamma_apply_add_one ((x : ℝ) : ℂ) hne
  have h2 := Complex.digamma_apply_add_one (((x : ℝ) : ℂ) + 1) hne1
  -- the shifted point
  have hcast : ((x : ℝ) : ℂ) + 1 + 1 = (((x + 2 : ℝ)) : ℂ) := by push_cast; ring
  have hzre : (((x + 2 : ℝ)) : ℂ).re = x + 2 := by simp
  have hznorm : ‖(((x + 2 : ℝ)) : ℂ)‖ = x + 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hstir := norm_digamma_sub_log_le_of_re_pos
    (z := (((x + 2 : ℝ)) : ℂ)) (by rw [hzre]; linarith) (by rw [hznorm]; linarith)
  rw [hznorm] at hstir
  -- real part of the shifted digamma
  have hlogre : (Complex.log (((x + 2 : ℝ)) : ℂ)).re = Real.log (x + 2) := by
    rw [Complex.log_re, hznorm]
  have hshift : (Complex.digamma (((x + 2 : ℝ)) : ℂ)).re ≤ Real.log (x + 2) + 3 / (x + 2) := by
    have hle : (Complex.digamma (((x + 2 : ℝ)) : ℂ) - Complex.log (((x + 2 : ℝ)) : ℂ)).re
        ≤ 3 / (x + 2) := le_trans (Complex.re_le_norm _) hstir
    rw [Complex.sub_re, hlogre] at hle
    linarith
  -- unwind the two recurrences
  have hinv0 : (((x : ℝ) : ℂ))⁻¹.re = 1 / x := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  have hinv1 : ((((x : ℝ) : ℂ) + 1))⁻¹.re = 1 / (x + 1) := by
    have hc : ((x : ℝ) : ℂ) + 1 = (((x + 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hc, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have hx1ne : x + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hcast] at h2
  have hre1 := congrArg Complex.re h1
  have hre2 := congrArg Complex.re h2
  rw [Complex.add_re, hinv0] at hre1
  rw [Complex.add_re, hinv1] at hre2
  -- numeric bounds (placeholder)
  have hb1 : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0']; linarith
  have hb2 : (1 : ℝ) / 2 ≤ 1 / (x + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hb3 : (3 : ℝ) / (x + 2) ≤ 6 / 5 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hb4 : Real.log (x + 2) ≤ Real.log 3 :=
    Real.log_le_log (by linarith) (by linarith)
  -- h1 : digamma (x+1) = digamma x + 1/x, h2 : digamma (x+2) = digamma (x+1) + 1/(x+1)
  linarith [hshift, hre1, hre2, hb1, hb2, hb3, hb4]

/-- **The explicit pole bound.** -/
theorem neg_re_logDeriv_riemannZeta_real_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  rw [Sieve.neg_div_re_eq_neg_logDeriv_re]
  set s : ℂ := ((σ : ℝ) : ℂ) with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have h1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hxine : xi s ≠ 0 := xi_ne_zero_of_one_le_re h1.le
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
  -- the elementary real parts
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
  -- the archimedean part
  have hhalf : s / 2 = (((σ / 2 : ℝ)) : ℂ) := by rw [hsdef]; push_cast; ring
  have hdig : (Complex.digamma (s / 2)).re ≤ Real.log 3 - 3 / 10 := by
    rw [hhalf]
    exact re_digamma_ofReal_le (by linarith) (by linarith)
  have hGre : (logDeriv Complex.Gammaℝ s).re
      ≤ (Real.log 3 - 3 / 10) / 2 - Real.log Real.pi / 2 := by
    rw [hG]
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
    linarith [hdig]
  have hpi : Real.log 3 ≤ Real.log Real.pi :=
    Real.log_le_log (by norm_num) (le_of_lt Real.pi_gt_three)
  have hsig : 1 / σ ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  linarith [hxi, hA, hB, hGre, hpi, hsig]

/-- The sharp de la Vallée Poussin constant at the explicit pole bound is at least `44`. -/
theorem forty_four_le_dlvpSharpConstant_one : (44 : ℝ) ≤ dlvpSharpConstant 1 := by
  unfold dlvpSharpConstant landauSharpConstant digammaVerticalLogConstant
  have hpi := Real.pi_gt_three
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- **The zero-free region with an explicit threshold.**  Every zero copy of `ξ` with ordinate at
least `exp (29 K / 63)`, `K = dlvpSharpConstant 1 = 14 + 10π + 6 log 2`, has real part at most
`1 − 1/(100 log γ)`. -/
theorem xiZeroCopy_zero_free_explicit {q : XiZeroCopy}
    (hq : Real.exp (29 * dlvpSharpConstant 1 / 63) ≤ (q.1 : ℂ).im) :
    (q.1 : ℂ).re ≤ 1 - 1 / 100 / Real.log ((q.1 : ℂ).im) := by
  have hA : ∀ u : ℝ, 1 < u → u ≤ 2 →
      (-deriv riemannZeta (u : ℂ) / riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + 1 :=
    fun u h1 h2 => neg_re_logDeriv_riemannZeta_real_le h1 h2
  set β : ℝ := (q.1 : ℂ).re with hβdef
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  set K : ℝ := dlvpSharpConstant 1 with hKdef
  have hK44 : (44 : ℝ) ≤ K := forty_four_le_dlvpSharpConstant_one
  have hexp2 : Real.exp 2 ≤ Real.exp (29 * K / 63) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h4exp : (4 : ℝ) ≤ Real.exp 2 := by
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hsq : Real.exp 1 ^ (2 : ℕ) = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [he, hsq, Real.exp_pos (1 : ℝ)]
  have hγ4 : (4 : ℝ) ≤ γ := le_trans (le_trans h4exp hexp2) hq
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log γ := by
    have he : Real.exp 1 < 4 := by
      have := Real.exp_one_lt_d9
      linarith
    have h : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) he
    rw [Real.log_exp] at h
    exact le_trans h.le (Real.log_le_log (by norm_num) hγ4)
  have hLpos : (0 : ℝ) < Real.log γ := by linarith
  have hLbig : 29 * K / 63 ≤ Real.log γ := by
    have h := Real.log_le_log (Real.exp_pos (29 * K / 63)) hq
    rwa [Real.log_exp] at h
  by_contra hcon
  rw [not_le] at hcon
  set σ : ℝ := 1 + 1 / (16 * Real.log γ) with hσdef
  have hδpos : (0 : ℝ) < 1 / (16 * Real.log γ) := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have : 1 / (16 * Real.log γ) ≤ 1 / 16 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q
  have hsb0 : (0 : ℝ) < σ - β := by linarith
  have hdlvp := dlvp_sharp hA hσ1 hσ2 q hγ4
  rw [← hβdef, ← hγdef, ← hKdef] at hdlvp
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
  have hfinal : 1600 * Real.log γ / 29 < 48 * Real.log γ + 5 * Real.log γ + K := by
    rw [← hpole]
    linarith [hlow, hdlvp]
  linarith [hfinal, hLbig]

end

end RHTower
