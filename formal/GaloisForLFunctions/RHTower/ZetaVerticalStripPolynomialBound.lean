import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound

/-!
# Polynomial growth of `ζ` on a left vertical strip

To the right of the critical strip the Euler--Maclaurin bound already gives `‖ζ(s)‖ = O(‖s‖^{1/2})`
away from the pole.  The functional equation

```text
ζ(1-s) = 2 (2π)^{-s} Γ(s) cos(π s / 2) ζ(s)
```

carries that bound to every abscissa on the left: the cosine grows like `e^{π|t|/2}`, the Gamma
factor decays like `e^{-π|t|/2}` uniformly on the reflected strip, and the two exponentials cancel,
leaving polynomial growth.  One constant and one exponent then serve the whole strip
`-M ≤ Re s ≤ 3/2` above unit height — the uniformity a rectangle's horizontal side needs.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Euler--Maclaurin bound in linear form: on `Re s ≥ 1/2` and unit height, with the abscissa
bounded by `B`, zeta grows at most linearly in the height. -/
theorem norm_riemannZeta_le_linear_of_re_ge_half {B σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hB : |σ| ≤ B)
    (ht : 1 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 5 * Real.sqrt (B + 3) * |t| := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg σ) hB
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by rw [hs]; simp
  have him : s.im = t := by rw [hs]; simp
  have hsep : (1 : ℝ) ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have h2 : (s - 1).im = t := by rw [Complex.sub_im, him]; simp
    rw [h2] at h1
    exact le_trans ht h1
  have hbase := norm_riemannZeta_le_sqrt_norm_add_two_half (s := s) (by rw [hre]; exact hσ)
    (d := 1) one_pos hsep
  have hnorm : ‖s‖ ≤ B + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him] at h
    linarith [hB]
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hstep : ‖s‖ + 2 ≤ (B + 3) * |t| := by nlinarith
  have hsqrt : Real.sqrt (‖s‖ + 2) ≤ Real.sqrt (B + 3) * |t| := by
    calc Real.sqrt (‖s‖ + 2) ≤ Real.sqrt ((B + 3) * |t|) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt (B + 3) * Real.sqrt |t| := Real.sqrt_mul (by positivity) _
      _ ≤ Real.sqrt (B + 3) * |t| := by
          have hle : Real.sqrt |t| ≤ |t| := by
            nlinarith [Real.sq_sqrt (le_of_lt htpos), Real.sqrt_nonneg |t|, ht]
          exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
  refine hbase.trans ?_
  have h5 : (2 : ℝ) + 1 / 1 + 2 = 5 := by norm_num
  rw [h5]
  calc (5 : ℝ) * Real.sqrt (‖s‖ + 2) ≤ 5 * (Real.sqrt (B + 3) * |t|) :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = 5 * Real.sqrt (B + 3) * |t| := by ring

/-- The cosine grows at most like the exponential of the imaginary part. -/
theorem norm_cos_le_exp_abs_im (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have hcos : Complex.cos w = (Complex.exp (w * I) + Complex.exp (-w * I)) / 2 := by
    rw [Complex.cos]
  have h1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have htri : ‖Complex.exp (w * I) + Complex.exp (-w * I)‖ ≤ 2 * Real.exp |w.im| := by
    refine (norm_add_le _ _).trans ?_
    rw [h1, h2]
    have hb1 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
    have hb2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
    linarith
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hcos, norm_div, hnorm2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Polynomial growth of `ζ` on a left vertical strip.**  One constant and one exponent serve
every abscissa with `|Re s| ≤ M`, above unit height. -/
theorem exists_bound_norm_riemannZeta_strip (M : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, |σ| ≤ M → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N := by
  classical
  set B : ℝ := |M| + 2 with hBdef
  set S : ℝ := 5 * Real.sqrt (B + 3) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  obtain ⟨CΓ, NΓ, hCΓ0, hCΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := (1 : ℝ) / 2) (by norm_num) (1 + |M|)
  refine ⟨2 * CΓ * S + S, NΓ + 1, by positivity, ?_⟩
  intro σ t hσabs ht
  have hσlow : -M ≤ σ := neg_le_of_abs_le hσabs
  have hσhigh : σ ≤ M := le_of_abs_le hσabs
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have htp : (0 : ℝ) ≤ |t| ^ (NΓ + 1) := by positivity
  have hMabs : |σ| ≤ B := by
    rw [hBdef]
    linarith [hσabs, le_abs_self M]
  rcases le_or_gt ((1 : ℝ) / 2) σ with hhalf | hhalf
  · have hbase := norm_riemannZeta_le_linear_of_re_ge_half hhalf hMabs ht
    rw [← hSdef] at hbase
    refine hbase.trans ?_
    have hpow : |t| ≤ |t| ^ (NΓ + 1) := by
      calc |t| = |t| ^ 1 := (pow_one _).symm
        _ ≤ |t| ^ (NΓ + 1) := pow_le_pow_right₀ ht (by omega)
    calc S * |t| ≤ S * |t| ^ (NΓ + 1) := mul_le_mul_of_nonneg_left hpow hS0
      _ ≤ (2 * CΓ * S + S) * |t| ^ (NΓ + 1) := by
          have hpos : (0 : ℝ) ≤ 2 * CΓ * S := mul_nonneg (by linarith) hS0
          nlinarith [htp, hpos]
  · set s : ℂ := ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I with hsdef
    have hre : s.re = 1 - σ := by rw [hsdef]; simp
    have him : s.im = -t := by rw [hsdef]; simp
    have habs_t : |(-t)| = |t| := abs_neg t
    have hup : 1 - σ ≤ 1 + |M| := by linarith [le_abs_self M, hσlow]
    have hne : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n hcon
      have hc := congrArg Complex.re hcon
      rw [hre] at hc
      simp only [Complex.neg_re, Complex.natCast_re] at hc
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hne1 : s ≠ 1 := by
      intro hcon
      have hc := congrArg Complex.im hcon
      rw [him] at hc
      simp only [Complex.one_im] at hc
      have htz : t = 0 := by linarith
      rw [htz] at ht
      norm_num at ht
    have hsub : 1 - s = (σ : ℂ) + (t : ℂ) * I := by rw [hsdef]; push_cast; ring
    have hfe := riemannZeta_one_sub hne hne1
    rw [hsub] at hfe
    rw [hfe]
    have hΓ : ‖Complex.Gamma s‖ ≤ CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)) := by
      have h := hCΓ (1 - σ) (-t) (by linarith) hup (by rw [habs_t]; exact ht)
      rw [habs_t] at h
      rw [hsdef]
      exact h
    have hcos : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ Real.exp (Real.pi * |t| / 2) := by
      have hrw : (Real.pi : ℂ) * s / 2 = ((Real.pi / 2 : ℝ) : ℂ) * s := by push_cast; ring
      have h := norm_cos_le_exp_abs_im ((Real.pi : ℂ) * s / 2)
      have him2 : ((Real.pi : ℂ) * s / 2).im = Real.pi / 2 * (-t) := by
        rw [hrw]; simp [Complex.mul_im, him]
      rw [him2] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2), habs_t]
      ring
    have hcpow : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ ≤ 1 := by
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos h2pi]
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
      · linarith [Real.two_le_pi]
      · simp only [Complex.neg_re, hre]
        linarith
    have hzeta : ‖riemannZeta s‖ ≤ S * |t| := by
      have habsre : |1 - σ| ≤ B := by
        rw [abs_of_pos (by linarith), hBdef]
        linarith [le_abs_self M, hσlow]
      have h := norm_riemannZeta_le_linear_of_re_ge_half (B := B) (σ := 1 - σ) (t := -t)
        (by linarith) habsre (by rw [habs_t]; exact ht)
      rw [habs_t, ← hSdef] at h
      rw [hsdef]
      exact h
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [hnorm2]
    have hexpcancel : Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t| / 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc 2 * ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ * ‖Complex.Gamma s‖
            * ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ * ‖riemannZeta s‖
        ≤ 2 * 1 * (CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)))
            * Real.exp (Real.pi * |t| / 2) * (S * |t|) := by
          have hB'0 : (0 : ℝ) ≤ CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)) :=
            mul_nonneg (mul_nonneg hCΓ0 (by positivity)) (Real.exp_pos _).le
          have h1 : (2 : ℝ) * ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ ≤ 2 * 1 :=
            mul_le_mul_of_nonneg_left hcpow (by norm_num)
          have h2 := mul_le_mul h1 hΓ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
          have h3 := mul_le_mul h2 hcos (norm_nonneg _)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * 1) hB'0)
          exact mul_le_mul h3 hzeta (norm_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * 1) hB'0) (Real.exp_pos _).le)
      _ = 2 * CΓ * S * |t| ^ (NΓ + 1) := by
          rw [pow_succ]
          linear_combination (2 * CΓ * S * |t| ^ NΓ * |t|) * hexpcancel
      _ ≤ (2 * CΓ * S + S) * |t| ^ (NΓ + 1) := by
          have hpos : (0 : ℝ) ≤ S * |t| ^ (NΓ + 1) := mul_nonneg hS0 htp
          nlinarith [hpos]

end

end RHTower
