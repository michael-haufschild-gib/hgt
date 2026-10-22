import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueTentLaplace

/-!
# The prime tent series is the logarithmically weighted filtered Mangoldt series

The `n`-th tent weight, evaluated against `e^{-σ log n}`, is exactly half the `n`-th term of the
`L`-series of `log · Λ(n)(1 − n^{-2})` at `σ − 1/2`.  The two `n`-powers that make this work are the
`n^{-1/2}` of Suzuki's kernel and the `sinh(log n) = (n − n^{-1})/2` of the tent's height:

`n^{-1/2}(n − n^{-1}) = n^{1/2}(1 − n^{-2})`.

So the tent series converges exactly where that `L`-series does — to the right of `3/2` — and sums to
half of it.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The filtered Mangoldt coefficient, read as a real number. -/
def filteredVonMangoldtReal (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (1 - (n : ℝ) ^ (-(2 : ℝ)))

theorem filteredVonMangoldtReal_nonneg (n : ℕ) : 0 ≤ filteredVonMangoldtReal n := by
  rw [filteredVonMangoldtReal]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have h : (n : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hnpos.le, inv_le_one_iff₀]
      right
      calc (1 : ℝ) = (1 : ℝ) ^ (2 : ℝ) := by norm_num
        _ ≤ (n : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow (by norm_num) hn1 (by norm_num)
    have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    nlinarith

theorem filteredVonMangoldtCoeff_eq_ofReal (n : ℕ) :
    filteredVonMangoldtCoeff n = ((filteredVonMangoldtReal n : ℝ) : ℂ) := by
  rw [filteredVonMangoldtCoeff, filteredVonMangoldtReal]
  push_cast
  congr 2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    norm_num
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h := Complex.ofReal_cpow hn0 (-(2 : ℝ))
    push_cast at h
    exact h.symm

/-- **The tent weight is half the filtered Mangoldt term.**  The kernel's `n^{-1/2}` and the tent's
`sinh(log n)` combine into the `L`-series shift `σ ↦ σ − 1/2`. -/
theorem suzukiTentCoeff_mul_exp_eq {σ : ℝ} (n : ℕ) :
    suzukiTentCoeff n * Real.exp (-σ * Real.log n)
      = (1 / 2) * (Real.log n * filteredVonMangoldtReal n * (n : ℝ) ^ (-(σ - 1 / 2))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [suzukiTentCoeff, filteredVonMangoldtReal]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hexp : Real.exp (-σ * Real.log n) = (n : ℝ) ^ (-σ) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (n : ℝ)
    have hsinh : Real.sinh (Real.log n) = ((n : ℝ) - (n : ℝ)⁻¹) / 2 := by
      rw [Real.sinh_eq, Real.exp_log hnpos, Real.exp_neg, Real.exp_log hnpos]
    have hinv2 : (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ) ^ (2 : ℝ))⁻¹ := Real.rpow_neg hnpos.le 2
    have hsq : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) * (n : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hpow : (n : ℝ) ^ (-(σ - 1 / 2)) = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-σ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    have hnhalf : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
      rw [← Real.rpow_add hnpos]
      norm_num
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    rw [suzukiTentCoeff, filteredVonMangoldtReal, hexp, hsqrt, hsinh, hpow, hinv2, hsq]
    set Lg : ℝ := Real.log (n : ℝ) with hLgdef
    set A : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) with hAdef
    set a : ℝ := (n : ℝ) ^ ((1 : ℝ) / 2) with hadef
    set b : ℝ := (n : ℝ) ^ (-σ) with hbdef
    have hapos : (0 : ℝ) < a := by
      rw [hadef]
      exact Real.rpow_pos_of_pos hnpos _
    rw [← hnhalf]
    field_simp


/-- The `L`-series term of the logarithmically weighted filtered coefficient is a real number. -/
theorem LSeries_term_logMul_filtered_eq (σ : ℝ) (n : ℕ) :
    LSeries.term (LSeries.logMul filteredVonMangoldtCoeff) ((σ : ℂ) - 1 / 2) n
      = ((Real.log n * filteredVonMangoldtReal n * (n : ℝ) ^ (-(σ - 1 / 2)) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [LSeries.term]
  · have hnne : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : ((σ : ℂ) - 1 / 2) = (((σ - 1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
    have hcpow : ((n : ℂ)) ^ (((σ - 1 / 2 : ℝ)) : ℂ) = (((n : ℝ) ^ (σ - 1 / 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hnpos.le]
    rw [LSeries.term_of_ne_zero hnne, LSeries.logMul, filteredVonMangoldtCoeff_eq_ofReal, hcast,
      hlog, hcpow, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    congr 1
    rw [Real.rpow_neg hnpos.le]
    field_simp

theorem summable_suzukiTentCoeff_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    Summable fun n : ℕ => suzukiTentCoeff n * Real.exp (-σ * Real.log n) := by
  have habs : LSeries.abscissaOfAbsConv filteredVonMangoldtCoeff < (((σ : ℂ) - 1 / 2).re : EReal) := by
    refine lt_of_le_of_lt abscissaOfAbsConv_filteredVonMangoldtCoeff_le_one ?_
    have hre : ((σ : ℂ) - 1 / 2).re = σ - 1 / 2 := by simp
    rw [hre]
    exact_mod_cast (by linarith : (1 : ℝ) < σ - 1 / 2)
  have hLS : LSeriesSummable (LSeries.logMul filteredVonMangoldtCoeff) ((σ : ℂ) - 1 / 2) :=
    LSeriesSummable_logMul_of_lt_re habs
  have hC : Summable fun n : ℕ =>
      ((Real.log n * filteredVonMangoldtReal n * (n : ℝ) ^ (-(σ - 1 / 2)) : ℝ) : ℂ) := by
    refine hLS.congr fun n => ?_
    exact LSeries_term_logMul_filtered_eq σ n
  have hR : Summable fun n : ℕ =>
      Real.log n * filteredVonMangoldtReal n * (n : ℝ) ^ (-(σ - 1 / 2)) :=
    Complex.summable_ofReal.mp hC
  refine (hR.mul_left (1 / 2)).congr fun n => ?_
  exact (suzukiTentCoeff_mul_exp_eq n).symm

theorem tsum_suzukiTentCoeff_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    ((∑' n : ℕ, suzukiTentCoeff n * Real.exp (-σ * Real.log n) : ℝ) : ℂ)
      = (1 / 2) * LSeries (LSeries.logMul filteredVonMangoldtCoeff) ((σ : ℂ) - 1 / 2) := by
  have habs : LSeries.abscissaOfAbsConv filteredVonMangoldtCoeff < (((σ : ℂ) - 1 / 2).re : EReal) := by
    refine lt_of_le_of_lt abscissaOfAbsConv_filteredVonMangoldtCoeff_le_one ?_
    have hre : ((σ : ℂ) - 1 / 2).re = σ - 1 / 2 := by simp
    rw [hre]
    exact_mod_cast (by linarith : (1 : ℝ) < σ - 1 / 2)
  have hLS : LSeriesSummable (LSeries.logMul filteredVonMangoldtCoeff) ((σ : ℂ) - 1 / 2) :=
    LSeriesSummable_logMul_of_lt_re habs
  have hcongr : ∀ n : ℕ, suzukiTentCoeff n * Real.exp (-σ * Real.log n)
      = (1 / 2) * (Real.log n * filteredVonMangoldtReal n * (n : ℝ) ^ (-(σ - 1 / 2))) :=
    fun n => suzukiTentCoeff_mul_exp_eq n
  rw [tsum_congr hcongr, tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 1
  · norm_num
  · rw [LSeries]
    refine tsum_congr fun n => ?_
    exact (LSeries_term_logMul_filtered_eq σ n).symm

end RHTower
