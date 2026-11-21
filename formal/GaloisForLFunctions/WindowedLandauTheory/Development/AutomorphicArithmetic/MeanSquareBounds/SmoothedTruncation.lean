import GaloisForLFunctions.WindowedLandauTheory.CesaroIncrementBounds
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity

/-! Finite decompositions relating the centered ramp to the truncated logarithmic derivative. -/

open Complex Finset ArithmeticFunction WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

noncomputable section

variable {N : ℕ} {χ : DirichletCharacter ℂ N}

def partialLogDerivative (χ : DirichletCharacter ℂ N) (z : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊z⌋₊, twistedVM χ n / n

variable [NeZero N]

theorem gChi_eq_truncated (hχ : χ ≠ 1) {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z)
    {q : ℕ} {κ : ℕ → ℂ} (hval : ∀ n : ℕ, χ n = κ n * J q n) :
    An.gChi χ y = -S z y q κ +
      (y : ℂ) * (partialLogDerivative χ z + An.logDerivativeAtOne χ) := by
  rw [An.gChi, if_neg hχ, sumLamChi_eq_ramp χ hy]
  have hf : ⌊y⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hyz
  have hnm (n : ℕ) (h : n ∈ Icc 1 ⌊z⌋₊) : (0 : ℝ) < n := by
    exact_mod_cast (mem_Icc.mp h).1
  have heq : (∑ n ∈ Icc 1 ⌊y⌋₊, twistedVM χ n * ((y : ℂ) / n - 1)) + S z y q κ =
      (y : ℂ) * partialLogDerivative χ z := by
    have hmask : (∑ n ∈ Icc 1 ⌊y⌋₊, twistedVM χ n * ((y : ℂ) / n - 1)) =
        ∑ n ∈ Icc 1 ⌊z⌋₊, twistedVM χ n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
      rw [← sumLamChi_eq_ramp χ hy]
      unfold An.sumLamChi
      refine (sum_congr rfl (fun n _ => ?_)).trans (sum_subset (Icc_subset_Icc_right hf) ?_)
      · simp only [twistedVM, An.abelian₂]
        rw [mul_comm (vonMangoldt n : ℂ)]
      · intro n hn hny
        have hn' : ⌊y⌋₊ < n := by
          have := (mem_Icc.mp hn).1
          simp only [mem_Icc] at hny
          omega
        have h := (Nat.floor_lt (zero_le_one.trans hy)).mp hn'
        rw [max_eq_right (sub_nonpos.mpr ((div_le_one (hnm n hn)).mpr h.le)), ofReal_zero, mul_zero]
    rw [hmask, S, partialLogDerivative, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hw : max (y / (n : ℝ) - 1) 0 + min 1 (y / (n : ℝ)) = y / (n : ℝ) := by
      rcases le_or_gt 1 (y / (n : ℝ)) with h | h
      · rw [max_eq_left (sub_nonneg.mpr h), min_eq_left h]; ring
      · rw [max_eq_right (sub_nonpos.mpr h.le), min_eq_right h.le, zero_add]
    have hc : (cN y n : ℂ) * κ n * J q n =
        twistedVM χ n * (↑(min 1 (y / n)) : ℂ) := by
      rw [cN, ofReal_mul, twistedVM, hval]
      ring
    rw [hc, ← mul_add, ← ofReal_add, hw, ofReal_div, ofReal_natCast]
    ring
  linear_combination heq

/-- The difference quotient of the ramp recovers its partial logarithmic derivative with a
short-interval error that depends only on the Mangoldt bound. -/
theorem norm_ramp_difference_sub (hχ : χ ≠ 1) {z h : ℝ} (hz : 1 < z) (hh : 0 < h) :
    ‖An.gChi χ (z + h) - An.gChi χ z -
      (h : ℂ) * (partialLogDerivative χ z + An.logDerivativeAtOne χ)‖ ≤
      h * (h + 1) * Real.log (z + h) / z := by
  have hzh : z ≤ z + h := le_add_of_nonneg_right hh.le
  have hzf : ⌊z⌋₊ ≤ ⌊z + h⌋₊ := Nat.floor_le_floor hzh
  let t := z + h
  let I := (Icc 1 ⌊t⌋₊).filter (⌊z⌋₊ < ·)
  have hθ : An.sumLamChi χ t - An.sumLamChi χ z - (h : ℂ) * partialLogDerivative χ z =
      ∑ n ∈ I, twistedVM χ n * ((t : ℂ) / n - 1) := by
    rw [sumLamChi_eq_ramp χ (hz.le.trans hzh), sumLamChi_eq_ramp χ hz.le,
      WindowedLandauTheory.sum_Icc_eq_add_filter _ hzf, add_sub_right_comm, ← sum_sub_distrib]
    rw [partialLogDerivative, mul_sum]
    have he : (∑ n ∈ Icc 1 ⌊z⌋₊,
        (twistedVM χ n * ((t : ℂ) / n - 1) - twistedVM χ n * ((z : ℂ) / n - 1))) =
        ∑ n ∈ Icc 1 ⌊z⌋₊, (h : ℂ) * (twistedVM χ n / n) := by
      refine sum_congr rfl fun n _ => ?_
      rw [show (t : ℂ) = (z : ℂ) + (h : ℂ) from ofReal_add z h, add_div]
      ring
    rw [he]
    abel
  have hcard : (I.card : ℝ) ≤ h + 1 := by
    have hI : I = Ioc ⌊z⌋₊ ⌊t⌋₊ := by
      ext n
      simp only [I, mem_filter, mem_Icc, mem_Ioc]
      omega
    rw [hI, Nat.card_Ioc, Nat.cast_sub hzf]
    have ht := Nat.floor_le (show 0 ≤ t from zero_le_one.trans (hz.le.trans hzh))
    have hzl := Nat.lt_floor_add_one z
    dsimp [t] at ht
    linarith only [ht, hzl]
  have ht : 1 ≤ t := hz.le.trans hzh
  have hbound (n : ℕ) (hn : n ∈ I) :
      ‖twistedVM χ n * ((t : ℂ) / n - 1)‖ ≤ h * Real.log t / z := by
    obtain ⟨hn₁, hn₂⟩ := mem_filter.mp hn
    have hzn : z < (n : ℝ) := (Nat.floor_lt (zero_le_one.trans hz.le)).mp hn₂
    have hn₀ : (0 : ℝ) < n := (by linarith only [hz] : 0 < z).trans hzn
    have hnt : (n : ℝ) ≤ t := (Nat.le_floor_iff (zero_le_one.trans ht)).mp (mem_Icc.mp hn₁).2
    have hw : 0 ≤ t / (n : ℝ) - 1 := sub_nonneg.mpr ((le_div_iff₀ hn₀).mpr (by simpa using hnt))
    have hw' : t / (n : ℝ) - 1 ≤ h / z := by
      calc t / (n : ℝ) - 1 ≤ h / (n : ℝ) := by
            rw [div_sub_one hn₀.ne', div_le_div_iff_of_pos_right hn₀]
            dsimp [t]
            linarith only [hzn]
        _ ≤ h / z := div_le_div_of_nonneg_left hh.le (by linarith only [hz]) hzn.le
    have hVM : ‖twistedVM χ n‖ ≤ Real.log t := by
      rw [twistedVM, norm_mul, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      rw [mul_comm ‖χ (n : ZMod N)‖]
      exact (mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)).trans
        (vonMangoldt_le_log.trans (Real.log_le_log hn₀ hnt))
    rw [norm_mul, ← ofReal_natCast, ← ofReal_div, ← ofReal_one, ← ofReal_sub,
      norm_real, Real.norm_of_nonneg hw]
    calc _ ≤ Real.log t * (h / z) := mul_le_mul hVM hw' hw (Real.log_nonneg ht)
      _ = _ := by ring
  rw [An.gChi, if_neg hχ, An.gChi, if_neg hχ]
  change ‖An.sumLamChi χ t + (t : ℂ) * An.logDerivativeAtOne χ -
    (An.sumLamChi χ z + (z : ℂ) * An.logDerivativeAtOne χ) - _‖ ≤ _
  rw [show An.sumLamChi χ t + (t : ℂ) * An.logDerivativeAtOne χ -
      (An.sumLamChi χ z + (z : ℂ) * An.logDerivativeAtOne χ) -
        (h : ℂ) * (partialLogDerivative χ z + An.logDerivativeAtOne χ) =
      An.sumLamChi χ t - An.sumLamChi χ z - (h : ℂ) * partialLogDerivative χ z by
        rw [show (t : ℂ) = (z : ℂ) + (h : ℂ) from ofReal_add z h]; ring, hθ]
  calc ‖∑ n ∈ I, twistedVM χ n * ((t : ℂ) / n - 1)‖
      ≤ ∑ _n ∈ I, h * Real.log t / z := (norm_sum_le _ _).trans (sum_le_sum hbound)
    _ = (I.card : ℝ) * (h * Real.log t / z) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (h + 1) * (h * Real.log t / z) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg (mul_nonneg hh.le (Real.log_nonneg ht)) (by linarith only [hz]))
    _ = _ := by ring

end

end QH
