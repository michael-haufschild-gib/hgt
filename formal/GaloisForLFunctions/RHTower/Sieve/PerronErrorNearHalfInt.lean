import GaloisForLFunctions.RHTower.Sieve.PerronErrorSplit

/-!
# The near part of the Perron error at a half-integer cutoff

Inside the dyadic window the logarithm is comparable to the displacement, and at a half-integer
cutoff no integer is closer than `1/2`, so the near part of the Perron error is a reciprocal-distance
sum over distinct odd integers — harmonic, hence polylogarithmic.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **The near part of the Perron error.** -/
theorem perron_error_near_halfInt_le {c : ℕ → ℂ} {N : ℕ} {σ T B : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 2) (hT : 0 < T) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, (n : ℝ) ≤ 2 * ((N : ℝ) + 1 / 2) → ‖c n‖ ≤ B) :
    ∑' n : ℕ, (if ((N : ℝ) + 1 / 2) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((N : ℝ) + 1 / 2) then
        ‖c n‖ * ((((N : ℝ) + 1 / 2) / n) ^ σ
          / (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)) else 0)
      ≤ (16 * B * ((N : ℝ) + 1 / 2) / (Real.pi * T))
          * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hx : (0 : ℝ) < x := by rw [hxdef]; positivity
  have hsupp : ∀ n : ℕ, n ∉ Finset.range (2 * N + 2) →
      (if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then
        ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnge : (2 * N + 2 : ℝ) ≤ (n : ℝ) := by
      have : 2 * N + 2 ≤ n := by omega
      exact_mod_cast this
    refine if_neg ?_
    rintro ⟨-, h2⟩
    rw [hxdef] at h2
    linarith
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ n ∈ Finset.range (2 * N + 2),
      (if x / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then
        ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) else 0)
        ≤ (16 * B * x / (Real.pi * T)) * (1 / |x - (n : ℝ)|) := by
    intro n _
    have hgap : (1 : ℝ) / 2 ≤ |x - (n : ℝ)| := by
      rw [hxdef]
      have hkey : |(N : ℝ) + 1 / 2 - (n : ℝ)| = |((2 * (N : ℤ) + 1 - 2 * (n : ℤ) : ℤ) : ℝ)| / 2 := by
        push_cast
        rw [show |2 * (N : ℝ) + 1 - 2 * (n : ℝ)| = |2 * ((N : ℝ) + 1 / 2 - (n : ℝ))| by ring_nf,
          abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        ring
      rw [hkey]
      have hne : (2 * (N : ℤ) + 1 - 2 * (n : ℤ)) ≠ 0 := by omega
      have h1 : (1 : ℤ) ≤ |2 * (N : ℤ) + 1 - 2 * (n : ℤ)| := by
        rcases lt_or_gt_of_ne hne with h | h <;> rw [Int.abs_eq_natAbs] <;> omega
      have h1R : (1 : ℝ) ≤ |((2 * (N : ℤ) + 1 - 2 * (n : ℤ) : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast h1
      linarith
    have hgap0 : (0 : ℝ) < |x - (n : ℝ)| := by linarith
    split_ifs with hnear
    · have hn0 : (0 : ℝ) < (n : ℝ) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exfalso
          have := hnear.1
          simp only [Nat.cast_zero] at this
          linarith
        · exact_mod_cast hn
      have hxn : (0 : ℝ) < x / n := div_pos hx hn0
      have hy1 : (1 : ℝ) / 2 ≤ x / n := by rw [le_div_iff₀ hn0]; linarith [hnear.2]
      have hy2 : x / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith [hnear.1]
      have hlogb := abs_sub_one_le_two_mul_abs_log hy1 hy2
      have hdisp : |x / n - 1| = |x - (n : ℝ)| / n := by
        rw [show x / n - 1 = (x - (n : ℝ)) / n by field_simp, abs_div, abs_of_pos hn0]
      rw [hdisp, div_le_iff₀ hn0] at hlogb
      have hlow : |x - (n : ℝ)| / (4 * x) ≤ |Real.log (x / n)| := by
        have hstep : |x - (n : ℝ)| / (2 * (n : ℝ)) ≤ |Real.log (x / n)| := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        have hmono : |x - (n : ℝ)| / (4 * x) ≤ |x - (n : ℝ)| / (2 * (n : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (abs_nonneg (x - (n : ℝ)))
            (by linarith [hnear.2] : (0:ℝ) ≤ 4 * x - 2 * (n : ℝ))]
        linarith
      have hpow0 : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg hxn.le σ
      have hpow : (x / n) ^ σ ≤ 4 := by
        have h1 : (x / n) ^ σ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow hxn.le hy2 hσ.le
        have h2 : (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
        have h3 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
          rw [show ((2 : ℝ) : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          norm_num
        linarith
      have hd1 : (0 : ℝ) < Real.pi * T * (|x - (n : ℝ)| / (4 * x)) := by positivity
      have hinv : 1 / (Real.pi * T * |Real.log (x / n)|)
          ≤ 4 * x / (Real.pi * T * |x - (n : ℝ)|) := by
        have hden : Real.pi * T * (|x - (n : ℝ)| / (4 * x))
            ≤ Real.pi * T * |Real.log (x / n)| := by
          have hpT : (0 : ℝ) < Real.pi * T := by positivity
          nlinarith [hlow, hpT]
        have h1 : 1 / (Real.pi * T * |Real.log (x / n)|)
            ≤ 1 / (Real.pi * T * (|x - (n : ℝ)| / (4 * x))) :=
          one_div_le_one_div_of_le hd1 hden
        refine h1.trans (le_of_eq ?_)
        field_simp
      calc ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|))
          = (‖c n‖ * (x / n) ^ σ) * (1 / (Real.pi * T * |Real.log (x / n)|)) := by ring
        _ ≤ (B * 4) * (4 * x / (Real.pi * T * |x - (n : ℝ)|)) := by
            refine mul_le_mul ?_ hinv (by positivity) (by positivity)
            exact mul_le_mul (hB n hnear.2) hpow hpow0 hB0
        _ = (16 * B * x / (Real.pi * T)) * (1 / |x - (n : ℝ)|) := by
            field_simp
            ring

    · positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hbase := sum_inv_dist_halfInt_le N (Finset.range (2 * N + 2))
  have hcard : (Finset.range (2 * N + 2)).card = 2 * N + 2 := Finset.card_range _
  rw [hcard] at hbase
  have hcoef : (0 : ℝ) ≤ 16 * B * x / (Real.pi * T) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  refine hbase.trans (le_of_eq ?_)
  congr 2

end

end RHTower.Sieve
