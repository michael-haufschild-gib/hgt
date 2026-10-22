import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheInversionDefectIsPositive

/-!
# The majorant source is never admitted

Every estimate for the damped Möbius energy that uses only the *sizes* of the coefficients applies
verbatim to the row `d ↦ d^{-ε}`, which dominates `|μ(d) d^{-ε}|` cell by cell
(`abs_pmPowerDamped_le_majorant`).  That row is a legitimate arithmetic source with the same
divisor prefix, the same pole subtraction and the same pronic observation weight — and it is
**never admitted** at or below half damping.

The reason is a one-sided computation with no cancellation at all.  The floor is at most the
quotient, so the centred prefix is negative and large:

`A^maj_ε(n) ≤ −n (Z(1+ε) − Σ_{d ≤ n} d^{-(1+ε)}) ≤ −2^{-(1+ε)} n^{1-ε}`
(`majorantCenteredPrefix_le`),

since one dyadic block already bounds the tail of the zeta series from below
(`dyadic_block_le_zeta_tail`).  The pronic energy of a row of that size diverges exactly when
`Σ n^{-2ε}` does, hence for every `ε ≤ 1/2` (`not_admits_majorantEnergy`).

So the Möbius signs are not a convenience of the proof: any argument for the damped Möbius energy
that survives replacing `μ(d) d^{-ε}` by its absolute value proves a false statement below the
threshold.  This is the continuation layer's own instance of the corpus's rule that a bound below
half damping must read the signs.
-/

open Finset Filter RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The majorant source -/

/-- The centred prefix of the majorant row `d ↦ d^{-ε}`: the same divisor prefix and the same pole
subtraction as the damped Möbius source, with the signs removed. -/
def majorantCenteredPrefix (ε : ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) * ((n / d : ℕ) : ℝ)) - (n : ℝ) * realZetaSeries (1 + ε)

/-- The pronic energy of the majorant source. -/
def majorantEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, majorantCenteredPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- The majorant row dominates the damped Möbius row cell by cell. -/
theorem abs_pmPowerDamped_le_majorant (ε : ℝ) (d : ℕ) :
    |(ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε)| ≤ (d : ℝ) ^ (-ε) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg d) (-ε), hμ,
    abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]

/-! ## §2. The prefix is large and negative -/

/-- One dyadic block bounds the tail of the zeta series from below. -/
theorem dyadic_block_le_zeta_tail {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-ε) ≤
      realZetaSeries (1 + ε) - ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-(1 + ε)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : (∑ d ∈ Icc 1 (2 * n), (d : ℝ) ^ (-(1 + ε))) =
      (∑ d ∈ Icc 1 n, (d : ℝ) ^ (-(1 + ε))) +
        ∑ d ∈ Icc (n + 1) (2 * n), (d : ℝ) ^ (-(1 + ε)) := by
    have h1 : Ioc 0 (2 * n) = Icc 1 (2 * n) := by ext d; simp only [mem_Ioc, mem_Icc]; omega
    have h2 : Ioc 0 n = Icc 1 n := by ext d; simp only [mem_Ioc, mem_Icc]; omega
    have h3 : Ioc n (2 * n) = Icc (n + 1) (2 * n) := by ext d; simp only [mem_Ioc, mem_Icc]; omega
    have h := Finset.sum_Ioc_consecutive (fun d : ℕ => (d : ℝ) ^ (-(1 + ε)))
      (Nat.zero_le n) (by omega : n ≤ 2 * n)
    rw [h1, h2, h3] at h
    linarith
  have hblock : (n : ℝ) * ((2 * n : ℕ) : ℝ) ^ (-(1 + ε)) ≤
      ∑ d ∈ Icc (n + 1) (2 * n), (d : ℝ) ^ (-(1 + ε)) := by
    have hterm : ∀ d ∈ Icc (n + 1) (2 * n),
        ((2 * n : ℕ) : ℝ) ^ (-(1 + ε)) ≤ (d : ℝ) ^ (-(1 + ε)) := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by
        have : 0 < d := by omega
        exact_mod_cast this
      have hdle : (d : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hd.2
      exact Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
    have hcard := Finset.card_nsmul_le_sum (Icc (n + 1) (2 * n))
      (fun d : ℕ => (d : ℝ) ^ (-(1 + ε))) (((2 * n : ℕ) : ℝ) ^ (-(1 + ε))) hterm
    rw [nsmul_eq_mul, Nat.card_Icc] at hcard
    have hc : ((2 * n + 1 - (n + 1) : ℕ) : ℝ) = (n : ℝ) := by
      have h : (2 * n + 1 - (n + 1) : ℕ) = n := by omega
      rw [h]
    rwa [hc] at hcard
  have hpart := sum_Icc_rpow_le_realZetaSeries hε (2 * n)
  have hdy : ((2 * n : ℕ) : ℝ) ^ (-(1 + ε)) =
      (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-(1 + ε)) := by
    have h : ((2 * n : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) := by push_cast; ring
    rw [h, Real.mul_rpow (by norm_num) (le_of_lt hn0)]
  have hmulpow : (n : ℝ) * ((2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-(1 + ε))) =
      (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-ε) := by
    rw [show -ε = 1 + -(1 + ε) by ring, Real.rpow_add hn0, Real.rpow_one]
    ring
  rw [hdy, hmulpow] at hblock
  linarith

/-- **The centred prefix of the majorant source is large and negative.** -/
theorem majorantCenteredPrefix_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    majorantCenteredPrefix ε n ≤ -((2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : (∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) * ((n / d : ℕ) : ℝ)) ≤
      (n : ℝ) * ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-(1 + ε)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hq : (((n / d : ℕ)) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hp : (0 : ℝ) < (d : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hd0 _
    have hsplit : (d : ℝ) ^ (-(1 + ε)) = (d : ℝ) ^ (-ε) * ((d : ℝ) ^ (-1 : ℝ)) := by
      rw [← Real.rpow_add hd0]
      congr 1
      ring
    calc (d : ℝ) ^ (-ε) * ((n / d : ℕ) : ℝ) ≤ (d : ℝ) ^ (-ε) * ((n : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hq hp.le
      _ = (n : ℝ) * ((d : ℝ) ^ (-ε) * ((d : ℝ) ^ (-1 : ℝ))) := by
          rw [Real.rpow_neg_one]
          field_simp
      _ = (n : ℝ) * (d : ℝ) ^ (-(1 + ε)) := by rw [hsplit]
  have htail := dyadic_block_le_zeta_tail hε hn
  have hmul := mul_le_mul_of_nonneg_left htail (le_of_lt hn0)
  have hleft : (n : ℝ) * ((2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-ε)) =
      (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := by
    rw [show (1 : ℝ) - ε = 1 + -ε by ring, Real.rpow_add hn0, Real.rpow_one]
    ring
  rw [hleft, mul_sub] at hmul
  rw [majorantCenteredPrefix]
  linarith

/-! ## §3. The majorant source is not admitted below the threshold -/

theorem not_summable_rpow_two_mul {ε : ℝ} (hε2 : ε ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * ε))) := by
  intro hsum
  have := Real.summable_nat_rpow.mp hsum
  linarith

/-- Each cell of the majorant energy is at least a constant times `n^{-2ε}`. -/
theorem majorantEnergy_cell_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * (n : ℝ) ^ (-(2 * ε)) ≤
      majorantCenteredPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-(1 + ε)) := Real.rpow_pos_of_pos (by norm_num) _
  have hp : (0 : ℝ) < (n : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos hn0 _
  have hpre := majorantCenteredPrefix_le hε hn
  have hsq : ((2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε)) ^ 2 ≤
      majorantCenteredPrefix ε n ^ 2 := by
    nlinarith [hpre, mul_pos hc hp]
  have hpow2 : ((2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε)) ^ 2 =
      ((2 : ℝ) ^ (-(1 + ε))) ^ 2 * (n : ℝ) ^ (2 - 2 * ε) := by
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 - ε)) 2,
      ← Real.rpow_mul (le_of_lt hn0)]
    congr 2
    push_cast
    ring
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hw : (n : ℝ) * ((n : ℝ) + 1) ≤ 2 * ((n : ℝ) * (n : ℝ)) := by nlinarith [h1n]
  have hnpow : (n : ℝ) ^ (2 - 2 * ε) = (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * (n : ℝ)) := by
    have h2 : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [h2, ← Real.rpow_add hn0]
    congr 1
    ring
  calc ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * (n : ℝ) ^ (-(2 * ε))
      = (((2 : ℝ) ^ (-(1 + ε))) ^ 2 * (n : ℝ) ^ (2 - 2 * ε)) /
          (2 * ((n : ℝ) * (n : ℝ))) := by
        rw [hnpow]
        field_simp
    _ ≤ majorantCenteredPrefix ε n ^ 2 / (2 * ((n : ℝ) * (n : ℝ))) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [← hpow2]
        exact hsq
    _ ≤ majorantCenteredPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hw

/-- **The majorant source is never admitted at or below half damping.** -/
theorem not_admits_majorantEnergy {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ∃ B : ℝ, ∀ T : ℕ, majorantEnergy ε T ≤ B := by
  rintro ⟨B, hB⟩
  have hc2 : (0 : ℝ) < ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 := by positivity
  have hlow : ∀ T : ℕ, ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 *
      (∑ n ∈ range (T + 1), (n : ℝ) ^ (-(2 * ε))) ≤ majorantEnergy ε T := by
    intro T
    have hsplit : (∑ n ∈ range (T + 1), (n : ℝ) ^ (-(2 * ε))) =
        ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
      have hins : (range (T + 1) : Finset ℕ) = insert 0 (Icc 1 T) := by
        ext m
        rw [mem_range, Finset.mem_insert, mem_Icc]
        omega
      rw [hins, Finset.sum_insert (by simp)]
      have hzero : ((0 : ℕ) : ℝ) ^ (-(2 * ε)) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith : -(2 * ε) ≠ 0)]
      rw [hzero, zero_add]
    rw [hsplit, majorantEnergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => majorantEnergy_cell_le hε (mem_Icc.mp hn).1
  have hdiv : Tendsto (fun T : ℕ => ∑ n ∈ range T, (n : ℝ) ^ (-(2 * ε))) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)).mp (not_summable_rpow_two_mul hε2)
  obtain ⟨T, hT⟩ := ((hdiv.const_mul_atTop hc2).eventually_gt_atTop B).exists
  have hmono : (∑ n ∈ range T, (n : ℝ) ^ (-(2 * ε))) ≤
      ∑ n ∈ range (T + 1), (n : ℝ) ^ (-(2 * ε)) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hx
        omega))
      (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hstep := mul_le_mul_of_nonneg_left hmono hc2.le
  have hle := hlow T
  have hBT := hB T
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
