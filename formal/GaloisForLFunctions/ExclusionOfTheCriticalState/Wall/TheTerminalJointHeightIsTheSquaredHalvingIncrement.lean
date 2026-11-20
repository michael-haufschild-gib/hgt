import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.JointOscillationsAtTheLastHalfOfThePrimeRow
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# The terminal joint height is the squared halving increment

On the terminal slab the joint height `J_s(H)` of the opposite prime moment is a product of
two positive parts: the halving increment `ΔE(H) = E(H) − E(⌊H/2⌋)`, `E = θ − id`, in the
orientation `s`, and the flank `F(H)`, the odd-quotient prime discrepancy on
`(⌊√H⌋, ⌊H/2⌋]`, in the opposite orientation. The two pieces together form the complete
odd-quotient row beyond `√H`, an alternating divisor count with square-root error. With the
explicit constants of that count, of `ψ − θ` and of the square-root cut:

* `H · J_s(H) = (s ΔE)₊ · (−s F)₊` (`mul_terminalJointHeight`);
* `|F(H) + ΔE(H)| ≤ 95 √H` for `H ≥ 2` (`abs_terminalFlank_add_terminalOddHalf_le`);
* `|H · J_s(H) − (s ΔE)₊²| ≤ 95 √H · (s ΔE)₊` (`abs_mul_terminalJointHeight_sub_sq_le`);
* `|H · (J₊(H) + J₋(H)) − ΔE(H)²| ≤ 95 √H · |ΔE(H)|`
  (`abs_mul_sum_terminalJointHeight_sub_sq_le`).

At the terminal slab the joint height therefore carries no arithmetic beyond one-sided sizes
of the halving increment.
-/

noncomputable section
open scoped Classical
open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- The flank of the terminal slab: the odd-quotient prime discrepancy on `(⌊√H⌋, ⌊H/2⌋]`. -/
def terminalFlank (H : ℕ) : ℝ := oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ (H/2)) H

private theorem icc_one_eq_ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n; simp only [mem_Icc, mem_Ioc]; omega

/-- The complete odd-quotient row: the alternating divisor count plus the prime powers. -/
private theorem abs_complete_row_le (H : ℕ) :
    |oddQuotientPrimeExcess (Ioc 0 H) H| ≤
      (75 + 2*|Real.eulerMascheroniConstant| + 3*(Real.log 4 + 4)) * Real.sqrt H := by
  let Z := fun n : ℕ => ((vonMangoldt - (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) *
    ((H/n%2:ℕ):ℝ)
  have hfull := ExceptionalLayerTheory.abs_prefix_alternatingPrimeExcess H
  rw [ExceptionalLayerTheory.alternatingPrimeExcess_eq_parity_count, icc_one_eq_ioc_zero] at hfull
  have hdiff : |oddQuotientPrimeExcess (Ioc 0 H) H - ∑ n ∈ Ioc 0 H, Z n| ≤
      Chebyshev.psi H - Chebyshev.theta H := by
    rw [oddQuotientPrimeExcess, ← sum_sub_distrib, Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Nat.floor_natCast, sum_filter]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n hn
    have hn0 := (mem_Ioc.mp hn).1.ne'
    have hz : (zeta n:ℝ) = 1 := by simp [ArithmeticFunction.zeta_apply, hn0]
    have hval : (vonMangoldt - (zeta : ArithmeticFunction ℝ)) n = vonMangoldt n - 1 := by
      change vonMangoldt n - (zeta n:ℝ) = _
      rw [hz]
    have hmod := Nat.mod_lt (H/n) (by decide : 0 < 2)
    by_cases h : H/n%2 = 1
    · have hz₁ : Z n = vonMangoldt n - 1 := by simp only [Z, hval, h, Nat.cast_one, mul_one]
      rw [if_pos h, hz₁, ordinaryPrimeExcessCoeff]
      by_cases hp : n.Prime
      · simp [hp, vonMangoldt_apply_prime hp]
      · rw [if_neg hp, if_pos hp, show (0:ℝ) - 1 - (vonMangoldt n - 1) = -vonMangoldt n by ring,
          abs_neg, abs_of_nonneg vonMangoldt_nonneg]
    · have hzero : H/n%2 = 0 := by omega
      have hz₀ : Z n = 0 := by simp only [Z, hzero, Nat.cast_zero, mul_zero]
      rw [if_neg h, hz₀, sub_self, abs_zero]
      split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl
  have h := abs_add_le (oddQuotientPrimeExcess (Ioc 0 H) H - ∑ n ∈ Ioc 0 H, Z n) (∑ n ∈ Ioc 0 H, Z n)
  rw [sub_add_cancel] at h
  change |∑ n ∈ Ioc 0 H, Z n| ≤ (75 + 2*|Real.eulerMascheroniConstant|) * Real.sqrt H at hfull
  linarith only [h, hdiff, hfull,
    GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt (H:ℝ)]

/-- The complete odd-quotient row beyond the square root, with explicit constant. -/
theorem abs_oddQuotientPrimeExcess_above_sqrt_le (H : ℕ) :
    |oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ H) H| ≤
      (76 + 2*|Real.eulerMascheroniConstant| + 3*(Real.log 4 + 4) + Real.log 4) * Real.sqrt H := by
  have hre : ((Ioc 0 H).filter fun n : ℕ => Real.sqrt H < n) = Ioc ⌊Real.sqrt H⌋₊ H := by
    ext n
    rw [mem_filter, mem_Ioc, mem_Ioc, Nat.floor_lt (Real.sqrt_nonneg _)]
    constructor
    · rintro ⟨⟨_, hl⟩, hr⟩; exact ⟨hr, hl⟩
    · rintro ⟨hr, hl⟩; exact ⟨⟨Nat.cast_pos.mp ((Real.sqrt_nonneg _).trans_lt hr), hl⟩, hr⟩
  have hb := oddQuotientPrimeExcess_sqrt_cost (Ioc 0 H) (fun _ hn => (mem_Ioc.mp hn).1) H
  rw [hre] at hb
  have hle := abs_sub (oddQuotientPrimeExcess (Ioc 0 H) H)
    (oddQuotientPrimeExcess (Ioc 0 H) H - oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ H) H)
  rw [sub_sub_cancel] at hle
  linarith only [hle, abs_complete_row_le H, hb]

/-- The explicit constant is below `95`: `γ < 2/3` and `log 4 < 1.4`. -/
private theorem row_constant_le :
    76 + 2*|Real.eulerMascheroniConstant| + 3*(Real.log 4 + 4) + Real.log 4 ≤ 95 := by
  have hγ : |Real.eulerMascheroniConstant| < 2/3 := abs_lt.mpr
    ⟨by linarith [Real.one_half_lt_eulerMascheroniConstant], Real.eulerMascheroniConstant_lt_two_thirds⟩
  have h4 : Real.log 4 < 1.4 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  linarith

/-- **Factorization.** The joint height is the product of the oriented halving increment and the
oppositely oriented flank. -/
theorem mul_terminalJointHeight (s : ℝ) {H : ℕ} (hH : 0 < H) :
    (H:ℝ) * terminalJointHeight s H =
      max 0 (s * terminalOddHalf H) * max 0 ((-s) * terminalFlank H) := by
  have hp : (H:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  simp only [terminalJointHeight, oppositePrimeProduct, middleTestFlank, if_true, terminalOddHalf,
    terminalFlank]
  field_simp

/-- **The flank is the negative halving increment up to `95 √H`.** -/
theorem abs_terminalFlank_add_terminalOddHalf_le {H : ℕ} (hH : 2 ≤ H) :
    |terminalFlank H + terminalOddHalf H| ≤ 95 * Real.sqrt H := by
  have hcut : ⌊Real.sqrt H⌋₊ ≤ H/2 := by
    rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
    obtain ⟨r, hr⟩ : ∃ r, r = Nat.sqrt H := ⟨_, rfl⟩
    rw [← hr]
    have hs : r * r ≤ H := hr ▸ Nat.sqrt_le H
    rcases Nat.lt_or_ge r 2 with h | h
    · omega
    · have h2 : 2 * r ≤ r * r := Nat.mul_le_mul_right r h
      generalize r * r = t at hs h2
      omega
  have hsplit : terminalFlank H + terminalOddHalf H =
      oddQuotientPrimeExcess (Ioc ⌊Real.sqrt H⌋₊ H) H :=
    Finset.sum_Ioc_consecutive _ hcut (Nat.div_le_self H 2)
  rw [hsplit]
  exact (abs_oddQuotientPrimeExcess_above_sqrt_le H).trans
    (mul_le_mul_of_nonneg_right row_constant_le (Real.sqrt_nonneg _))

/-- **Squared halving increment.** In each orientation the joint height is the square of the
oriented halving increment, up to `95 √H` times that increment. -/
theorem abs_mul_terminalJointHeight_sub_sq_le {s : ℝ} (hs : s = 1 ∨ s = -1) {H : ℕ} (hH : 2 ≤ H) :
    |(H:ℝ) * terminalJointHeight s H - (max 0 (s * terminalOddHalf H))^2| ≤
      95 * Real.sqrt H * max 0 (s * terminalOddHalf H) := by
  rw [mul_terminalJointHeight s (by omega)]
  have hP : 0 ≤ max 0 (s * terminalOddHalf H) := le_max_left _ _
  have hQ : |max 0 ((-s) * terminalFlank H) - max 0 (s * terminalOddHalf H)| ≤ 95 * Real.sqrt H := by
    rw [max_comm 0 ((-s) * terminalFlank H), max_comm 0 (s * terminalOddHalf H)]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show (-s) * terminalFlank H - s * terminalOddHalf H =
        -s * (terminalFlank H + terminalOddHalf H) by ring, abs_mul, abs_neg]
    rcases hs with rfl | rfl <;>
      simpa only [abs_one, one_mul, abs_neg] using abs_terminalFlank_add_terminalOddHalf_le hH
  rw [show max 0 (s * terminalOddHalf H) * max 0 ((-s) * terminalFlank H) -
      (max 0 (s * terminalOddHalf H))^2 = max 0 (s * terminalOddHalf H) *
      (max 0 ((-s) * terminalFlank H) - max 0 (s * terminalOddHalf H)) by ring,
    abs_mul, abs_of_nonneg hP, mul_comm (95 * Real.sqrt H)]
  exact mul_le_mul_of_nonneg_left hQ hP

/-- **Both orientations.** The two joint heights together are the squared halving increment up
to `95 √H |ΔE(H)|`. -/
theorem abs_mul_sum_terminalJointHeight_sub_sq_le {H : ℕ} (hH : 2 ≤ H) :
    |(H:ℝ) * (terminalJointHeight 1 H + terminalJointHeight (-1) H) - (terminalOddHalf H)^2| ≤
      95 * Real.sqrt H * |terminalOddHalf H| := by
  have h1 := abs_mul_terminalJointHeight_sub_sq_le (Or.inl rfl) hH
  have h2 := abs_mul_terminalJointHeight_sub_sq_le (Or.inr rfl) hH
  simp only [one_mul, neg_one_mul] at h1 h2
  have hsq : (max 0 (terminalOddHalf H))^2 + (max 0 (-terminalOddHalf H))^2 =
      (terminalOddHalf H)^2 := by
    rcases le_total 0 (terminalOddHalf H) with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonneg.mpr h)]; ring
  have habs : max 0 (terminalOddHalf H) + max 0 (-terminalOddHalf H) = |terminalOddHalf H| := by
    rcases le_total 0 (terminalOddHalf H) with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · rw [max_eq_left h, max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
  rw [← habs, ← hsq, mul_add, mul_add]
  calc _ = |((H:ℝ) * terminalJointHeight 1 H - (max 0 (terminalOddHalf H))^2) +
        ((H:ℝ) * terminalJointHeight (-1) H - (max 0 (-terminalOddHalf H))^2)| := by
          congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

#print axioms mul_terminalJointHeight
#print axioms abs_terminalFlank_add_terminalOddHalf_le
#print axioms abs_mul_terminalJointHeight_sub_sq_le
#print axioms abs_mul_sum_terminalJointHeight_sub_sq_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
