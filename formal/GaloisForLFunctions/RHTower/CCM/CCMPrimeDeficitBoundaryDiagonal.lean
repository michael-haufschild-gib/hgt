import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitShortenedCutoffWindow

/-!
# Critical control of the diagonal in a thick boundary shell

For the full shell `3k <= m`, the diagonal costs at most `9k^2/m <= m`.
It therefore stays at square-root scale without the thin-shell condition
`k^3 <= m^2`. The exact complement retains all signed interactions between
distinct indices, whose cancellation is not assumed.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitBoundaryDiagonal (m k : ℕ) (T : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
    logarithmicLongTail m moebiusCoeff a ^ 2 *
      ccmPrimeDeficitDivisorSource (T - Real.log (a * a : ℕ))

def ccmPrimeDeficitBoundaryOffDiagonal (m k : ℕ) (T : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
    ∑ b ∈ (Finset.Icc (m + 1) (m + 3 * k)).erase a,
      logarithmicLongTail m moebiusCoeff a * logarithmicLongTail m moebiusCoeff b *
        ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))

theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_diagonal_add_offDiagonal
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T =
      ccmPrimeDeficitBoundaryDiagonal m k T + ccmPrimeDeficitBoundaryOffDiagonal m k T := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_eq_strip hm hk h0 hT]
  symm
  unfold ccmPrimeDeficitBoundaryDiagonal ccmPrimeDeficitBoundaryOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  simpa only [pow_two, add_comm] using Finset.sum_erase_add
    (Finset.Icc (m + 1) (m + 3 * k))
    (fun b => logarithmicLongTail m moebiusCoeff a * logarithmicLongTail m moebiusCoeff b *
      ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))) ha

theorem abs_ccmPrimeDeficitBoundaryDiagonal_quadratic_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ}
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    |ccmPrimeDeficitBoundaryDiagonal m k T| ≤ 9 * (k : ℝ) ^ 2 / m := by
  have hterm (a : ℕ) (ha : a ∈ Finset.Icc (m + 1) (m + 3 * k)) :
      |logarithmicLongTail m moebiusCoeff a ^ 2 *
        ccmPrimeDeficitDivisorSource (T - Real.log (a * a : ℕ))| ≤ 3 * (k : ℝ) / m := by
    have ham : m < a := by have := (Finset.mem_Icc.mp ha).1; omega
    have hsq : |logarithmicLongTail m moebiusCoeff a| ^ 2 ≤ 1 := by
      have hb := abs_logarithmicLongTail_moebiusCoeff_le_one m a
      simpa only [pow_two, one_mul] using mul_le_mul hb hb (abs_nonneg _) zero_le_one
    rw [abs_mul, abs_pow]
    simpa only [one_mul] using mul_le_mul hsq
      (abs_ccmPrimeDeficitDivisorSource_square_window_near_le hm hk ham ham hT)
      (abs_nonneg _) zero_le_one
  unfold ccmPrimeDeficitBoundaryDiagonal
  calc
    _ ≤ ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
        |logarithmicLongTail m moebiusCoeff a ^ 2 *
          ccmPrimeDeficitDivisorSource (T - Real.log (a * a : ℕ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.Icc (m + 1) (m + 3 * k), 3 * (k : ℝ) / m :=
      Finset.sum_le_sum hterm
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc,
        show m + 3 * k + 1 - (m + 1) = 3 * k by omega, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_ofNat]
      ring

theorem ccmPrimeDeficitBoundaryDiagonal_eq_zero_before_cutoff
    {m : ℕ} (hm : 0 < m) (k : ℕ) {T : ℝ} (hT : T ≤ 2 * Real.log (m : ℝ)) :
    ccmPrimeDeficitBoundaryDiagonal m k T = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have ham : m < a := by have := (Finset.mem_Icc.mp ha).1; omega
  have hz := ccmPrimeDeficitDivisorSource_square_window_far_zero
    (k := 0) hm (by omega) (by simpa only [mul_zero, Nat.add_zero] using ham) ham
    (by simpa only [Nat.add_zero] using hT)
  rw [hz, mul_zero]

/-- Every diagonal contribution of the thick boundary shell is controlled
at the actual time's critical scale. -/
theorem abs_ccmPrimeDeficitBoundaryDiagonal_critical_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ}
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    |ccmPrimeDeficitBoundaryDiagonal m k T| ≤ Real.exp (T / 2) := by
  by_cases ht : T ≤ 2 * Real.log (m : ℝ)
  · rw [ccmPrimeDeficitBoundaryDiagonal_eq_zero_before_cutoff hm k ht, abs_zero]
    exact (Real.exp_pos _).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : 3 * (k : ℝ) ≤ m := by exact_mod_cast hk
  calc
    _ ≤ 9 * (k : ℝ) ^ 2 / m := abs_ccmPrimeDeficitBoundaryDiagonal_quadratic_le hm hk hT
    _ ≤ m := by
      rw [div_le_iff₀ hmR]
      nlinarith only [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 3 * k) hkR]
    _ = Real.exp (Real.log (m : ℝ)) := (Real.exp_log hmR).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_sub_offDiagonal_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T -
      ccmPrimeDeficitBoundaryOffDiagonal m k T| ≤ Real.exp (T / 2) := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_diagonal_add_offDiagonal hm hk h0 hT,
    add_sub_cancel_right]
  exact abs_ccmPrimeDeficitBoundaryDiagonal_critical_le hm hk hT

end RHTower
