import GaloisForLFunctions.RHTower.CCMPrimeDeficitBoundaryKernel
import GaloisForLFunctions.RHTower.CCMPrimeDeficitTruncationDefect
import GaloisForLFunctions.RHTower.LogarithmicCausalPairHorizon

/-!
# Uniform control of the signed cutoff defect

One shortened Möbius prefix controls the truncation error throughout
`0 <= T <= 2 log(m+k)`. The cubic estimate reaches the critical scale
`exp(T/2)` throughout this window when `k^3 <= m^2` and `3k <= m`.
This estimates the omitted boundary component; the retained action still
requires its own bound.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

private def boundaryTerm (m : ℕ) (T : ℝ) (a b : ℕ) : ℝ :=
  logarithmicLongTail m moebiusCoeff a * logarithmicLongTail m moebiusCoeff b *
    ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))

private theorem boundaryTerm_comm (m : ℕ) (T : ℝ) (a b : ℕ) :
    boundaryTerm m T a b = boundaryTerm m T b a := by
  unfold boundaryTerm
  rw [Nat.mul_comm a b]
  ring

private theorem boundaryTerm_zero_left {m k a : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m)
    {T : ℝ} (hT : T ≤ 2 * Real.log (m + k : ℕ))
    (ha : a ∉ Finset.Icc (m + 1) (m + 3 * k)) (b : ℕ) : boundaryTerm m T a b = 0 := by
  by_cases ham : m < a
  · by_cases hbm : m < b
    · have hafar : m + 3 * k < a := by
        simp only [Finset.mem_Icc] at ha
        omega
      unfold boundaryTerm
      rw [ccmPrimeDeficitDivisorSource_square_window_far_zero hm hk hafar hbm hT, mul_zero]
    · simp [boundaryTerm, logarithmicLongTail, hbm]
  · simp [boundaryTerm, logarithmicLongTail, ham]

private theorem strip_subset_square {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) :
    Finset.Icc (m + 1) (m + 3 * k) ⊆ Finset.Icc 1 ((m + k) ^ 2) := by
  intro a ha
  have halow := (Finset.mem_Icc.mp ha).1
  have hahigh := (Finset.mem_Icc.mp ha).2
  by_cases hm2 : 2 ≤ m
  · apply Finset.mem_Icc.mpr
    refine ⟨by omega, hahigh.trans ?_⟩
    nlinarith [Nat.mul_le_mul_left m hm2, Nat.zero_le (m * k), Nat.zero_le (k * k)]
  · have hm1 : m = 1 := by omega
    have hk0 : k = 0 := by omega
    omega

/-- The full signed defect has the same finite support throughout the window. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_eq_strip
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T =
      ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k), ∑ b ∈ Finset.Icc (m + 1) (m + 3 * k),
        logarithmicLongTail m moebiusCoeff a * logarithmicLongTail m moebiusCoeff b *
          ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ)) := by
  have hN : (0 : ℝ) < (m + k : ℕ) := by exact_mod_cast (show 0 < m + k by omega)
  have hfloor : ⌊Real.exp T⌋₊ ≤ (m + k) ^ 2 := by
    calc
      _ ≤ ⌊Real.exp (2 * Real.log (m + k : ℕ))⌋₊ := Nat.floor_mono (Real.exp_le_exp.mpr hT)
      _ = _ := by
        rw [two_mul, Real.exp_add, Real.exp_log hN, ← Nat.cast_mul, Nat.floor_natCast, pow_two]
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction m h0,
    logarithmicWeightedDilation_pair_eq_square_of_horizon _ _ _
      (fun _ ht => ccmPrimeDeficitDivisorSource_of_nonpos ht.le) hfloor]
  change (∑ a ∈ Finset.Icc 1 ((m + k) ^ 2), ∑ b ∈ Finset.Icc 1 ((m + k) ^ 2),
      boundaryTerm m T a b) = ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
        ∑ b ∈ Finset.Icc (m + 1) (m + 3 * k), boundaryTerm m T a b
  have hsub := strip_subset_square hm hk
  have ho : (∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
      ∑ b ∈ Finset.Icc 1 ((m + k) ^ 2), boundaryTerm m T a b) =
      ∑ a ∈ Finset.Icc 1 ((m + k) ^ 2), ∑ b ∈ Finset.Icc 1 ((m + k) ^ 2),
        boundaryTerm m T a b := by
    apply Finset.sum_subset hsub
    intro a _ ha
    exact Finset.sum_eq_zero (fun b _ => boundaryTerm_zero_left hm hk hT ha b)
  rw [← ho]
  apply Finset.sum_congr rfl
  intro a _
  symm
  apply Finset.sum_subset hsub
  intro b _ hb
  rw [boundaryTerm_comm]
  exact boundaryTerm_zero_left hm hk hT hb a

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_cubic_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T| ≤
      27 * (k : ℝ) ^ 3 / m := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_eq_strip hm hk h0 hT]
  let J := Finset.Icc (m + 1) (m + 3 * k)
  have hterm (a : ℕ) (ha : a ∈ J) (b : ℕ) (hb : b ∈ J) :
      |boundaryTerm m T a b| ≤ 3 * (k : ℝ) / m := by
    have ham : m < a := by have := (Finset.mem_Icc.mp ha).1; omega
    have hbm : m < b := by have := (Finset.mem_Icc.mp hb).1; omega
    have hc : |logarithmicLongTail m moebiusCoeff a| *
        |logarithmicLongTail m moebiusCoeff b| ≤ 1 := by
      simpa only [one_mul] using mul_le_mul
        (abs_logarithmicLongTail_moebiusCoeff_le_one m a)
        (abs_logarithmicLongTail_moebiusCoeff_le_one m b) (abs_nonneg _) zero_le_one
    rw [boundaryTerm, abs_mul, abs_mul]
    simpa only [one_mul] using mul_le_mul hc
      (abs_ccmPrimeDeficitDivisorSource_square_window_near_le hm hk ham hbm hT)
      (abs_nonneg _) zero_le_one
  change |∑ a ∈ J, ∑ b ∈ J, boundaryTerm m T a b| ≤ _
  calc
    _ ≤ ∑ a ∈ J, |∑ b ∈ J, boundaryTerm m T a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ J, ∑ b ∈ J, |boundaryTerm m T a b| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a ∈ J, ∑ _b ∈ J, 3 * (k : ℝ) / m :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hterm a ha b hb))
    _ = _ := by
      simp only [J, Finset.sum_const, Nat.card_Icc,
        show m + 3 * k + 1 - (m + 1) = 3 * k by omega, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_ofNat]
      ring

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_critical_le
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (hc : k ^ 3 ≤ m ^ 2)
    {T : ℝ} (h0 : 0 ≤ T) (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    |ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T| ≤
      27 * Real.exp (T / 2) := by
  by_cases ht : T ≤ 2 * Real.log (m : ℝ)
  · have hz := abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_cubic_le
      hm (k := 0) (by omega) h0 (by simpa only [Nat.add_zero] using ht)
    simp only [Nat.cast_zero, zero_pow (by norm_num : 3 ≠ 0), mul_zero, zero_div] at hz
    exact hz.trans (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcR : (k : ℝ) ^ 3 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hc
  have hme : (m : ℝ) ≤ Real.exp (T / 2) := by
    calc
      _ = Real.exp (Real.log (m : ℝ)) := (Real.exp_log hmR).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 27 * (k : ℝ) ^ 3 / m :=
      abs_ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_cubic_le hm hk h0 hT
    _ ≤ 27 * (m : ℝ) ^ 2 / m := by gcongr
    _ = 27 * (m : ℝ) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hme (by norm_num)

end RHTower
