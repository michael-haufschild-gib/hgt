import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDilationLimit
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitMobiusCenteredEnergy

/-!
# The square-root divisor split of the actual signed reconstruction

Subtracting the source's limiting constant makes the entire small-divisor
transient logarithmically bounded. The exact formula keeps the explicit
work, the full Möbius partial sum, and every large-divisor transient.
No cancellation estimate for their combined contribution is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitMobiusTransientHead (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
    moebiusCoeff n *
      (ccmPrimeDeficitDilationRemainder (T - Real.log n) - ccmPrimeDeficitDilationLimit)

def ccmPrimeDeficitMobiusTransientTail (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊Real.exp (T / 2)⌋₊ ⌊Real.exp T⌋₊,
    moebiusCoeff n *
      (ccmPrimeDeficitDilationRemainder (T - Real.log n) - ccmPrimeDeficitDilationLimit)

/-- A bound for the complete signed transient below any admissible cutoff.
The right side depends quadratically on the divisor cutoff, rather than
linearly on the original terminal scale. -/
theorem abs_ccmPrimeDeficitMobiusTransient_prefix_le {T : ℝ} {m : ℕ}
    (hT : 0 ≤ T) (hm : m ≤ ⌊Real.exp T⌋₊) :
    |∑ n ∈ Finset.Icc 1 m, moebiusCoeff n *
      (ccmPrimeDeficitDilationRemainder (T - Real.log n) - ccmPrimeDeficitDilationLimit)| ≤
        Real.exp (-T) * (m : ℝ) ^ 2 * (T + 14) / 4 := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 m) :
      |moebiusCoeff n * (ccmPrimeDeficitDilationRemainder (T - Real.log n) -
        ccmPrimeDeficitDilationLimit)| ≤ Real.exp (-T) * m * (T + 14) / 4 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
    have hnm : (n : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hnT : (n : ℝ) ≤ Real.exp T :=
      (Nat.le_floor_iff (Real.exp_pos T).le).mp ((Finset.mem_Icc.mp hn).2.trans hm)
    have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr hnT
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have he : Real.exp (-(T - Real.log n)) = Real.exp (-T) * n := by
      rw [show -(T - Real.log n) = -T + Real.log n by ring,
        Real.exp_add, Real.exp_log hnpos]
    rw [abs_mul]
    calc
      _ ≤ Real.exp (-(T - Real.log n)) * (T - Real.log n + 14) / 4 := by
        simpa only [one_mul] using mul_le_mul (abs_moebiusCoeff_le_one n)
          (abs_ccmPrimeDeficitDilationRemainder_sub_limit_le (sub_nonneg.mpr hlog))
          (abs_nonneg _) zero_le_one
      _ = Real.exp (-T) * n * (T - Real.log n + 14) / 4 := by rw [he]
      _ ≤ Real.exp (-T) * n * (T + 14) / 4 := by gcongr; linarith only [hlog0]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 m, |moebiusCoeff n *
        (ccmPrimeDeficitDilationRemainder (T - Real.log n) - ccmPrimeDeficitDilationLimit)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 m, Real.exp (-T) * m * (T + 14) / 4 :=
      Finset.sum_le_sum hterm
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- The whole small-divisor transient is `O(T)`, with its actual signs
retained. At `x = exp T`, this lies below square-root scale. -/
theorem abs_ccmPrimeDeficitMobiusTransientHead_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitMobiusTransientHead T| ≤ (T + 14) / 4 := by
  have hm : ⌊Real.exp (T / 2)⌋₊ ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono
    (Real.exp_le_exp.mpr (by linarith only [hT]))
  have hs : (⌊Real.exp (T / 2)⌋₊ : ℝ) ^ 2 ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (T / 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.exp_pos _).le) 2
      _ = Real.exp T := by rw [sq, ← Real.exp_add]; congr 1; ring
  have hc : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ ≤ Real.exp (-T) * (⌊Real.exp (T / 2)⌋₊ : ℝ) ^ 2 * (T + 14) / 4 :=
      abs_ccmPrimeDeficitMobiusTransient_prefix_le hT hm
    _ ≤ Real.exp (-T) * Real.exp T * (T + 14) / 4 := by gcongr
    _ = _ := by rw [hc, one_mul]

private theorem split_sum (f : ℕ → ℝ) {m N : ℕ} (hm : m ≤ N) :
    (∑ n ∈ Finset.Icc 1 m, f n) + (∑ n ∈ Finset.Ioc m N, f n) =
      ∑ n ∈ Finset.Icc 1 N, f n := by
  have hd : Disjoint (Finset.Icc 1 m) (Finset.Ioc m N) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  have hu : Finset.Icc 1 m ∪ Finset.Ioc m N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_union hd, hu]

/-- Full reconstruction after the square-root divisor split. Neither the
Möbius partial sum nor any large-divisor or explicit term is discarded. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_moebius_split {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      ccmPrimeDeficitMobiusExplicitWork T +
        ccmPrimeDeficitDilationLimit * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, moebiusCoeff n) +
          ccmPrimeDeficitMobiusTransientHead T + ccmPrimeDeficitMobiusTransientTail T := by
  have hm : ⌊Real.exp (T / 2)⌋₊ ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono
    (Real.exp_le_exp.mpr (by linarith only [hT]))
  have hs := split_sum (fun n => moebiusCoeff n *
    (ccmPrimeDeficitDilationRemainder (T - Real.log n) - ccmPrimeDeficitDilationLimit)) hm
  rw [ccmLogChebyshevDeficitPrimitive_eq_moebius_centered_work hT,
    ccmPrimeDeficitMobiusTransientHead, ccmPrimeDeficitMobiusTransientTail]
  rw [add_assoc, add_assoc, hs]
  congr 1
  rw [ccmPrimeDeficitMobiusCenteredWork, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- An unconditional bound for the error in retaining the complete long
signed tail together with its explicit and constant channels. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T -
      (ccmPrimeDeficitMobiusExplicitWork T +
        ccmPrimeDeficitDilationLimit * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, moebiusCoeff n) +
          ccmPrimeDeficitMobiusTransientTail T)| ≤ (T + 14) / 4 := by
  rw [ccmLogChebyshevDeficitPrimitive_eq_moebius_split hT]
  convert abs_ccmPrimeDeficitMobiusTransientHead_le hT using 1
  congr 1
  ring

end RHTower
