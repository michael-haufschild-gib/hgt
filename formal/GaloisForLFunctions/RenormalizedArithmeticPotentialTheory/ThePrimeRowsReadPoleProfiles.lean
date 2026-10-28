import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PolarMatchingReadsTheDensityOfTheGauge

/-!
# Exact prime rows on arbitrary pole profiles

Multiplication of the pole vector by an arbitrary real sequence preserves the
upward-multiple and downward-divisor row decomposition. Subtracting the constant
profile separates the Mertens pole from the arithmetic correction.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction ArithmeticEffectivityTheory ArithmeticElectrostatics

/-- The upward prime sum of a pole profile. -/
def poleProfileUp (g : ℕ → ℝ) (y n : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, g (n * t) * Λ t / (t : ℝ)

/-- The downward divisor sum of a pole profile. -/
def poleProfileDown (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, g d * Λ (n / d)

/-- The correction left after subtracting the constant profile in both directions. -/
def poleProfileCorrection (g : ℕ → ℝ) (y n : ℕ) : ℝ :=
  (∑ t ∈ Icc 1 y, (g (n * t) - g n) * Λ t / (t : ℝ)) +
    ∑ d ∈ n.divisors, (g d - g n) * Λ (n / d)

/-- Complementary divisors put the downward correction in the same jump variable
as its upward counterpart. -/
theorem poleProfileCorrection_eq_divisor_jumps (g : ℕ → ℝ) (y n : ℕ) :
    poleProfileCorrection g y n =
      (∑ t ∈ Icc 1 y, (g (n * t) - g n) * Λ t / (t : ℝ)) +
        ∑ d ∈ n.divisors, (g (n / d) - g n) * Λ d := by
  unfold poleProfileCorrection
  congr 1
  exact (Nat.sum_divisorsAntidiagonal (n := n)
    (fun d e => (g d - g n) * Λ e)).symm.trans
      (Nat.sum_divisorsAntidiagonal' (n := n) (fun d e => (g d - g n) * Λ e))

/-- Multiplication by a constant commutes with the exact row correction. -/
theorem poleProfileCorrection_div (g : ℕ → ℝ) (a : ℝ) (y n : ℕ) :
    poleProfileCorrection (fun j => g j / a) y n = poleProfileCorrection g y n / a := by
  unfold poleProfileCorrection
  rw [add_div, sum_div, sum_div]
  congr 1
  · exact sum_congr rfl fun t _ => by ring
  · exact sum_congr rfl fun d _ => by ring

private theorem sum_up_profile_eq (g : ℕ → ℝ) {m N : ℕ} (hm : 0 < m) :
    (∑ n ∈ Icc 1 N, if m ∣ n ∧ m ≠ n then
      g n * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) = poleProfileUp g (N / m) m := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then
      g n * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) =
      if m ∣ n then g n * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst n
        simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h, poleProfileUp]
  exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]

private theorem sum_down_profile_eq (g : ℕ → ℝ) {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (∑ n ∈ Icc 1 N, if n ∣ m ∧ n ≠ m then g n * Λ (m / n) else 0) =
      poleProfileDown g m := by
  have hterm : ∀ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then g n * Λ (m / n) else 0) =
      if n ∣ m then g n * Λ (m / n) else 0 := by
    intro n _
    by_cases h : n ∣ m
    · by_cases h' : n = m
      · subst n
        simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_Icc_dvd_eq_divisors hm hmN]
  rfl

/-- The literal finite prime row splits exactly into its upward and downward sums. -/
theorem sum_weilPrimeKernel_poleProfile (g : ℕ → ℝ) {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (∑ n ∈ Icc 1 N, weilPrimeKernel m n * (g n * poleVector n)) =
      (poleProfileUp g (N / m) m + poleProfileDown g m) * poleVector m := by
  have hterm : ∀ n ∈ Icc 1 N, weilPrimeKernel m n * (g n * poleVector n) =
      poleVector m *
        ((if m ∣ n ∧ m ≠ n then g n * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) +
          (if n ∣ m ∧ n ≠ m then g n * Λ (m / n) else 0)) := by
    intro n hn
    have hn0 := (mem_Icc.mp hn).1
    have hstep : weilPrimeKernel m n * (g n * poleVector n) =
        g n * (poleVector m * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n))) := by
      rw [← weilPrimeKernel_mul_poleVector hm hn0]
      ring
    rw [hstep, weilPrimeKernel_mul_sqrt_ratio hm hn0]
    split_ifs <;> ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib,
    sum_up_profile_eq g hm, sum_down_profile_eq g hm hmN, mul_comm]

/-- Removing the constant profile leaves precisely the finite arithmetic correction. -/
theorem poleProfileUp_add_down_eq (g : ℕ → ℝ) (y n : ℕ) :
    poleProfileUp g y n + poleProfileDown g n =
      (mertensSum y + Real.log n) * g n + poleProfileCorrection g y n := by
  have hdown : (∑ d ∈ n.divisors, Λ (n / d)) = Real.log n := by
    rw [Nat.sum_div_divisors n (fun d => Λ d), vonMangoldt_sum]
  simp only [poleProfileUp, poleProfileDown, poleProfileCorrection, mertensSum,
    sub_mul, sub_div, sum_sub_distrib, mul_div_assoc, ← mul_sum, hdown]
  ring

/-- Exact centered row identity for arbitrary real pole profiles. -/
theorem sum_weilPrimeKernel_poleProfile_eq_correction (g : ℕ → ℝ) {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (∑ n ∈ Icc 1 N, weilPrimeKernel m n * (g n * poleVector n)) =
      ((mertensSum (N / m) + Real.log m) * g m + poleProfileCorrection g (N / m) m) *
        poleVector m := by
  rw [sum_weilPrimeKernel_poleProfile g hm hmN, poleProfileUp_add_down_eq]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
