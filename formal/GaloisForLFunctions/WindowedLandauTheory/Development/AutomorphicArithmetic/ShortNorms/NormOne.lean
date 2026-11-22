import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination

/-! Integral norm-one prime representatives in an imaginary quadratic ray class. -/

noncomputable section

namespace GlobalTheory.Mem.An

open Finset

/-- The prime is the norm of an integral quadratic element congruent to one modulo `M`. -/
def NormOne (d M p : ℕ) : Prop :=
  ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧ (M : ℤ) ∣ B ∧ (2 * (M : ℤ)) ∣ A - 2 - B

open Classical in

def normPrimes (d M : ℕ) (X Y : ℝ) : Finset ℕ :=
  (Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun p => p.Prime ∧ NormOne d M p)

/-- The norm is one modulo the level, and its representative works at every divisor of the level. -/
theorem normOne_modEq_one_and_of_dvd :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by
  intro d M p hd h
  obtain ⟨A, B, hAB, hB, hA⟩ := h
  refine ⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB,
    (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨k, hk⟩ := hA
  have hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3 := by omega
  have hA' : A = 2 + M * b + 2 * M * k := by linear_combination hk
  have key : (4 : ℤ) * (p - 1) =
      4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))) := by
    rw [hA', hdq] at hAB
    linear_combination -hAB
  have key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)) := by
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key
  exact (Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm

end GlobalTheory.Mem.An
