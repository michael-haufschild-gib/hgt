import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Residue-channel refinement without extra sieve strength

Raising a modulus to a positive power creates more residue labels but excludes
exactly the same integers by coprimality. The surviving fraction is unchanged.
Products likewise separate into their component coprimality tests.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Fraction of a complete residue period surviving the coprimality sieve. -/
def residueChannelDensity (m : ℕ) : ℝ := (m.totient : ℝ) / (m : ℝ)

/-- Power refinement changes channel count by the same factor as period length. -/
theorem totient_channel_pow (m n : ℕ) :
    (m ^ (n + 1)).totient = m ^ n * m.totient := by
  by_cases hm : m = 0
  · subst m
    simp
  have hφ : 0 < m.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : m ∣ m ^ (n + 1) := ⟨m ^ n, by rw [pow_succ]; exact mul_comm _ _⟩
    have h := Nat.totient_gcd_mul_totient_mul m (m ^ (n + 1))
    rw [Nat.gcd_eq_left hd, ih] at h
    apply Nat.eq_of_mul_eq_mul_left hφ
    convert h using 1 <;> ring_nf

theorem residueChannelDensity_pow (m n : ℕ) :
    residueChannelDensity (m ^ (n + 1)) = residueChannelDensity m := by
  by_cases hm : m = 0
  · subst m
    simp [residueChannelDensity]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold residueChannelDensity
  rw [totient_channel_pow]
  push_cast
  rw [pow_succ]
  field_simp

/-- Repeated prime factors change resolution but add no new coprimality exclusion. -/
theorem residueChannel_power_survivor (m n x : ℕ) :
    x.Coprime (m ^ (n + 1)) ↔ x.Coprime m :=
  Nat.coprime_pow_right_iff (Nat.succ_pos n) x m

/-- Joint residue screening is exactly the conjunction of the component screens. -/
theorem residueChannel_product_survivor (m n x : ℕ) :
    x.Coprime (m * n) ↔ x.Coprime m ∧ x.Coprime n :=
  Nat.coprime_mul_iff_right

/-- Arbitrary positive refinements of both component moduli retain the same survivors. -/
theorem residueChannel_refined_product_survivor (m n i j x : ℕ) :
    x.Coprime (m ^ (i + 1) * n ^ (j + 1)) ↔ x.Coprime (m * n) := by
  rw [residueChannel_product_survivor, residueChannel_power_survivor,
    residueChannel_power_survivor, residueChannel_product_survivor]

/-- The number of coprime sites in a refined period scales exactly with the period. -/
theorem residueChannel_refined_count (m n a : ℕ) :
    ((Finset.Ico a (a + m ^ (n + 1))).filter (fun x => x.Coprime (m ^ (n + 1)))).card =
      m ^ n * m.totient := by
  have hf : ((Finset.Ico a (a + m ^ (n + 1))).filter
      (fun x => x.Coprime (m ^ (n + 1)))) =
      ((Finset.Ico a (a + m ^ (n + 1))).filter (fun x => (m ^ (n + 1)).Coprime x)) := by
    exact Finset.filter_congr (fun _ _ => Nat.coprime_comm)
  rw [hf]
  rw [Nat.filter_coprime_Ico_eq_totient, totient_channel_pow]

end
end GaloisForLFunctions.HTGeometry
