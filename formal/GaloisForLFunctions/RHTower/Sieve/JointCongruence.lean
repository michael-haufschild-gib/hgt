import GaloisForLFunctions.RHTower.Sieve.ShiftedCongruenceCount

/-!
# The two congruences of a shifted correlation have a common solution

A shifted correlation weighted by the squarefree identity meets the pair of conditions

`d² ∣ n`  and  `e² ∣ n + h`.

For coprime moduli the Chinese remainder theorem supplies a common solution, so the pair cuts out a
single residue class and its count in a window is governed by the single-congruence bound of the
previous module.

Here the existence of the common solution is established; the residue `-h` modulo `b` is realised as
the natural number `(b - h % b) % b`.
-/

namespace RHTower.Sieve

open Finset

/-- The natural representative of `-h` modulo `b`. -/
def negShift (b h : ℕ) : ℕ := (b - h % b) % b

/-- `negShift b h + h` is divisible by `b`. -/
theorem negShift_add_dvd {b : ℕ} (hb : 0 < b) (h : ℕ) : b ∣ (negShift b h + h) := by
  have hr : h % b < b := Nat.mod_lt _ hb
  have hdm : b * (h / b) + h % b = h := Nat.div_add_mod h b
  have key : b ∣ ((b - h % b) + h) := by
    refine ⟨1 + h / b, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    have h1 : (b - h % b) + h = (b - h % b) + (b * (h / b) + h % b) := by rw [hdm]
    rw [h1, ← Nat.add_assoc, Nat.add_comm (b - h % b) (b * (h / b)), Nat.add_assoc,
      Nat.sub_add_cancel (le_of_lt hr), Nat.add_comm]
  have hmod : (negShift b h + h) % b = ((b - h % b) + h) % b := by
    rw [negShift, Nat.mod_add_mod]
  rw [Nat.dvd_iff_mod_eq_zero, hmod, ← Nat.dvd_iff_mod_eq_zero]
  exact key

/-- **The two congruences have a common solution.** -/
theorem exists_joint_solution {a b : ℕ} (hb : 0 < b) (hab : Nat.Coprime a b) (h : ℕ) :
    ∃ n₀ : ℕ, a ∣ n₀ ∧ b ∣ (n₀ + h) := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hab 0 (negShift b h)
  refine ⟨k, ?_, ?_⟩
  · exact (Nat.modEq_zero_iff_dvd).mp hk1
  · have hstep : (k + h) ≡ (negShift b h + h) [MOD b] := Nat.ModEq.add_right h hk2
    exact (Nat.modEq_zero_iff_dvd).mp
      (hstep.trans ((Nat.modEq_zero_iff_dvd).mpr (negShift_add_dvd hb h)))

end RHTower.Sieve
