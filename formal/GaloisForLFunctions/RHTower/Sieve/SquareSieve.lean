import GaloisForLFunctions.RHTower.Sieve.SieveBound

/-!
# A set omitting half the classes is small

The sieve is sharpest when the omitted proportion is bounded away from zero.  If `A` misses at least
half the residue classes modulo each prime of a family `P` — the situation of a set of quadratic
residues, or of any set defined by a congruence obstruction of density `1/2` — then each term of the
sieve sum is at least `1/3`, so

`|A| ≤ 3 (N + Q²(1 + log(Q²/2 + 1))) / |P|`.

The constant `1/3` is the value of `w/(p - w)` at `w = (p-1)/2`, `p = 2`, and improves to `1` as `p`
grows; no prime counting is involved, only the size of `P`.
-/

namespace RHTower.Sieve

open Finset

/-- Omitting half the classes makes the deficiency ratio at least `1/3`. -/
theorem third_le_ratio {p w : ℝ} (hp : 2 ≤ p) (hhalf : (p - 1) / 2 ≤ w) (hwp : w < p) :
    (1 : ℝ) / 3 ≤ w / (p - w) := by
  have hpos : (0 : ℝ) < p - w := by linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- **A set omitting half the classes modulo each prime of `P` is small.** -/
theorem card_le_of_half_omitted (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hPne : P.Nonempty) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hhalf : ∀ p ∈ P, ((p : ℝ) - 1) / 2 ≤ w p)
    (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ)) :
    (A.card : ℝ)
      ≤ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2 + 1))) / (P.card : ℝ) := by
  have hPcard : (0 : ℝ) < (P.card : ℝ) := by
    have := Finset.card_pos.mpr hPne
    exact_mod_cast this
  have hratio : ∀ p ∈ P, (1 : ℝ) / 3 ≤ w p / ((p : ℝ) - w p) := by
    intro p hp
    obtain ⟨hprime, _⟩ := hP p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    exact third_le_ratio hp2 (hhalf p hp) (hwp p hp)
  have hL : (P.card : ℝ) / 3 ≤ ∑ p ∈ P, w p / ((p : ℝ) - w p) := by
    have hconst : ∑ _p ∈ P, (1 : ℝ) / 3 = (P.card : ℝ) / 3 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [← hconst]
    exact Finset.sum_le_sum hratio
  have hLpos : (0 : ℝ) < (P.card : ℝ) / 3 := by positivity
  have hbase := card_le_of_sieve N hQ A hA hAne P hP w hwp hocc hLpos hL
  have heq : ((N : ℝ) + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2 + 1))) / ((P.card : ℝ) / 3)
      = 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2 + 1))) / (P.card : ℝ) := by
    rw [div_div_eq_mul_div, mul_comm]
  rw [heq] at hbase
  exact hbase

end RHTower.Sieve
