import GaloisForLFunctions.RHTower.Sieve.CoprimeCounting

/-!
# Peeling one prime off a coprimality class

Splitting the residues coprime to `e` according to divisibility by a prime `p` is the first step of
the prime-peeling recursion, which is the mechanism that produces cancellation *across* the divisors
of the modulus — the ingredient the two retired routes (bricks 31 and 38) lacked.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The prime split of a coprimality class.** -/
theorem sum_filter_coprime_split {p e y : ℕ} (hp : p.Prime) (g : ℕ → ℝ) :
    ∑ j ∈ (Finset.Icc 1 y).filter (fun j => Nat.Coprime e j), g j
      = (∑ j ∈ (Finset.Icc 1 y).filter (fun j => Nat.Coprime (p * e) j), g j)
        + ∑ j ∈ (Finset.Icc 1 y).filter (fun j => Nat.Coprime e j ∧ p ∣ j), g j := by
  classical
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 y).filter (fun j => Nat.Coprime e j)) (fun j => Nat.Coprime p j) g).symm
  rw [hsplit]
  congr 1
  · congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, hce⟩, hcp⟩
      exact ⟨hj, Nat.Coprime.mul_left hcp hce⟩
    · rintro ⟨hj, hc⟩
      obtain ⟨hcp, hce⟩ := Nat.coprime_mul_iff_left.mp hc
      exact ⟨⟨hj, hce⟩, hcp⟩
  · congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, hce⟩, hnc⟩
      exact ⟨hj, hce, not_not.mp (fun h => hnc (hp.coprime_iff_not_dvd.mpr h))⟩
    · rintro ⟨hj, hce, hdvd⟩
      exact ⟨⟨hj, hce⟩, fun hc => (hp.coprime_iff_not_dvd.mp hc) hdvd⟩

end RHTower.Sieve
