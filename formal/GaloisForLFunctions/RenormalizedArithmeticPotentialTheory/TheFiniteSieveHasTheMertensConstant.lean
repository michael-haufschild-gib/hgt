import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasOneEulerConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTheTowerForm

/-!
# The Mertens constant of a finite sieve

A nonzero von Mangoldt term is supported on one prime. Deleting a prime therefore
removes its entire geometric tail, independently of all previous deletions.
The harmonic and Mertens constants are the same sieve Euler constant, with
opposite signs after density normalization.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry

/-- The von Mangoldt harmonic sum on units of a finite prime sieve. -/
def sievedMertensSum (Q : Finset Nat.Primes) (N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => Nat.Coprime n (sievePrimorial Q)),
    ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- A prime deletion removes exactly that prime's geometric Mertens tail. -/
theorem sievedMertensSum_insert {Q : Finset Nat.Primes} {p : Nat.Primes}
    (hp : p ∉ Q) (N : ℕ) :
    sievedMertensSum (insert p Q) N = sievedMertensSum Q N - pPowerMertensSum p N := by
  rw [sievedMertensSum, sievedMertensSum, pPowerMertensSum,
    sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, zero_div, ite_self, sub_self]
  by_cases hpd : (p : ℕ) ∣ n
  · have hcop : Nat.Coprime n (sievePrimorial Q) := by
      obtain ⟨q, r, hq, _, hpow⟩ :=
        (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpq : (p : ℕ) ∣ q := p.2.dvd_of_dvd_pow (by rw [hpow]; exact hpd)
      have hqp : q = (p : ℕ) := by
        rcases (Nat.dvd_prime hq).mp hpq with h | h
        · exact (p.2.ne_one h).elim
        · exact h.symm
      rw [← hpow, hqp]
      exact (coprime_sievePrimorial hp).pow_left r
    have hnot : ¬ Nat.Coprime n (sievePrimorial (insert p Q)) := by
      rw [coprime_sievePrimorial_insert_iff hp]
      exact fun h => h.2 hpd
    rw [if_neg hnot, if_pos hcop, if_pos hpd, sub_self]
  · simp only [coprime_sievePrimorial_insert_iff hp, hpd,
      not_false_eq_true, and_true, if_false, sub_zero]

/-- The finite sieve has Mertens constant minus its shared Euler constant. -/
theorem tendsto_sievedMertensSum_sub_log (Q : Finset Nat.Primes) :
    Tendsto (fun N : ℕ => sievedMertensSum Q N - Real.log N) atTop
      (𝓝 (-sieveEuler Q)) := by
  classical
  induction Q using Finset.induction with
  | empty =>
      simpa [sievedMertensSum, mertensSum] using tendsto_mertensSum_sub_log
  | insert p Q hp ih =>
      have h := ih.sub (tendsto_pPowerMertensSum p.2)
      have hvalue : -sieveEuler Q - Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1) =
          -sieveEuler (insert p Q) := by
        rw [sieveEuler_insert hp]
        ring
      rw [hvalue] at h
      refine h.congr fun N => ?_
      rw [sievedMertensSum_insert hp]
      ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

