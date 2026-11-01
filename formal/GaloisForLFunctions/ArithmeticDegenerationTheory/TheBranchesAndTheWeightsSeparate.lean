import GaloisForLFunctions.ArithmeticDegenerationTheory.TheScalingFormOfTheDegeneration
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheRescaledLimitTensorizesOverThePrimes

/-!
# The branches and the weights separate

The degeneration of the complete Weil family has the scaling form
`E_m(c) = J(m) c⁻⁷ R_m(c/m)` (`TheScalingFormOfTheDegeneration`). This file shows that its two
factors read two different pieces of the conductor:

* **The scaling function reads the branches** (`scalingFunction_eq_of_primeFactors_eq`): `R_m`
  depends on `m` only through its set of prime factors — which branches of the prime cone the
  conductor lies on. Coprimality to `m` is coprimality to its radical.
* **The Jordan coefficient reads the weights**: along each branch it records the position in the
  weight string (`TheWeightStringsOfTheRescaledLimit`), and over the branches it multiplies
  (`TheRescaledLimitTensorizesOverThePrimes`).
* **Prime powers** (`completedConductorEnergy_prime_pow_eq`): for `a ≥ 1`,
  `c⁷ E_{p^a}(c) = J(1) [8]_p p^{7(a−1)} R_p(c/p^a)`: the whole `p`-tower degenerates along one
  scaling function `R_p`, sampled at `c/p^a`, with the string weights as prefactors.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- Coprimality to `m` depends only on the prime factors of `m`. -/
theorem coprime_iff_of_primeFactors_eq {m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : m.primeFactors = m'.primeFactors) (n : ℕ) : Nat.Coprime m n ↔ Nat.Coprime m' n := by
  have key : ∀ {a b : ℕ}, a ≠ 0 → b.primeFactors = a.primeFactors → Nat.Coprime a n →
      Nat.Coprime b n := by
    intro a b ha hab hcop
    refine Nat.coprime_of_dvd fun k hk hkb hkn => ?_
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ha (by simpa using hab.symm)
    have hka : k ∣ a := by
      have : k ∈ b.primeFactors := hk.mem_primeFactors hkb hb
      rw [hab] at this
      exact (Nat.mem_primeFactors.mp this).2.1
    exact hk.one_lt.ne' (Nat.eq_one_of_self_dvd_one (by
      rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd hka hkn))
  exact ⟨key hm h.symm, key hm' h⟩

/-- **The scaling function reads only the branches.** Two conductors with the same prime factors
have the same scaling function. -/
theorem scalingFunction_eq_of_primeFactors_eq {m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : m.primeFactors = m'.primeFactors) (x : ℝ) :
    scalingFunction m x = scalingFunction m' x := by
  have hc := coprime_iff_of_primeFactors_eq hm hm' h
  simp only [scalingFunction, shellAverage, coprimeZetaSum, hc]

/-- **A tower degenerates along one scaling function.** For `a ≥ 1` and `c > 0`,
`c⁷ E_{p^a}(c) = J(1) [8]_p p^{7(a−1)} R_p(c/p^a)`. -/
theorem completedConductorEnergy_prime_pow_eq {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a)
    {c : ℝ} (hc : 0 < c) :
    c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c (p ^ a) =
      jordanCoefficient 1 * pInteger p * (p : ℝ) ^ (7 * (a - 1)) *
        scalingFunction p (c / (p ^ a : ℕ)) := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  rw [rpow_seven_mul_completedConductorEnergy_eq_scaling hc hpa, jordanCoefficient_prime_pow hp ha,
    scalingFunction_eq_of_primeFactors_eq (pow_pos hp.pos a).ne' hp.ne_zero
      (by rw [Nat.primeFactors_prime_pow (by omega) hp, Nat.Prime.primeFactors hp])]

end GaloisForLFunctions.ArithmeticDegenerationTheory
