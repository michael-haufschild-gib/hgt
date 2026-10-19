import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiFinitePrimeAntichainBound
import GaloisForLFunctions.RHTower.Sieve.DampedCorrExp

/-!
# Bounded reciprocal prime capacity gives native Fermi observability

The existing corpus Euler-correction estimate turns the finite-prime bound into
`8 * exp(6*M)` when allowed reciprocal-prime subsums are bounded by `M`. The
finite prime set is the union of the prime supports of the chosen odd indices.

This is the quantitative forward bound for parameterized native antichains.
The arbitrary-support equivalence and divergent-capacity physical
counterexample construction remain unfinished parts of the programme.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- Finite reciprocal-prime mass gives the explicit physical constant `8 * exp(6*M)`. -/
theorem fermiDyadicAntichain_reciprocalPrime_physical_bound (N : ℕ) (P S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ d ∈ S, Odd d) (hSP : ∀ d ∈ S, d.primeFactors ⊆ P)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (M : ℝ)
    (hM : ∑ p ∈ P, 1/(p : ℝ) ≤ M) :
    sieveTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) ≤
      8*Real.exp (6*M)*fermiSelectedTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) := by
  let B : ℝ := ∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1)
  have hB0 : 0 ≤ B := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
    exact div_nonneg (by positivity) (by linarith)
  have hc : RHTower.Sieve.dampedCorrBound P 1 = B := by
    unfold RHTower.Sieve.dampedCorrBound B
    apply Finset.prod_congr rfl
    intro p hp
    rw [Real.rpow_neg_one]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    have hp1 : (p : ℝ)-1 ≠ 0 := by
      have : 1 < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
      linarith
    field_simp
  have he := RHTower.Sieve.dampedCorrBound_le_exp (fun p hp => (hP p hp).two_le) (c := 1) le_rfl
  rw [hc] at he
  simp only [Real.rpow_neg_one] at he
  have hB : B ≤ Real.exp (3*M) := he.trans (Real.exp_le_exp.mpr (by
    simpa only [one_div] using mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ 3 by norm_num)))
  have hB2 : B^2 ≤ Real.exp (6*M) := by
    calc
      _ ≤ (Real.exp (3*M))^2 := pow_le_pow_left₀ hB0 hB 2
      _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hQ : 0 ≤ fermiSelectedTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) := by
    unfold fermiSelectedTotalPronicEnergy
    apply tsum_nonneg
    intro m
    unfold fermiSelectedPronicEnergy
    apply Finset.sum_nonneg
    intro k _
    positivity
  exact (fermiDyadicAntichain_finitePrime_physical_bound N P S j a hP hS hSP hN).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB2 (by norm_num)) hQ)

/-- Finite reciprocal capacity gives one native constant for every packet and every horizon. -/
theorem fermiDyadicAntichain_boundedCapacity_physical_bound
    (allowed : Set ℕ) (hallowed : ∀ p ∈ allowed, p.Prime ∧ Odd p) (M : ℝ)
    (hcap : ∀ P : Finset ℕ, (∀ p ∈ P, p ∈ allowed) → (∑ p ∈ P, 1/(p : ℝ)) ≤ M)
    (N : ℕ) (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ)
    (hS : ∀ d ∈ S, Odd d) (hSP : ∀ d ∈ S, ∀ p ∈ d.primeFactors, p ∈ allowed)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) :
    sieveTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) ≤
      8*Real.exp (6*M)*fermiSelectedTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) := by
  let P := S.biUnion Nat.primeFactors
  have hPallowed (p : ℕ) (hp : p ∈ P) : p ∈ allowed := by
    obtain ⟨d, hd, hpd⟩ := Finset.mem_biUnion.mp hp
    exact hSP d hd p hpd
  exact fermiDyadicAntichain_reciprocalPrime_physical_bound N P S j a
    (fun p hp => (hallowed p (hPallowed p hp)).1) hS
    (fun d hd => Finset.subset_biUnion_of_mem Nat.primeFactors hd) hN M (hcap P hPallowed)

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
