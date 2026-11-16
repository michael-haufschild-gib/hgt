import GaloisForLFunctions.SelbergClass.DirichletSeries.DistinctPrimeSign
import GaloisForLFunctions.RHTower.Sieve.HarmonicWeightedGrahamMeanSquare

/-!
# Exact incidence energy of the distinct-prime sign

The squarefree coefficient `μ(d) 2^ω(d)` has divisor response `(-1)^ω(n)`.
Its response therefore has unit squared magnitude at every positive integer.
The weighted Graham identity turns this pointwise law into an exact
evaluation of the signed lcm quadratic form at every horizon.
-/

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

open ArithmeticFunction Finset

/-- The squarefree divisor source for distinct-prime parity. -/
def distinctPrimeParitySource (d : ℕ) : ℝ :=
  (moebius d : ℝ) * 2 ^ d.primeFactors.card

/-- The divisor response is a sign, including at nonsquarefree integers. -/
theorem distinctPrimeParitySource_response (n : ℕ) :
    (∑ d ∈ (n + 1).divisors, distinctPrimeParitySource d) =
      (-1 : ℝ) ^ (n + 1).primeFactors.card := by
  simpa only [distinctPrimeParitySource, Finset.prod_const,
    show (1 : ℝ) - 2 = -1 by ring] using
    SelbergClass.sum_divisors_squarefreePrimeWeight (fun _ => (2 : ℝ)) n

/-- Every positive integer has exactly one unit of response energy. -/
theorem distinctPrimeParitySource_response_sq (n : ℕ) :
    (∑ d ∈ (n + 1).divisors, distinctPrimeParitySource d) ^ 2 = 1 := by
  rw [distinctPrimeParitySource_response, ← pow_mul, Nat.mul_comm, pow_mul]
  simp only [neg_one_sq, one_pow]

/-- The signed lcm incidence energy equals the total observation weight. -/
theorem distinctPrimeParitySource_lcm_energy (N : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
      distinctPrimeParitySource p.1 * distinctPrimeParitySource p.2 *
        ∑ k ∈ (Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), w k) =
      ∑ k ∈ Icc 1 N, w k := by
  rw [← RHTower.Sieve.sum_weighted_sq_divisorSum_eq_lcm_quadratic]
  apply sum_congr rfl
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (mem_Icc.mp hk).1)
  rw [distinctPrimeParitySource_response_sq, mul_one]

/-- Counting measure gives the exact energy `N`. -/
theorem distinctPrimeParitySource_counting_energy (N : ℕ) :
    (∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
      distinctPrimeParitySource p.1 * distinctPrimeParitySource p.2 *
        ((Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k)).card) = (N : ℝ) := by
  simpa using distinctPrimeParitySource_lcm_energy N (fun _ => 1)

/-- Harmonic observation gives the harmonic mass exactly. -/
theorem distinctPrimeParitySource_harmonic_energy (N : ℕ) :
    (∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
      distinctPrimeParitySource p.1 * distinctPrimeParitySource p.2 *
        ∑ k ∈ (Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ)) =
      ∑ k ∈ Icc 1 N, 1 / (k : ℝ) :=
  distinctPrimeParitySource_lcm_energy N _

#print axioms distinctPrimeParitySource_lcm_energy
#print axioms distinctPrimeParitySource_counting_energy
#print axioms distinctPrimeParitySource_harmonic_energy

end GaloisForLFunctions.BezoutValuationIncidence
