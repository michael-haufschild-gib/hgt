import GaloisForLFunctions.RHTower.WoldEulerActivationHolonomy
import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization

/-!
# Euler activation, squarefree occupancy, and valuation depth

The diagonal Wold--Euler activation holonomy is the squarefree partition
`ζ(s) / ζ(2s)`.  Its local positive-depth masses form a zero-modified
geometric law.  The occupancy marginal is the squarefree Bernoulli law,
while conditional positive valuation is geometric.

At unit aperture, these positive-depth masses are exactly the Möbius
Schur forward differences already selected by the source.  Their damping
square is the squarefree occupancy Fisher variance, and removing that
damping recovers the Gamma-selected half-shifted valuation frame.

The results are unconditional scalar and Euler-half-plane identities.
They do not assert that the radical conditional expectation remains
completely contractive after Gamma/co-Poisson continuation to the Xi
divisor.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive valuation atom of the normalized diagonal activation law. -/
def diagonalActivationPositiveValuationMass (q : ℝ) (e : ℕ) : ℝ :=
  (1 - q) * q ^ (e + 1) / (1 + q)

/-- Occupancy probability of the diagonal activation law. -/
def diagonalActivationOccupancyProbability (q : ℝ) : ℝ :=
  q / (1 + q)

/-- Conditional valuation law after a prime is occupied. -/
def diagonalActivationConditionalValuationMass (q : ℝ) (e : ℕ) : ℝ :=
  (1 - q) * q ^ e

/-- Fisher information of the local occupancy bit in logarithmic scale. -/
def diagonalActivationOccupancyFisher (q : ℝ) : ℝ :=
  q / (1 + q) ^ (2 : ℕ)

/-- The positive-depth atom factors into occupancy and conditional valuation. -/
theorem diagonalActivationPositiveValuationMass_factorization
    {q : ℝ} (hq : 0 ≤ q) (_hq1 : q < 1) (e : ℕ) :
    diagonalActivationPositiveValuationMass q e =
      diagonalActivationOccupancyProbability q *
        diagonalActivationConditionalValuationMass q e := by
  have hplus : 1 + q ≠ 0 := by linarith
  simp only [diagonalActivationPositiveValuationMass,
    diagonalActivationOccupancyProbability,
    diagonalActivationConditionalValuationMass, pow_succ]
  field_simp [hplus]

/-- All positive valuation atoms sum to the occupancy probability. -/
theorem tsum_diagonalActivationPositiveValuationMass
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' e : ℕ, diagonalActivationPositiveValuationMass q e) =
      diagonalActivationOccupancyProbability q := by
  have hminus : 1 - q ≠ 0 := by linarith
  have hplus : 1 + q ≠ 0 := by linarith
  calc
    (∑' e : ℕ, diagonalActivationPositiveValuationMass q e) =
        ∑' e : ℕ, (q * (1 - q) / (1 + q)) * q ^ e := by
      apply tsum_congr
      intro e
      simp only [diagonalActivationPositiveValuationMass, pow_succ]
      ring
    _ = (q * (1 - q) / (1 + q)) * ∑' e : ℕ, q ^ e := by
      rw [tsum_mul_left]
    _ = (q * (1 - q) / (1 + q)) * (1 - q)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq hq1]
    _ = diagonalActivationOccupancyProbability q := by
      simp only [diagonalActivationOccupancyProbability]
      field_simp [hminus, hplus]

/-- The zero atom and all positive-depth atoms have total mass one. -/
theorem diagonalActivationValuationMass_total
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    1 / (1 + q) +
        ∑' e : ℕ, diagonalActivationPositiveValuationMass q e = 1 := by
  rw [tsum_diagonalActivationPositiveValuationMass hq hq1]
  have hplus : 1 + q ≠ 0 := by linarith
  simp only [diagonalActivationOccupancyProbability]
  field_simp [hplus]

/-- The occupancy Fisher information is its Bernoulli variance. -/
theorem diagonalActivationOccupancyFisher_eq_variance
    {q : ℝ} (hq : 0 ≤ q) (_hq1 : q < 1) :
    diagonalActivationOccupancyFisher q =
      diagonalActivationOccupancyProbability q *
        (1 - diagonalActivationOccupancyProbability q) := by
  have hplus : 1 + q ≠ 0 := by linarith
  simp only [diagonalActivationOccupancyFisher,
    diagonalActivationOccupancyProbability]
  field_simp [hplus]
  ring

/-- The occupancy Fisher information is the existing squarefree-parity variance. -/
theorem diagonalActivationOccupancyFisher_eq_dyadicSquarefreeParityVariance
    (q : ℝ) :
    diagonalActivationOccupancyFisher q =
      dyadicSquarefreeParityVariance q := by
  rfl

/-- The diagonal activation holonomy is exactly the squarefree partition. -/
theorem woldActivationHolonomy_diagonal_eq_squarefreePartition
    (s : ℂ) :
    woldActivationHolonomy s s =
      GaloisForLFunctions.squarefreePartition s := by
  simp only [woldActivationHolonomy,
    GaloisForLFunctions.squarefreePartition]
  congr 2
  ring

/-- At a rational prime, the literal positive valuation atom is the Möbius Schur
forward difference. -/
theorem diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference
    (p : Nat.Primes) (e : ℕ) :
    diagonalActivationPositiveValuationMass
        (xiTransversePrimeApertureDiskNode 1 p) e =
      xiMobiusPrimeSchurForwardDifference p e := by
  rw [xiMobiusPrimeSchurForwardDifference_eq_geometric]
  simp only [diagonalActivationPositiveValuationMass]
  ring

/-- The Möbius depth atom is the Fisher-damped Gamma valuation coordinate. -/
theorem diagonalActivationPrimeMass_eq_fisherDampedGammaValuation
    (p : Nat.Primes) (e : ℕ) :
    diagonalActivationPositiveValuationMass
        (xiTransversePrimeApertureDiskNode 1 p) e =
      xiMobiusPrimeSchurValuationDamping p *
        xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  rw [diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference,
    xiMobiusPrimeSchurForwardDifference_eq_dampedValuation]

/-- The square of the prime damping is exactly occupancy Fisher information. -/
theorem xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p ^ (2 : ℕ) =
      diagonalActivationOccupancyFisher
        (xiTransversePrimeApertureDiskNode 1 p) := by
  rw [diagonalActivationOccupancyFisher_eq_dyadicSquarefreeParityVariance]
  simpa [primeSchurWeight_one_eq_xiTransversePrimeApertureDiskNode] using
    xiMobiusPrimeSchurValuationDamping_sq_eq_parityVariance p

/-- The completed Xi/squarefree current correction is the diagonal normal
connection of the same activation source. -/
theorem completedXi_sub_completedSquarefree_eq_activationNormalConnection
    {s : ℂ} (hs : 1 < s.re) :
    2 * seamFluxCochain s -
        GaloisForLFunctions.completedSquarefreeFixedCurrent s =
      4 * infinitePrimeFlux (s + s) := by
  have h :=
    GaloisForLFunctions.completedXi_sub_completedSquarefree_eq_four_mul_infinitePrimeFlux_two
      hs
  simpa [two_mul] using h

/-- Certificate collecting the literal diagonal source, occupancy law, Möbius atoms,
Fisher damping, Gamma valuation fibre, and completed-current normal correction. -/
structure EulerActivationSquarefreeDisintegrationCertificate (s : ℂ) : Prop where
  diagonalSource :
    woldActivationHolonomy s s =
      GaloisForLFunctions.squarefreePartition s
  localMass :
    ∀ (p : Nat.Primes) (e : ℕ),
      diagonalActivationPositiveValuationMass
          (xiTransversePrimeApertureDiskNode 1 p) e =
        xiMobiusPrimeSchurForwardDifference p e
  fisherDampedGamma :
    ∀ (p : Nat.Primes) (e : ℕ),
      diagonalActivationPositiveValuationMass
          (xiTransversePrimeApertureDiskNode 1 p) e =
        xiMobiusPrimeSchurValuationDamping p *
          xiTransversePrimeHalfShiftedValuationCoordinate p e
  dampingFisher :
    ∀ p : Nat.Primes,
      xiMobiusPrimeSchurValuationDamping p ^ (2 : ℕ) =
        diagonalActivationOccupancyFisher
          (xiTransversePrimeApertureDiskNode 1 p)
  currentNormal :
    2 * seamFluxCochain s -
        GaloisForLFunctions.completedSquarefreeFixedCurrent s =
      4 * infinitePrimeFlux (s + s)

/-- The source laws form one unconditional Euler activation disintegration. -/
theorem eulerActivationSquarefreeDisintegration_law
    {s : ℂ} (hs : 1 < s.re) :
    EulerActivationSquarefreeDisintegrationCertificate s where
  diagonalSource :=
    woldActivationHolonomy_diagonal_eq_squarefreePartition s
  localMass :=
    diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference
  fisherDampedGamma :=
    diagonalActivationPrimeMass_eq_fisherDampedGammaValuation
  dampingFisher :=
    xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher
  currentNormal :=
    completedXi_sub_completedSquarefree_eq_activationNormalConnection hs

end

end RHTower
