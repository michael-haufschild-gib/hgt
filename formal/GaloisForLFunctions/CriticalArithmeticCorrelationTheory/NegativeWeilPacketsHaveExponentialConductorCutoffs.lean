import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilReserveHasPolynomialOverlapCost
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasAnExponentialConductorCutoff

/-!
# Conductor confinement of nonpositive complete Weil packets

The polynomial overlap cost of the complete signed source bounds prime defect.
Exponential defect confinement then gives one finite conductor cutoff for every
unit packet of nonpositive energy, uniformly over the allowed horizons.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics

/-- Nonpositive complete packets admit a conductor cutoff exponential in `c¹⁶`. -/
theorem exists_negative_completeWeil_exponential_conductor_cutoff
    {η : ℝ} (hη : 0 < η) :
    ∃ C D H : ℝ, 0 < C ∧ 0 < D ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∃ R : ℕ,
        (R : ℝ) ≤ Real.exp (D * (C * c ^ 16 + 1)) ∧
        ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ‖x‖ = 1 →
            completeWeilEnergy tiltedUnitSpline c N x ≤ 0 →
            ∃ b : ℕ → ℝ,
              (∑ n ∈ Icc 1 N,
                (primeHorizonExtension x n -
                  ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  obtain ⟨C, H, hC, hH, hdef⟩ :=
    exists_negative_completeWeil_poleDefect_polynomial_bound
  obtain ⟨D, hD, happrox⟩ := exists_exponential_conductor_cutoff_of_poleDefect_le hη
  refine ⟨C, D, H, hC, hD, hH, fun c hc => ?_⟩
  obtain ⟨R, hR, hcut⟩ := happrox (C * c ^ 16) (by positivity)
  refine ⟨R, hR, fun N hN x hx he => ?_⟩
  apply hcut N (primeHorizonExtension x) _ (hdef c hc N hN x hx he)
  rw [sum_primeHorizonExtension_sq, hx, one_pow]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_negative_completeWeil_exponential_conductor_cutoff
