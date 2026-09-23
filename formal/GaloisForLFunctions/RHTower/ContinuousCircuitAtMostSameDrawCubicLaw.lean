import GaloisForLFunctions.RHTower.ContinuousExactCircuitSameDrawCubicLaw
import GaloisForLFunctions.HTGeometry.TwoQubitCircuitIdentityPaddingLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix Set Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

noncomputable section

attribute [local instance] Classical.propDecidable

theorem exists_pairQubitProjective_growth_noContinuousCircuitAtMostReturn
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    (s : ℕ) {r : ℕ} (hr : 0 < r) {delta kappa : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 < kappa)
    {guard eta returnRadius thetaN thetaW radius : ℝ}
    (hguard : 0 ≤ guard)
    (hTpos : 0 < 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)
    (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hradius : 0 < radius)
    (hmeshReturn : thetaN - thetaW ≤ returnRadius)
    (hreturnT : returnRadius ≤ 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)
    (hguardStart : guard ≤ returnRadius)
    (hscalarBudget :
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
          (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) +
        (2 * Real.pi * (L : ℝ) ^ (3 : ℕ)) *
          (rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ (3 : ℕ))) < eta)
    (hselect : pairQubitWeakTwoLocalGrowthFailureBudget L +
        Real.exp (-twoLocalAnchorTransverseUniformRate (L * 2) r scale
          (pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale)) /
            kappa < 1)
    (hmoment :
      ((((L * 2) * (L * 2)) ^ s * (r * s + 1) ^ (s * 16) + 1 : ℕ) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          kappa +
          Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) /
              pairQubitProjectiveStaticChoiSpeedCeiling L rho scale) /
            (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
              (thetaW ^ (2 : ℕ)) ^ r) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ∧
      ¬ ∃ t ∈ Icc
          (returnRadius + (thetaN - thetaW) /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
          (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard),
        ∃ U ∈ TwoQubitArchitecture.circuitImageAtMost (L * 2) s,
          eta + thetaN + radius ≤ ‖inner ℂ
            (staticSpectralChoiVector
              (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
            (GaloisForLFunctions.RHTower.choiVector
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
                L p scale x
                  (unitaryGroupReindex
                    (pairQubitPathConfigurationEquiv L).symm U) :
                Matrix (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2)))))
                  (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))‖ := by
  obtain ⟨x, hx, hmax, hnoExact⟩ :=
    exists_pairQubitProjective_growth_noContinuousExactCircuitReturn hL hp hrho
      hseed hscale s hr hdelta hkappa hguard hTpos hreturnPos hthetaW hgap
      hradius hmeshReturn hreturnT hguardStart hscalarBudget hselect hmoment
  refine ⟨x, hx, hmax, ?_⟩
  rintro ⟨t, ht, U, hU, hhit⟩
  apply hnoExact
  exact ⟨t, ht, U, circuitImageAtMost_subset_exact (by omega : 2 ≤ L * 2) hU, hhit⟩

end

end RHTower

