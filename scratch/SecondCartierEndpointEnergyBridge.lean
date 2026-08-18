import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

def testEndpointEnergy (lam c : ℂ) (n : ℕ) : ℝ :=
  ‖bilateralEigenFamily lam (-(n : ℤ))‖ ^ 2 +
    4 * ‖c * bilateralEigenFamily lam (n : ℤ)‖ ^ 2

theorem testEndpointEnergy_eq (lam c : ℂ) (n : ℕ) :
    testEndpointEnergy lam c n =
      sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n) := by
  rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy]
  simp [testEndpointEnergy, bilateralEigenFamily, pow_mul]
  ring

theorem testBounded_iff_moderate
    {c₀ lam : ℂ} {N : ℕ}
    (hscale : sourceHorizontalWoldBVKreinGhostEnergy c₀ N ≠ 0)
    (hlam : lam ≠ 0) :
    SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded lam
        (sourceHorizontalWoldBVKreinGhostEnergy c₀ N : ℂ) ↔
      bilateralModerate
        (sourceHorizontalEndpointSecondJetHardyDescent c₀ N lam
          sourceHorizontalBilateralSecondJetGhost) := by
  rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff
      hlam (by exact_mod_cast hscale),
    sourceHorizontalEndpointSecondJetHardyDescent_ghost_moderate_iff hscale hlam]

theorem testActualEnergy
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) (n : ℕ) :
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
          (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n) =
      ‖bilateralEigenFamily
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) (-(n : ℤ))‖ ^ 2 +
        4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) (n : ℤ)‖ ^ 2 := by
  rw [← testEndpointEnergy_eq
    (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n]
  simp only [testEndpointEnergy]
  congr 2
  rw [sourceHorizontalActualXiEndpointSecondJetHardyDescent]
  change _ = ‖(sourceHorizontalWoldBVKreinGhostEnergy
      (sourceHorizontalActualXiConormalCoefficient x u q r) N : ℂ) *
        sourceHorizontalBilateralSecondJetHardyDescent
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
          sourceHorizontalBilateralSecondJetGhost (n : ℤ)‖ ^ 2
  rw [sourceHorizontalBilateralSecondJetHardyDescent_ghost]
  simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
    sourceHorizontalActualXiSecondCartierKreinScale, bilateralEigenFamily]

theorem testActualBounded_iff_endpointModerate
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    SourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded x u q r N p ↔
      bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) := by
  have hscaleC := sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
    q hkappa hr N hjet
  have hscale : sourceHorizontalWoldBVKreinGhostEnergy
      (sourceHorizontalActualXiConormalCoefficient x u q r) N ≠ 0 := by
    rw [sourceHorizontalActualXiSecondCartierKreinScale] at hscaleC
    exact_mod_cast hscaleC
  exact testBounded_iff_moderate hscale
    (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p)

end

end RHTower
