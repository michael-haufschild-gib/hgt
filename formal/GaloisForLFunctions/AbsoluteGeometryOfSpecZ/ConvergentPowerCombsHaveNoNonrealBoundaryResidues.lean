import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerCombConvergencePaysContactAsymptotics
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PowerAsymptoticsHaveNoNonrealBoundaryResidues

/-!
# Nonreal boundary residues of convergent power combs vanish

The contact asymptotic supplied by the literal comb is a convergent
logarithmic profile. Its nonresonant Abel limit excludes a pole residue
at every nonzero frequency on the critical contact line.
-/

noncomputable section

open Finset Filter Topology Complex

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- The summatory weighted prime contacts. -/
def powerContactPrefix (a : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n

/-- Every nonreal boundary residue vanishes if the literal power comb converges. -/
theorem tendsto_mul_powerContactMellin_of_powerCombTailConverges
    {a τ : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hτ : τ ≠ 0)
    (hc : PowerCombTailConverges a) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      complexMellinPairing (powerContactPrefix a)
        (((1 - 2 * a + ε : ℝ) : ℂ) + (τ : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL⟩ :=
    (powerCombTailConverges_iff_normalizedPowerContacts_converges ha ha2).mp hc
  apply tendsto_mul_complexMellinPairing_at_nonreal_boundary
    (by simp [powerContactPrefix]) (by linarith only [ha2]) hτ
  apply hL.congr
  intro N
  change (N : ℝ) ^ (2 * a - 1) * powerContactPrefix a N =
    (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N
  rw [show -(1 - 2 * a) = 2 * a - 1 by ring]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
