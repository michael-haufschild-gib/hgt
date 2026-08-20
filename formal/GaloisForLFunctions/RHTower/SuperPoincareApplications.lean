import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.RHTower.CCMPublishedRestrictedWeilParityBlocks
import GaloisForLFunctions.RHTower.CCMParityInvolutionGrading
import GaloisForLFunctions.RHTower.RankTwoCommutatorParityMultiplicityBalance
import GaloisForLFunctions.RHTower.RealCoronaQuaternionicCyclic
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseAnomalousDarboux

/-!
# Super-Poincare applications in RHTower

This module packages closed anticommuting operator pairs as dimensional reductions of the
Super-Poincare supertranslation algebra.  It also isolates the unconditional constant-polynomial
BPS state of the theta-cusp Morse factorization.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Real-corona grading and swap are unit-momentum `N = 2` supercharges. -/
def realCoronaMatrixD1N2 :
    SuperPoincare.D1N2 (Matrix (Fin 2) (Fin 2) ℂ) where
  supercharge0 := realCoronaMatrixGrading
  supercharge1 := realCoronaMatrixSwap
  momentum := 1
  supercharge0_sq := realCoronaMatrixGrading_sq
  supercharge1_sq := realCoronaMatrixSwap_sq
  mixed_anticommutator := by
    rw [realCoronaMatrixGrading_anticommutes_swap]
    exact neg_add_cancel _

/-- Residual branch sign and branch reflection give a unit-momentum `N = 2` sector. -/
def residualParityD1N2 (L : ℕ) :
    SuperPoincare.D1N2 (Module.End ℝ (Fin L × Bool → ℝ)) where
  supercharge0 := residualBranch L
  supercharge1 := residualParity L
  momentum := 1
  supercharge0_sq := by
    apply LinearMap.ext
    exact residualBranch_involutive L
  supercharge1_sq := by
    apply LinearMap.ext
    exact residualParity_involutive L
  mixed_anticommutator := by
    apply LinearMap.ext
    intro f
    change residualBranch L (residualParity L f) +
      residualParity L (residualBranch L f) = 0
    have h := residualBranch_anticommutes L f
    rw [residualBranchEquiv_apply] at h
    rw [h]
    exact neg_add_cancel _

end GaloisForLFunctions.RHTower

namespace RHTower

/-- CCM centered clock and parity reflection form a split-momentum `N = 2` sector. -/
def ccmParityClockReflectionD1N2Split (N : ℕ) :
    SuperPoincare.D1N2Split
      (Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) where
  supercharge0 := ccmParityClockMatrix N
  supercharge1 := ccmParityReflectionMatrix N
  mixed_anticommutator := by
    rw [ccmParityClockMatrix_anticommutes_reflection]
    exact neg_add_cancel _

/-- Reflection supplies the unit diagonal momentum in the CCM split sector. -/
theorem ccmParityClockReflection_momentum1_eq_one (N : ℕ) :
    (ccmParityClockReflectionD1N2Split N).momentum1 = 1 := by
  exact ccmParityReflectionMatrix_sq N

/-- Truncated frequency and reflection form a split-momentum `N = 2` sector. -/
def truncatedFrequencyReflectionD1N2Split (N : ℕ) :
    SuperPoincare.D1N2Split
      (Module.End ℝ (EuclideanSpace ℝ (Fin (2 * N + 1)))) where
  supercharge0 := truncatedFrequency N
  supercharge1 := truncatedReflection N
  mixed_anticommutator := by
    apply LinearMap.ext
    intro f
    change truncatedFrequency N (truncatedReflection N f) +
      truncatedReflection N (truncatedFrequency N f) = 0
    rw [truncatedFrequency_anticommutes]
    exact neg_add_cancel _

/-- Reflection again supplies unit momentum; frequency squared retains the spectral coordinate. -/
theorem truncatedFrequencyReflection_momentum1_eq_one (N : ℕ) :
    (truncatedFrequencyReflectionD1N2Split N).momentum1 = 1 := by
  apply LinearMap.ext
  intro f
  ext i
  change f.ofLp (truncatedReflectionIndex N (truncatedReflectionIndex N i)) = f.ofLp i
  rw [truncatedReflectionIndex_involutive N i]

/-- Constant Morse-dressed theta state is annihilated by the first-order supercharge everywhere. -/
theorem thetaCuspMorseConstant_supercharge_zero (A : ℝ) (n : ℕ) (x : ℝ) :
    deriv (thetaCuspMorseDressedPolynomial A n 1) x +
        thetaCuspMorseSuperpotential A n x *
          thetaCuspMorseDressedPolynomial A n 1 x = 0 := by
  rw [thetaCuspMorse_supercharge_dressedPolynomial]
  simp

/-- Same BPS state has exactly zero lower Witten Hamiltonian. -/
theorem thetaCuspMorseConstant_hamiltonian_zero (A : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspMorseHamiltonianMinus A n
      (thetaCuspMorseDressedPolynomial A n 1) x = 0 := by
  rw [thetaCuspMorseHamiltonianMinus_dressedPolynomial]
  simp

end RHTower
