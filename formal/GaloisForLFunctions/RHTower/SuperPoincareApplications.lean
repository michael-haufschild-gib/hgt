import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.RHTower.CCMPublishedRestrictedWeilParityBlocks
import GaloisForLFunctions.RHTower.CCMParityInvolutionGrading
import GaloisForLFunctions.RHTower.RankTwoCommutatorParityMultiplicityBalance
import GaloisForLFunctions.RHTower.RealCoronaQuaternionicCyclic
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseAnomalousDarboux
import GaloisForLFunctions.RHTower.SuzukiPositiveResolventParityNoGo
import GaloisForLFunctions.RHTower.DeningerArithmeticQuaternionicTransitionNoReal

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

/-- Linear parity reflection in the Suzuki four-space. -/
def suzukiParityReflectionEnd : Module.End ℝ SuzukiParityFourSpace where
  toFun := suzukiParityReflection
  map_add' u v := by
    rcases u with ⟨⟨u0, u1⟩, ⟨u2, u3⟩⟩
    rcases v with ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩
    ext <;> simp [suzukiParityReflection, add_comm]
  map_smul' c v := by
    rcases v with ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩
    ext <;> simp [suzukiParityReflection, smul_eq_mul]

/-- Linear parity-changing Suzuki position operator. -/
def suzukiParityPositionEnd : Module.End ℝ SuzukiParityFourSpace where
  toFun := suzukiParityPosition
  map_add' u v := by
    rcases u with ⟨⟨u0, u1⟩, ⟨u2, u3⟩⟩
    rcases v with ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩
    rfl
  map_smul' c v := by
    rcases v with ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩
    rfl

/-- Suzuki position and reflection are unit-momentum `N = 2` supercharges. -/
def suzukiParityD1N2 :
    SuperPoincare.D1N2 (Module.End ℝ SuzukiParityFourSpace) where
  supercharge0 := suzukiParityPositionEnd
  supercharge1 := suzukiParityReflectionEnd
  momentum := 1
  supercharge0_sq := by
    apply LinearMap.ext
    rintro ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩
    rfl
  supercharge1_sq := by
    apply LinearMap.ext
    rintro ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩
    simp [suzukiParityReflectionEnd, suzukiParityReflection]
  mixed_anticommutator := by
    apply LinearMap.ext
    intro v
    change suzukiParityPosition (suzukiParityReflection v) +
      suzukiParityReflection (suzukiParityPosition v) = 0
    rw [suzukiParityPosition_anticommutes_reflection]
    exact neg_add_cancel _

/-- First Deninger quaternion transition as a complex-linear endomorphism. -/
def deningerQuaternionTransitionIEnd : Module.End ℂ (ℂ × ℂ) where
  toFun := deningerQuaternionTransitionI
  map_add' u v := by
    rcases u with ⟨u0, u1⟩
    rcases v with ⟨v0, v1⟩
    ext <;> simp [deningerQuaternionTransitionI] <;> ring
  map_smul' c v := by
    rcases v with ⟨v0, v1⟩
    ext <;> simp [deningerQuaternionTransitionI, smul_eq_mul] <;> ring

/-- Second Deninger quaternion transition as a complex-linear endomorphism. -/
def deningerQuaternionTransitionKEnd : Module.End ℂ (ℂ × ℂ) where
  toFun := deningerQuaternionTransitionK
  map_add' u v := by
    rcases u with ⟨u0, u1⟩
    rcases v with ⟨v0, v1⟩
    ext <;> simp [deningerQuaternionTransitionK, add_comm]
  map_smul' c v := by
    rcases v with ⟨v0, v1⟩
    ext <;> simp [deningerQuaternionTransitionK, smul_eq_mul]

/-- Quaternionic transitions form an `N = 2` sector with negative unit momentum. -/
def deningerQuaternionD1N2 :
    SuperPoincare.D1N2 (Module.End ℂ (ℂ × ℂ)) where
  supercharge0 := deningerQuaternionTransitionIEnd
  supercharge1 := deningerQuaternionTransitionKEnd
  momentum := -1
  supercharge0_sq := by
    apply LinearMap.ext
    intro v
    change deningerQuaternionTransitionI (deningerQuaternionTransitionI v) = -v
    exact deningerQuaternionTransitionI_sq v
  supercharge1_sq := by
    apply LinearMap.ext
    intro v
    change deningerQuaternionTransitionK (deningerQuaternionTransitionK v) = -v
    exact deningerQuaternionTransitionK_sq v
  mixed_anticommutator := by
    apply LinearMap.ext
    intro v
    change deningerQuaternionTransitionI (deningerQuaternionTransitionK v) +
      deningerQuaternionTransitionK (deningerQuaternionTransitionI v) = 0
    rw [deningerQuaternionTransitionI_anticommutes_K]
    exact neg_add_cancel _

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
