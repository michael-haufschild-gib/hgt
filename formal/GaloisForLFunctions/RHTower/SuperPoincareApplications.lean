import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinReflection
import GaloisForLFunctions.RHTower.CCMPublishedRestrictedWeilParityBlocks
import GaloisForLFunctions.RHTower.CCMParityInvolutionGrading
import GaloisForLFunctions.RHTower.RankTwoCommutatorParityMultiplicityBalance
import GaloisForLFunctions.RHTower.RealCoronaQuaternionicCyclic
import GaloisForLFunctions.RHTower.PrimeArchThetaMorseAnomalousDarboux
import GaloisForLFunctions.RHTower.SuzukiPositiveResolventParityNoGo
import GaloisForLFunctions.RHTower.DeningerArithmeticQuaternionicTransitionNoReal
import GaloisForLFunctions.RHTower.GradingSectorWitness
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering
import GaloisForLFunctions.RHTower.SuzukiXiRealFEBipolarizationCompletion

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

/-- Abstract sign grading and its occupied odd sector form another unit-momentum `N = 2` pair. -/
def gradingSectorD1N2 :
    SuperPoincare.D1N2 (Matrix (Fin 2) (Fin 2) ℝ) where
  supercharge0 := signGrading
  supercharge1 := flipMatrix
  momentum := 1
  supercharge0_sq := signGrading_sq
  supercharge1_sq := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [flipMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  mixed_anticommutator := by
    rw [signGrading_anticomm]
    exact neg_add_cancel _

end GaloisForLFunctions.RHTower

open GaloisForLFunctions GaloisForLFunctions.RHTower

namespace RHTower

/-- Positive-aperture Burnol holonomy and cosine reflection form split `N = 2`. -/
def burnolApertureHolonomyD1N2Split (u v : ℝ) :
    SuperPoincare.D1N2Split (evenSubspace →L[ℂ] evenSubspace) := by
  let a := Real.exp u
  have ha : 0 < a := Real.exp_pos u
  let r := Real.exp v + 1
  have hr : 1 < r := by
    dsimp [r]
    linarith [Real.exp_pos v]
  refine {
    supercharge0 := burnolExtendedBilateralApertureHolonomy a ha r hr
    supercharge1 := evenFourierTransform
    mixed_anticommutator := ?_ }
  · apply ContinuousLinearMap.ext
    intro x
    change burnolExtendedBilateralApertureHolonomy
        a ha r hr (evenFourierTransform x) +
      evenFourierTransform (burnolExtendedBilateralApertureHolonomy
        a ha r hr x) = 0
    have h := burnolExtendedBilateralApertureHolonomy_cosine_odd a ha r hr x
    change burnolExtendedBilateralApertureHolonomy
        a ha r hr (evenFourierTransform x) =
      -evenFourierTransform (burnolExtendedBilateralApertureHolonomy
        a ha r hr x) at h
    rw [h]
    exact neg_add_cancel _

/-- Fourier-reflection diagonal translation in the Burnol split sector is the identity. -/
theorem burnolApertureHolonomy_momentum1_eq_one (u v : ℝ) :
    (burnolApertureHolonomyD1N2Split u v).momentum1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact evenFourierTransform_involutive x

/-- Sonin logarithmic Fourier scattering is an infinite-dimensional unit-momentum supercharge. -/
def soninLogFourierScatteringD1N1 :
    SuperPoincare.D1N1 (SoninL2 →L[ℂ] SoninL2) where
  supercharge := soninLogFourierScattering
  momentum := 1
  supercharge_sq := by
    simpa only [pow_two] using soninLogFourierScattering_sq_eq_one

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

/-- Xi-real quarter-turn and FE reflection form split `N = 2` with opposite momenta. -/
def suzukiWeldQuarterTurnReflectionD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℝ (ℝ × ℝ)) where
  supercharge0 := planeJ
  supercharge1 := weldFEReflectionLinear
  mixed_anticommutator := by
    apply LinearMap.ext
    intro x
    change planeJ (weldFEReflectionLinear x) + weldFEReflectionLinear (planeJ x) = 0
    have h := congrArg (fun f : Module.End ℝ (ℝ × ℝ) => f x)
      planeJ_comp_weldFEReflectionLinear_eq_neg
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h
    rw [h]
    exact neg_add_cancel _

/-- Quarter-turn diagonal translation is negative unit momentum. -/
theorem suzukiWeldQuarterTurnReflection_momentum0_eq_neg_one :
    suzukiWeldQuarterTurnReflectionD1N2Split.momentum0 = -1 := by
  apply LinearMap.ext
  intro x
  change planeJ (planeJ x) = -x
  have h := congrArg (fun f : Module.End ℝ (ℝ × ℝ) => f x) planeJ_sq
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] using h

/-- FE-reflection diagonal translation is positive unit momentum. -/
theorem suzukiWeldQuarterTurnReflection_momentum1_eq_one :
    suzukiWeldQuarterTurnReflectionD1N2Split.momentum1 = 1 := by
  apply LinearMap.ext
  intro x
  change weldFEReflectionLinear (weldFEReflectionLinear x) = x
  have h := congrArg (fun f : Module.End ℝ (ℝ × ℝ) => f x)
    weldFEReflectionLinear_sq
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Positive light-cone combination of the split supercharges is nilpotent. -/
theorem suzukiWeldQuarterTurnReflection_positive_lightlike :
    ((2 : ℝ)⁻¹ •
      (suzukiWeldQuarterTurnReflectionD1N2Split.supercharge0 +
        suzukiWeldQuarterTurnReflectionD1N2Split.supercharge1)) *
      ((2 : ℝ)⁻¹ •
        (suzukiWeldQuarterTurnReflectionD1N2Split.supercharge0 +
          suzukiWeldQuarterTurnReflectionD1N2Split.supercharge1)) = 0 := by
  apply LinearMap.ext
  intro x
  change suzukiWeldPositiveTriangleLinear (suzukiWeldPositiveTriangleLinear x) = 0
  have h := congrArg (fun f : Module.End ℝ (ℝ × ℝ) => f x)
    suzukiWeldPositiveTriangleLinear_sq
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- Negative light-cone combination of the split supercharges is also nilpotent. -/
theorem suzukiWeldQuarterTurnReflection_negative_lightlike :
    ((2 : ℝ)⁻¹ •
      (suzukiWeldQuarterTurnReflectionD1N2Split.supercharge0 -
        suzukiWeldQuarterTurnReflectionD1N2Split.supercharge1)) *
      ((2 : ℝ)⁻¹ •
        (suzukiWeldQuarterTurnReflectionD1N2Split.supercharge0 -
          suzukiWeldQuarterTurnReflectionD1N2Split.supercharge1)) = 0 := by
  apply LinearMap.ext
  intro x
  change suzukiWeldNegativeTriangleLinear (suzukiWeldNegativeTriangleLinear x) = 0
  have h := congrArg (fun f : Module.End ℝ (ℝ × ℝ) => f x)
    suzukiWeldNegativeTriangleLinear_sq
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

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
