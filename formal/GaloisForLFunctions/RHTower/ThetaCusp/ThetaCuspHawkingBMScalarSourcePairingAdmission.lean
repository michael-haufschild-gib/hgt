import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMWeightedSquareCuspBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceCutoffCommutator

/-! Absolute quotient-space admission of every angular channel against the literal scalar field. -/
namespace RHTower.D4BMJointSource
open Complex Set MeasureTheory D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false

/-- The literal scalar testing field times the complete subtracted square is in quotient L². -/
theorem scalar_squareResidual_memLp (q : XiZeroCopy) (u : ℂ) :
    MemLp (fun z : UpperHalfPlane => scalar u (coordinates z)*squareResidual q (coordinates z))
      2 D4BMModularCore.measure := by
  obtain ⟨B,-,hb⟩ := scalar_squareRemainder_bounded u (center q) 3 (by norm_num)
  have hs : ContinuousOn (scalar u) domain := (cuspLeg_contDiffOn .scalar u).continuousOn
  apply cuspBound_memLp _ (hs.mul (squareResidual_continuousOn q)) (B/2)
  intro z hz
  simp only [Pi.mul_apply]
  rw [squareResidual_high q z hz,← mul_div_assoc,norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (hb z hz.le) (by norm_num)

/-- The full residual pairing is an absolutely convergent actual quotient integral. -/
theorem scalar_squareResidual_integrable (q : XiZeroCopy) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane => scalar u (coordinates z)*squareResidual q (coordinates z))
      D4BMModularCore.measure :=
  MemLp.integrable (by norm_num) (scalar_squareResidual_memLp q u)

/-- Multiplying the actual cutoff commutator by the full scalar leg preserves quotient L² admission. -/
theorem scalar_cutoffCommutator_memLp (u k : ℂ) :
    MemLp (fun z : UpperHalfPlane => scalar u (coordinates z)*cutoffCommutator k (coordinates z))
      2 D4BMModularCore.measure := by
  have hs : ContinuousOn (scalar u) domain := (cuspLeg_contDiffOn .scalar u).continuousOn
  apply cuspBound_memLp _ (hs.mul (cutoffCommutator_continuousOn k)) 0
  intro z hz
  simp only [Pi.mul_apply]
  rw [cutoffCommutator_high k z hz,mul_zero,norm_zero]

/-- Every retained cutoff derivative has an absolutely convergent scalar-field pairing. -/
theorem scalar_cutoffCommutator_integrable (u k : ℂ) :
    Integrable (fun z : UpperHalfPlane => scalar u (coordinates z)*cutoffCommutator k (coordinates z))
      D4BMModularCore.measure :=
  MemLp.integrable (by norm_num) (scalar_cutoffCommutator_memLp u k)

end
end RHTower.D4BMJointSource
