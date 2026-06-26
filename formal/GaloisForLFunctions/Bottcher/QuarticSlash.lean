/-
# The quartic defect as a slash-invariant function (generator invariances)

`quarticDefectH : ℍ → ℂ`, `z ↦ F(z) = θ₃⁴−θ₂⁴−θ₄⁴`, is invariant under the `SlashAction` of the
`Γ(2)` generators. With `Gamma2_eq_closure` and mathlib's `slash_action_generators`, these promote to
`F ∈ SlashInvariantForm (↑Γ(2)) 2` (the `R`-generator case + the GL-image bridge are the remaining
plumbing). Built from the unconditional weight-2 transformation laws `quarticDefect_add_two`,
`quarticDefect_lowerTri` via `ModularForm.slash_action_eq'_iff`.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaModular
import GaloisForLFunctions.Bottcher.Gamma2Generators

open Matrix ModularGroup CongruenceSubgroup Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace Bottcher

/-- `F` as a function on the upper half-plane. -/
noncomputable def quarticDefectH : ℍ → ℂ := fun z => quarticDefect (z : ℂ)

/-- `F ∣[2] T² = F`: invariance under the `T²` generator of `Γ(2)`. -/
theorem quarticDefectH_slash_Tsq :
    quarticDefectH ∣[(2 : ℤ)] (ModularGroup.T ^ 2) = quarticDefectH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff]
  have he10 : ((ModularGroup.T ^ 2) 1 0 : ℤ) = 0 := by
    show (↑(ModularGroup.T ^ 2) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0; rw [Tsq_coe]; rfl
  have he11 : ((ModularGroup.T ^ 2) 1 1 : ℤ) = 1 := by
    show (↑(ModularGroup.T ^ 2) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1; rw [Tsq_coe]; rfl
  have hact : ((ModularGroup.T ^ 2 • z : ℍ) : ℂ) = (z : ℂ) + 2 := by
    have := ModularGroup.coe_T_zpow_smul_eq (z := z) (n := 2); push_cast at this ⊢; convert this using 2
  show quarticDefectH (ModularGroup.T ^ 2 • z) = ((((ModularGroup.T ^ 2) 1 0 : ℤ) : ℂ) * z +
    (((ModularGroup.T ^ 2) 1 1 : ℤ) : ℂ)) ^ 2 * quarticDefectH z
  rw [he10, he11, quarticDefectH, quarticDefectH, hact, quarticDefect_add_two]; simp

/-- `F ∣[2] (−I) = F`: invariance under `−I ∈ Γ(2)` (weight-2 evenness). -/
theorem quarticDefectH_slash_negOne :
    quarticDefectH ∣[(2 : ℤ)] (-1 : SL(2, ℤ)) = quarticDefectH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff]
  have e10 : ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := by decide
  have e11 : ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 := by decide
  have hact : (((-1 : SL(2, ℤ)) • z : ℍ) : ℂ) = (z : ℂ) := by
    rw [show ((-1 : SL(2, ℤ)) • z : ℍ) = ((1 : SL(2, ℤ)) • z) from by rw [← SL_neg_smul]; norm_num,
      one_smul]
  show quarticDefectH ((-1 : SL(2, ℤ)) • z) = ((((-1 : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * z +
    (((-1 : SL(2, ℤ)) 1 1 : ℤ) : ℂ)) ^ 2 * quarticDefectH z
  rw [e10, e11, quarticDefectH, quarticDefectH, hact]; push_cast; ring

end Bottcher
