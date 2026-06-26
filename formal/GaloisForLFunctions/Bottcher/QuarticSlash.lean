/-
# The quartic defect as a slash-invariant function (generator invariances)

`quarticDefectH z = F(z) = θ₃⁴−θ₂⁴−θ₄⁴` is invariant under the `SlashAction` of the `Γ(2)` generators.
With `Gamma2_eq_closure` + `slash_action_generators`, these promote to `F ∈ SlashInvariantForm (↑Γ(2)) 2`.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaModular
import GaloisForLFunctions.Bottcher.Gamma2Generators

open Matrix ModularGroup CongruenceSubgroup Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace Bottcher

/-- `F` as a function on the upper half-plane. -/
noncomputable def quarticDefectH : ℍ → ℂ := fun z => quarticDefect (z : ℂ)

/-- `F ∣[2] T² = F` (the `T²` generator of `Γ(2)`). -/
theorem quarticDefectH_slash_Tsq :
    quarticDefectH ∣[(2 : ℤ)] (ModularGroup.T ^ 2) = quarticDefectH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, quarticDefectH, quarticDefectH]
  have hact : ((ModularGroup.T ^ 2 • z : ℍ) : ℂ) = (z : ℂ) + 2 := by
    have := ModularGroup.coe_T_zpow_smul_eq (z := z) (n := 2); push_cast at this ⊢; convert this using 2
  have he10 : ((ModularGroup.T ^ 2) 1 0 : ℤ) = 0 := by
    show (↑(ModularGroup.T ^ 2) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0; rw [Tsq_coe]; rfl
  have he11 : ((ModularGroup.T ^ 2) 1 1 : ℤ) = 1 := by
    show (↑(ModularGroup.T ^ 2) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1; rw [Tsq_coe]; rfl
  rw [hact, he10, he11, quarticDefect_add_two]
  show quarticDefect (z : ℂ) = (((0 : ℤ) : ℂ) * (z : ℂ) + ((1 : ℤ) : ℂ)) ^ 2 * quarticDefect (z : ℂ)
  norm_num

/-- `F ∣[2] (−I) = F` (weight-2 evenness; `−I ∈ Γ(2)`). -/
theorem quarticDefectH_slash_negOne :
    quarticDefectH ∣[(2 : ℤ)] (-1 : SL(2, ℤ)) = quarticDefectH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, quarticDefectH, quarticDefectH]
  have hact : (((-1 : SL(2, ℤ)) • z : ℍ) : ℂ) = (z : ℂ) := by
    rw [show (-1 : SL(2, ℤ)) • z = (1 : SL(2, ℤ)) • z from by rw [← SL_neg_smul]; norm_num, one_smul]
  have e10 : ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := by decide
  have e11 : ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 := by decide
  rw [hact, e10, e11]
  show quarticDefect (z : ℂ) = (((0 : ℤ) : ℂ) * (z : ℂ) + (((-1) : ℤ) : ℂ)) ^ 2 * quarticDefect (z : ℂ)
  norm_num

theorem quarticDefectH_slash_R : quarticDefectH ∣[(2 : ℤ)] Rgen = quarticDefectH := by
  funext z
  rw [ModularForm.slash_action_eq'_iff, quarticDefectH, quarticDefectH]
  show quarticDefect ((Rgen • z : ℍ) : ℂ)
    = (((Rgen 1 0 : ℤ) : ℂ) * (z : ℂ) + ((Rgen 1 1 : ℤ) : ℂ)) ^ 2 * quarticDefect (z : ℂ)
  have hzim : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  have e00 : (Rgen 0 0 : ℤ) = 1 := by show (↑Rgen : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1; rw [Rgen_apply]; rfl
  have e01 : (Rgen 0 1 : ℤ) = 0 := by show (↑Rgen : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0; rw [Rgen_apply]; rfl
  have e10 : (Rgen 1 0 : ℤ) = 2 := by show (↑Rgen : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 2; rw [Rgen_apply]; rfl
  have e11 : (Rgen 1 1 : ℤ) = 1 := by show (↑Rgen : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1; rw [Rgen_apply]; rfl
  have hd : 2 * (z : ℂ) + 1 ≠ 0 := by
    intro h; apply absurd hzim; rw [show (z : ℂ) = -1 / 2 by linear_combination h / 2]; norm_num
  have hact : ((Rgen • z : ℍ) : ℂ) = (z : ℂ) / (2 * (z : ℂ) + 1) := by
    rw [coe_specialLinearGroup_apply, e00, e01, e10, e11]
    simp only [algebraMap_int_eq, eq_intCast]; push_cast; ring
  rw [hact, e10, e11, quarticDefect_lowerTri (τ := (z : ℂ)) hzim]
  simp only [Int.cast_ofNat, Int.cast_one]; rfl

theorem quarticDefectH_slash_Gamma2 (A : SL(2, ℤ)) (hA : A ∈ CongruenceSubgroup.Gamma 2) :
    quarticDefectH ∣[(2 : ℤ)] A = quarticDefectH := by
  have hmem : A ∈ Subgroup.closure ({ModularGroup.T ^ 2, Rgen, -1} : Set SL(2, ℤ)) :=
    Gamma2_eq_closure ▸ hA
  clear hA
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [quarticDefectH_slash_Tsq, quarticDefectH_slash_R, quarticDefectH_slash_negOne]
  | one => exact SlashAction.slash_one 2 quarticDefectH
  | mul x y _ _ ihx ihy => rw [SlashAction.slash_mul, ihx, ihy]
  | inv x _ ih => rw [← ih, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, ih]

noncomputable def quarticDefectSIF : SlashInvariantForm (CongruenceSubgroup.Gamma 2) 2 where
  toFun := quarticDefectH
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    simp only [SpecialLinearGroup.mapGL]
    exact quarticDefectH_slash_Gamma2 A hA

end Bottcher
