/-
# The quartic defect as a (slash-invariant) holomorphic form for Γ(2)

`quarticDefectH` is holomorphic (`MDiff`) on `ℍ`. Together with `quarticDefectSIF` this is the
holomorphy half of `ModularForm/CuspForm Γ(2) 2`; the cusp-behaviour (`bdd_at_cusps'` /
`zero_at_cusps'`) is the remaining input toward `F ≡ 0` via `NormTrace` to level-one weight-12.
-/
import GaloisForLFunctions.Bottcher.QuarticSlash

open Matrix ModularGroup CongruenceSubgroup Complex UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace Bottcher

/-- `quarticDefectH = F(z)` is holomorphic on the upper half-plane (manifold sense), since each
nullwert is and `F` is a polynomial in them. -/
theorem quarticDefectH_mdiff : MDiff quarticDefectH := by
  rw [mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := by simpa using hz
  refine (differentiableAt_quarticDefect hz').differentiableWithinAt.congr (fun w hw => ?_) ?_
  · show quarticDefect ((ofComplex w : ℍ) : ℂ) = quarticDefect w
    rw [ofComplex_apply_of_im_pos (by simpa using hw)]
  · show quarticDefect ((ofComplex z : ℍ) : ℂ) = quarticDefect z
    rw [ofComplex_apply_of_im_pos hz']

end Bottcher

namespace Bottcher2Cusp
open Bottcher

/-- `F ∣[2] S = −F`: from `F(−1/τ) = −τ²F(τ)` and `denom S τ = τ`. -/
theorem quarticDefectH_slash_S :
    quarticDefectH ∣[(2 : ℤ)] ModularGroup.S = -quarticDefectH := by
  funext z
  have hzim : 0 < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  rw [ModularForm.SL_slash_apply, Pi.neg_apply, quarticDefectH, quarticDefectH]
  have hact : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_div, one_div, inv_neg]
  rw [hact, show denom (ModularGroup.S) z = (z : ℂ) from denom_S z, quarticDefect_S hzim, _root_.zpow_neg]
  rw [show ((z : ℂ) ^ (2 : ℤ)) = (z : ℂ) ^ 2 from by norm_cast]
  field_simp

/-- `F ∣[2] T = −F`: from `F(τ+1) = −F(τ)` and `denom T τ = 1`. -/
theorem quarticDefectH_slash_T :
    quarticDefectH ∣[(2 : ℤ)] ModularGroup.T = -quarticDefectH := by
  funext z
  rw [ModularForm.SL_slash_apply, Pi.neg_apply, quarticDefectH, quarticDefectH]
  have hact : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [← zpow_one ModularGroup.T, ModularGroup.coe_T_zpow_smul_eq]; push_cast; ring
  have hden : denom (ModularGroup.T) z = 1 := by simp [ModularGroup.T, denom_apply]
  rw [hact, hden, quarticDefect_add_one]; simp

/-- `F ∣[2] γ = ±F` for every `γ ∈ SL(2,ℤ)` (it is `±` according to the sign character). -/
theorem quarticDefectH_slash_pm (γ : SL(2, ℤ)) :
    quarticDefectH ∣[(2 : ℤ)] γ = quarticDefectH ∨ quarticDefectH ∣[(2 : ℤ)] γ = -quarticDefectH := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [Or.inr quarticDefectH_slash_S, Or.inr quarticDefectH_slash_T]
  | one => exact Or.inl (SlashAction.slash_one 2 quarticDefectH)
  | mul x y _ _ ihx ihy =>
    rw [SlashAction.slash_mul]
    rcases ihx with hx | hx <;> rcases ihy with hy | hy <;>
      simp [hx, hy, SlashAction.neg_slash]
  | inv x _ ih =>
    rcases ih with h | h
    · left; rw [← h, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, h]
    · right
      have : (-quarticDefectH) ∣[(2:ℤ)] x⁻¹ = quarticDefectH := by
        rw [← h, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
      rwa [SlashAction.neg_slash, neg_eq_iff_eq_neg] at this

/-- `F → 0` at `i∞` (manifold form), from the cusp limit `tendsto_quarticDefect_atImInfty`. -/
theorem quarticDefectH_zeroAtImInfty : IsZeroAtImInfty quarticDefectH :=
  tendsto_quarticDefect_atImInfty.comp tendsto_coe_atImInfty

/-- `F ∣[2] γ → 0` at `i∞` for every `γ ∈ SL(2,ℤ)` (it is `±F`). -/
theorem quarticDefectH_slash_zeroAtImInfty (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (quarticDefectH ∣[(2 : ℤ)] γ) := by
  rcases quarticDefectH_slash_pm γ with h | h
  · rw [h]; exact quarticDefectH_zeroAtImInfty
  · rw [h]; exact quarticDefectH_zeroAtImInfty.neg

end Bottcher2Cusp
