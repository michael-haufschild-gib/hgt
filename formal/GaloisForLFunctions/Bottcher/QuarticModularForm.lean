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

/-- `F² = (θ₃⁴−θ₂⁴−θ₄⁴)²` is `SL(2,ℤ)`-slash-invariant of weight `4`: from `F∣[2]γ = ±F`,
`F²∣[4]γ = (±F)² = F²` (the sign squares away). -/
theorem quarticDefectH_sq_slash_SL2Z (γ : SL(2, ℤ)) :
    (quarticDefectH ^ 2) ∣[(4 : ℤ)] γ = quarticDefectH ^ 2 := by
  rw [pow_two, show (4 : ℤ) = 2 + 2 by norm_num, ModularForm.mul_slash_SL2]
  rcases quarticDefectH_slash_pm γ with h | h
  · rw [h]
  · rw [h]; ring

/-- `F²` as a weight-`4` cusp form for `SL(2,ℤ)`: holomorphic (`F` is), `SL(2,ℤ)`-invariant
(`quarticDefectH_sq_slash_SL2Z`), and zero at the cusp (`F → 0`, so `F² → 0`). -/
noncomputable def quarticDefectSq : CuspForm 𝒮ℒ 4 where
  toFun := quarticDefectH ^ 2
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact quarticDefectH_sq_slash_SL2Z γ
  holo' := quarticDefectH_mdiff.pow 2
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [quarticDefectH_sq_slash_SL2Z γ]
    show Filter.Tendsto (quarticDefectH ^ 2) atImInfty (nhds 0)
    simpa using Filter.Tendsto.pow quarticDefectH_zeroAtImInfty 2

/-- **The Jacobi quartic identity** `θ₃⁴ = θ₂⁴ + θ₄⁴`, equivalently `F ≡ 0` on `ℍ`.

`F²` is a weight-`4` cusp form for `SL(2,ℤ)`, and the space `S₄(SL(2,ℤ))` of weight-`4` cusp forms
is zero-dimensional (`CuspForm.rank_eq_zero_of_weight_lt_twelve`, since `4 < 12`). Hence `F² ≡ 0`,
and so `F ≡ 0`. This is the theta-side input giving "`λ` omits `1`", closing
`λ : ℍ → ℂ ∖ {0,1}` ← (a) of the three-value Montel reduction. -/
theorem quarticDefect_eq_zero {σ : ℂ} (hσ : 0 < σ.im) : quarticDefect σ = 0 := by
  have h0 : quarticDefectSq = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) quarticDefectSq
  have hz : (quarticDefect σ) ^ 2 = 0 := by
    have key : quarticDefectSq ⟨σ, hσ⟩ = (0 : CuspForm 𝒮ℒ 4) ⟨σ, hσ⟩ :=
      DFunLike.congr_fun h0 _
    rw [CuspForm.zero_apply] at key
    exact key
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hz

end Bottcher2Cusp

namespace Bottcher

/-- **`λ` omits `1`, unconditionally.** The Jacobi quartic identity is now a theorem
(`Bottcher2Cusp.quarticDefect_eq_zero`), so the hypothesis of `modularLambda_ne_one_of_quartic`
is discharged: for `0 < τ.im`, `modularLambda τ ≠ 1`. -/
theorem modularLambda_ne_one {τ : ℂ} (hτ : 0 < τ.im) : modularLambda τ ≠ 1 :=
  modularLambda_ne_one_of_quartic hτ (Bottcher2Cusp.quarticDefect_eq_zero hτ)

/-- **`λ : ℍ → ℂ ∖ {0,1}`, unconditionally.** Both omitted values, with the quartic identity proven. -/
theorem modularLambda_omits_zero_one' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda τ ≠ 0 ∧ modularLambda τ ≠ 1 :=
  modularLambda_omits_zero_one (fun _ hσ => Bottcher2Cusp.quarticDefect_eq_zero hσ) hτ

/-- The range condition as a single membership: `λ τ ∈ ℂ ∖ {0,1}`, unconditionally. -/
theorem modularLambda_mem_compl_zero_one' {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda τ ∈ ({0, 1} : Set ℂ)ᶜ :=
  modularLambda_mem_compl_zero_one (fun _ hσ => Bottcher2Cusp.quarticDefect_eq_zero hσ) hτ

end Bottcher
