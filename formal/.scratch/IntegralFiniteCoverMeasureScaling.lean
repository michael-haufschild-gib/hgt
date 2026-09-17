import GaloisForLFunctions.RHTower.IntegralSubgroupFiniteCoverFundamentalDomain

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

theorem integralFiniteCoverFundamentalSet_aedisjoint (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    Pairwise ((AEDisjoint realSL2Haar) on fun q : Γ ⧸ K.subgroupOf Γ =>
      MulOpposite.op (integralSL2ToReal q.out.val) • integralSubgroupFundamentalSet Γ) := by
  let qΓ : Γ ⧸ K.subgroupOf Γ → (realImage Γ).op := fun q =>
    ⟨MulOpposite.op (integralSL2ToReal q.out.val), by
      change integralSL2ToReal q.out.val ∈ realImage Γ
      exact ⟨q.out.val, q.out.property, rfl⟩⟩
  have hqΓ_injective : Function.Injective qΓ := by
    intro q₁ q₂ h
    apply Quotient.out_injective
    apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
    exact congrArg (fun z : (realImage Γ).op => z.val.unop) h
  change Pairwise ((AEDisjoint realSL2Haar) on fun q =>
    qΓ q • integralSubgroupFundamentalSet Γ)
  intro q₁ q₂ hne
  apply (integralSubgroupFundamentalSet_isFundamentalDomain Γ).aedisjoint
  exact fun h => hne (hqΓ_injective h)

end

end GaloisForLFunctions.RHTower
