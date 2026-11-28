import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroCuspidalFixedType

/-! Two inflated cuspidal types in the same smooth irreducible
representation have the same range. The comparison intertwines the
finite actions because integral reduction is surjective. -/

noncomputable section

open Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V W W' : Type}
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

theorem character_eq_of_common_cuspidal_inflation
    (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V) [ρ.IsIrreducible]
    (hρ : ∀ v : V, IsOpen {g : GL (Fin n) ℚ_[p] | ρ g v = v})
    (ω : ℚ_[p]ˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (τ : Representation ℂ (Gn p n) W) (τ' : Representation ℂ (Gn p n) W')
    (hτ : IsCusp τ.character) (hτ' : IsCusp τ'.character)
    (j : W →ₗ[ℂ] V) (j' : W' →ₗ[ℂ] V) (hj₀ : j ≠ 0) (hj'₀ : j' ≠ 0)
    (hji : Function.Injective j) (hji' : Function.Injective j')
    (hj : ∀ (k : GL (Fin n) ℤ_[p]) (w : W),
      j (τ (integralReduction p (Fin n) k) w) = ρ (integralInclusion p (Fin n) k) (j w))
    (hj' : ∀ (k : GL (Fin n) ℤ_[p]) (w : W'),
      j' (τ' (integralReduction p (Fin n) k) w) = ρ (integralInclusion p (Fin n) k) (j' w)) :
    τ.character = τ'.character := by
  have hr := (principalFixed_eq_range_of_cuspidal_type ρ hρ ω hω τ hτ j hj₀ hj).symm.trans
    (principalFixed_eq_range_of_cuspidal_type ρ hρ ω hω τ' hτ' j' hj'₀ hj')
  let e := (LinearEquiv.ofInjective j hji).trans
    ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective j' hji').symm)
  have he (w : W) : j' (e w) = j w :=
    congrArg Subtype.val ((LinearEquiv.ofInjective j' hji').apply_symm_apply
      (LinearEquiv.ofEq _ _ hr (LinearEquiv.ofInjective j hji w)))
  apply char_iso (Representation.Equiv.mk e ?_)
  intro g
  obtain ⟨k, rfl⟩ := integralReduction_surjective p (Fin n) g
  apply LinearMap.ext
  intro w
  apply hji'
  change j' (e (τ (integralReduction p (Fin n) k) w)) =
    j' (τ' (integralReduction p (Fin n) k) (e w))
  rw [he, hj, hj', he]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.character_eq_of_common_cuspidal_inflation
