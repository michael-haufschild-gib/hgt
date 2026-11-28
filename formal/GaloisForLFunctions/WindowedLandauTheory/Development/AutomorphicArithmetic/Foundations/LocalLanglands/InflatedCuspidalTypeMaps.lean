import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FiniteCuspidalTypeIrreducible

/-! A nonzero map realizing an inflated cuspidal type is injective.
Surjectivity of integral reduction makes its kernel invariant under
the full residue group. -/

noncomputable section

open Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A type map for restriction to the integral p-adic general linear group. -/
def HasInflatedType (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V) (τ : FDRep ℂ (Gn p n)) : Prop :=
  ∃ j : τ →ₗ[ℂ] V, j ≠ 0 ∧ ∀ (k : GL (Fin n) ℤ_[p]) (w : τ),
    j (τ.ρ (integralReduction p (Fin n) k) w) = ρ (integralInclusion p (Fin n) k) (j w)

theorem injective_of_cuspidal_type_map (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)
    (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character) (j : τ →ₗ[ℂ] V) (hj₀ : j ≠ 0)
    (hj : ∀ (k : GL (Fin n) ℤ_[p]) (w : τ),
      j (τ.ρ (integralReduction p (Fin n) k) w) = ρ (integralInclusion p (Fin n) k) (j w)) :
    Function.Injective j := by
  letI := isIrreducible_of_isCusp_character τ hτ
  let S : Subrepresentation τ.ρ :=
    ⟨LinearMap.ker j, fun g {w} hw => by
      obtain ⟨k, rfl⟩ := integralReduction_surjective p (Fin n) g
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hj, hw, map_zero]⟩
  have hs : S = ⊥ := (eq_bot_or_eq_top S).resolve_right fun he => hj₀ (LinearMap.ext fun w => by
    have hw : w ∈ S.toSubmodule := he.symm ▸ Submodule.mem_top
    exact hw)
  exact LinearMap.ker_eq_bot.mp (congrArg Subrepresentation.toSubmodule hs)

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.injective_of_cuspidal_type_map
