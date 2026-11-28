import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FiniteCuspidalTypeTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicUnitCharacterReduction

/-! Tame determinant twisting of an inflated type is the inflation
of the corresponding determinant twist over the residue field. -/

noncomputable section

open Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inflatedType_determinantTwist (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)
    (τ : FDRep ℂ (Gn p n)) (hτ : HasInflatedType ρ τ)
    (χ : ℚ_[p]ˣ →* ℂˣ) (δ : (ZMod p)ˣ →* ℂˣ)
    (hδ : ∀ u : ℤ_[p]ˣ, δ (padicUnitReduction u) =
      χ (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)) :
    HasInflatedType (ρ.scalarTwist (χ.comp GeneralLinearGroup.det)) (finiteDeterminantTwist τ δ) := by
  obtain ⟨j, hj₀, hj⟩ := hτ
  refine ⟨j, hj₀, fun k v => ?_⟩
  change j ((δ (GeneralLinearGroup.det (integralReduction p (Fin n) k)) : ℂ) •
      τ.ρ (integralReduction p (Fin n) k) v) =
    (χ (GeneralLinearGroup.det (integralInclusion p (Fin n) k)) : ℂ) • ρ (integralInclusion p (Fin n) k) (j v)
  have hr : GeneralLinearGroup.det (integralReduction p (Fin n) k) = padicUnitReduction (GeneralLinearGroup.det k) :=
    GeneralLinearGroup.map_det _ _
  have hi : GeneralLinearGroup.det (integralInclusion p (Fin n) k) =
      Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom (GeneralLinearGroup.det k) :=
    GeneralLinearGroup.map_det _ _
  rw [map_smul, hj, hr, hi, hδ]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.inflatedType_determinantTwist
