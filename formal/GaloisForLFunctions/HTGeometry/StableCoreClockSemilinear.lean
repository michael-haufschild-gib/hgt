import GaloisForLFunctions.HTGeometry.StableCoreFunctoriality

/-!
# The restricted clock on the persistent core is semilinear

The clock cocharacter `ρ` restricts to a symmetry `ρ|T` of the persistent core `T = stableRangeCore φ`
(`stableRangeCoreSymmetryAlgEquiv`).  When the ambient clock is semilinear for the derivation
(`ρ(x′) = λ·(ρ x)′`), so is its restriction: `ρ|T(w′) = λ·(ρ|T w)′`.  This is the semilinearity
hypothesis of the §3(a) core-Möbius step (`clockSemilinearAlgEquiv_generator_mobius`) applied at the
core generator.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- The restricted core clock agrees with the ambient clock on the underlying field. -/
@[simp] theorem stableRangeCoreSymmetryAlgEquiv_coe
    (φ : F →ₐ[C] F) (ρ : F ≃ₐ[C] F) (hcomm : ∀ x, φ (ρ x) = ρ (φ x))
    (x : stableRangeCore φ) :
    ((stableRangeCoreSymmetryAlgEquiv φ ρ hcomm x : stableRangeCore φ) : F) = ρ (x : F) := rfl

/-- **The restricted clock is semilinear.**  If the ambient clock `ρ` is semilinear for the
derivation with factor `λ`, its restriction to the persistent core is semilinear with the same
factor. -/
theorem stableRangeCoreSymmetry_semilinear
    [Differential C] [Differential F] [DifferentialAlgebra C F]
    (φ : F →ₐ[C] F) (hφ : ∀ x : F, φ x′ = (φ x)′)
    (ρ : F ≃ₐ[C] F) (hcomm : ∀ x, φ (ρ x) = ρ (φ x))
    {lam : C} (hsemi : ∀ x : F, ρ x′ = algebraMap C F lam * (ρ x)′) :
    letI : Differential (stableRangeCore φ) :=
      derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
    ∀ w : stableRangeCore φ,
      (stableRangeCoreSymmetryAlgEquiv φ ρ hcomm).toAlgHom w′
        = algebraMap C (stableRangeCore φ) lam
          * ((stableRangeCoreSymmetryAlgEquiv φ ρ hcomm).toAlgHom w)′ := by
  letI : Differential (stableRangeCore φ) :=
    derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
  intro w
  apply Subtype.ext
  have hlam : ((algebraMap C (stableRangeCore φ) lam : stableRangeCore φ) : F) = algebraMap C F lam := by
    rw [IsScalarTower.algebraMap_apply C (stableRangeCore φ) F]; rfl
  push_cast [derivationClosedDifferential_apply, stableRangeCoreSymmetryAlgEquiv_coe, hlam]
  exact hsemi (w : F)

end GaloisForLFunctions.HTGeometry
