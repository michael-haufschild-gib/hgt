import GaloisForLFunctions.HTGeometry.AlgebraSpectrumEquiv
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysIntegralLift

/-!
# Surjectivity on complex points for integral extensions

Lying over and algebraic closedness extend every complex point of a base algebra through an
injective integral extension.  Repackaging the resulting ring homomorphism as a complex-algebra
homomorphism makes the contravariant map on `AlgSpec` surjective.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AlgSpec

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
variable [Algebra.IsIntegral A B] [FaithfulSMul A B]

/-- **An injective integral extension is surjective on complex points.** -/
theorem surjective_precomp_of_isIntegral :
    Function.Surjective (precomp (IsScalarTower.toAlgHom ℂ A B)) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := RHTower.deningerHom_exists_extension_of_isIntegral
    (A := A) (B := B) (C := ℂ) φ.toRingHom
  let ψAlg : B →ₐ[ℂ] ℂ :=
    { ψ with
      commutes' := fun c => by
        have htower : algebraMap ℂ B c = algebraMap A B (algebraMap ℂ A c) :=
          IsScalarTower.algebraMap_apply ℂ A B c
        rw [htower]
        calc
          ψ (algebraMap A B (algebraMap ℂ A c)) =
              φ (algebraMap ℂ A c) := hψ _
          _ = c := φ.commutes c
          _ = algebraMap ℂ ℂ c := by simp }
  refine ⟨ψAlg, ?_⟩
  apply DFunLike.ext _ _
  intro a
  exact hψ a

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
