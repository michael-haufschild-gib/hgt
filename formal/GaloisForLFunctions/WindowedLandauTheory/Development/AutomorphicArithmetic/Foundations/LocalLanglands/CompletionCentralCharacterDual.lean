import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompletionCentralCharacterClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothSubrepresentation

/-! The central character of a smooth contragredient inverts
the original central character. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation GlobalTheory.PRep

namespace GlobalTheory.GLp.IrrGL

variable {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) {n : ℕ}

local notation "L" => HeightOneSpectrum.adicCompletion E v

theorem centralCharacter_smoothDual (π π' : IrrRep (GL (Fin n) L))
    (e : π'.ρ.Equiv π.ρ.smoothDual) :
    centralCharacter v (⟨n, π'.cl⟩ : IrrGL L) = (centralCharacter v (⟨n, π.cl⟩ : IrrGL L))⁻¹ := by
  apply centralCharacter_eq_of_act v π'
  intro z w
  let g := GeneralLinearGroup.scalar (Fin n) z
  apply e.toLinearEquiv.injective
  have h := IntertwiningMap.isIntertwining π'.ρ π.ρ.smoothDual e.toIntertwiningMap g w
  change e.toLinearEquiv (π'.ρ g w) = π.ρ.smoothDual g (e.toLinearEquiv w) at h
  change e.toLinearEquiv (π'.ρ g w) = e.toLinearEquiv (_ • w)
  rw [h, map_smul]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [smoothDual_apply]
  change (e.toLinearEquiv w).val (π.ρ ((GeneralLinearGroup.scalar (Fin n) z)⁻¹) x) =
    (↑(((centralCharacter v (⟨n, π.cl⟩ : IrrGL L))⁻¹) z) : ℂ) • (e.toLinearEquiv w).val x
  rw [← map_inv (GeneralLinearGroup.scalar (Fin n)), centralCharacter_act v π z⁻¹, map_smul,
    map_inv, MonoidHom.inv_apply]

end GlobalTheory.GLp.IrrGL

#print axioms GlobalTheory.GLp.IrrGL.centralCharacter_smoothDual
