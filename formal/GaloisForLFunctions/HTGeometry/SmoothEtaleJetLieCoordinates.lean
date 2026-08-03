import GaloisForLFunctions.HTGeometry.FormalEtaleJetCompatibility
import GaloisForLFunctions.HTGeometry.SmoothJetLieCoordinates

/-!
# Transport of smooth jet coordinates through an étale chart

An étale chart from affine space to an affine smooth neighborhood transports based jets
uniquely.  Combining formal-étale lifting with explicit affine-space coefficients yields
the local smooth/Lie-coordinate identification: one tangent vector for every positive
jet order.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (ι : Type v)
variable {B : Type w} [CommRing B] [Algebra R B]

/-- **Smooth étale Lie coordinates.** Given a formally étale coordinate chart
`R[X_i] → B` and a point `p` of its source, based order-`n` arcs on `B` are exactly `n`
vectors in the chart tangent space `ι → R`. -/
noncomputable def smoothEtaleBasedArcLieEquiv
    (f : MvPolynomial ι R →ₐ[R] B) (hf : f.toRingHom.FormallyEtale)
    (p : B →ₐ[R] R) (n : ℕ) :
    BasedAlgArc (truncatedArcAugmentation R n) p ≃ (Fin n → ι → R) := by
  let x : ι → R := fun i => p (f (MvPolynomial.X i))
  have hx : p.comp f = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x]
  exact (formallyEtale_truncatedArc_basedAlgEquiv f hf p n).trans <|
    (Equiv.setCongr (by
      ext g
      change ((truncatedArcAugmentation R n).comp g = p.comp f) ↔
        ((truncatedArcAugmentation R n).comp g = MvPolynomial.aeval x)
      rw [hx])).trans (affineSpaceBasedArcLieEquiv R ι n x)

end

end GaloisForLFunctions.HTGeometry
