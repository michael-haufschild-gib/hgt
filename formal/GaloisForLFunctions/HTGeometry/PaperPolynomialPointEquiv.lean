import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AmbientMaps

/-!
# Recovering algebra automorphisms from polynomial coordinate witnesses

The paper's `PolynomialEquiv` stores forward and inverse coordinate polynomials
with formal inverse identities. This supplies the converse bridge to algebra
equivalences, retaining the exact induced point maps.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

variable {k : Type*} [CommSemiring k] {σ τ : Type*}

/-- Reverse the two displayed polynomial coordinate systems. -/
def paperPolynomialEquivSymm (e : AmbientMaps.PolynomialEquiv k σ τ) :
    AmbientMaps.PolynomialEquiv k τ σ where
  forward := e.inverse
  inverse := e.forward
  forward_inverse := e.inverse_forward
  inverse_forward := e.forward_inverse

/-- Formal polynomial inverse identities induce an actual coefficient-algebra equivalence. -/
def paperPolynomialEquivAlgEquiv (e : AmbientMaps.PolynomialEquiv k σ τ) :
    MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (aeval e.forward) (aeval e.inverse)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change aeval e.forward (aeval e.inverse (X i)) = X i
      rw [aeval_X]
      exact e.forward_inverse i)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change aeval e.inverse (aeval e.forward (X i)) = X i
      rw [aeval_X]
      exact e.inverse_forward i)

/-- The recovered equivalence induces exactly the supplied forward point map. -/
theorem paperPolynomialEquivAlgEquiv_pointMap (e : AmbientMaps.PolynomialEquiv k σ τ) :
    AmbientMaps.pointMap (paperPolynomialEquivAlgEquiv e).toAlgHom = e.toPointMap := by
  funext x i
  change aeval x (aeval e.forward (X i)) = aeval x (e.forward i)
  rw [aeval_X]

/-- Its inverse induces exactly the supplied inverse point map. -/
theorem paperPolynomialEquivAlgEquiv_inversePointMap (e : AmbientMaps.PolynomialEquiv k σ τ) :
    AmbientMaps.pointMap (paperPolynomialEquivAlgEquiv e).symm.toAlgHom = e.invPointMap := by
  funext x i
  change aeval x (aeval e.inverse (X i)) = aeval x (e.inverse i)
  rw [aeval_X]

end

end GaloisForLFunctions.HTGeometry
