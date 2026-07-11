import GaloisForLFunctions.DifferentialPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Partial evaluation of differential polynomials and the differential Steinitz exchange

The differential-transcendence matroid needs the exchange property.  Its mechanism is a *partial*
evaluation of a two-family differential polynomial: substitute the jets of the right family `y` into
the right variables and keep the left variables `X` formal, landing in the differential polynomial
ring in the left variables over `K`.

The construction factors as the isomorphism splitting the left/right variables followed by
`MvPolynomial.map` of the jet evaluation at `y`; hence it is injective exactly when `y` is
differentially transcendental (the jet evaluation is injective).  This injectivity is the crux: a
nonzero two-family relation stays nonzero after substituting a differentially transcendental `y`.
-/

namespace GaloisForLFunctions

open MvPolynomial

variable {L R k K : Type*} [CommRing k] [CommRing K] [Algebra k K] [Differential K]

/-- Split the left and right jet variables: `k{L ⊔ R}` as differential polynomials in the left
variables with coefficients differential polynomials in the right variables. -/
noncomputable def diffPolySumSplit (L R k : Type*) [CommRing k] :
    DifferentialPolynomial (L ⊕ R) k ≃ₐ[k]
      MvPolynomial (L × ℕ) (DifferentialPolynomial R k) :=
  (MvPolynomial.renameEquiv k (Equiv.sumProdDistrib L R ℕ)).trans
    (MvPolynomial.sumAlgEquiv k (L × ℕ) (R × ℕ))

/-- Partial evaluation: substitute the right variables with the jets of `y`, keep the left variables
formal. -/
noncomputable def diffPolyEvalRight (y : R → K) :
    DifferentialPolynomial (L ⊕ R) k →+* DifferentialPolynomial L K :=
  (MvPolynomial.map (differentialPolynomialEval (C := k) y).toRingHom).comp
    (diffPolySumSplit L R k).toRingHom

/-- When `y` is differentially transcendental, substituting it into the right variables is injective:
a nonzero two-family relation cannot vanish. -/
theorem diffPolyEvalRight_injective (y : R → K) (hy : DifferentialIndependent k y) :
    Function.Injective (diffPolyEvalRight (L := L) (k := k) y) := by
  have hmap : Function.Injective
      ⇑(MvPolynomial.map (σ := L × ℕ) (differentialPolynomialEval (C := k) y).toRingHom) := by
    apply MvPolynomial.map_injective
    intro a b hab
    exact hy hab
  have hsplit : Function.Injective ⇑(diffPolySumSplit L R k).toRingHom :=
    (diffPolySumSplit L R k).injective
  rw [diffPolyEvalRight, RingHom.coe_comp]
  exact hmap.comp hsplit

end GaloisForLFunctions
