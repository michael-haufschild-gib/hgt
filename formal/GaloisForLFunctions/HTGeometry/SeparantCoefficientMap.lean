import GaloisForLFunctions.HTGeometry.DifferentialRelationBaseChange

/-!
# The separant commutes with an injective coefficient map

The separant is the partial derivative at the leader, and an injective coefficient map moves neither
the leader nor a partial derivative.  So pushing coefficients forward commutes with taking the
separant.

Reduction arguments state their hypotheses with the separant of the *mapped* characteristic while the
constructions produce the *mapped* separant; this is the identification between them.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K L : Type*} [CommRing K] [CommRing L]

/-- **An injective coefficient map preserves the leader.** -/
theorem scalarDifferentialPolynomialLeader_map {f : K →+* L} (hf : Function.Injective f)
    (P : DifferentialPolynomial Unit K) :
    scalarDifferentialPolynomialLeader (MvPolynomial.map f P)
      = scalarDifferentialPolynomialLeader P := by
  rw [scalarDifferentialPolynomialLeader, scalarDifferentialPolynomialLeader,
    scalarDifferentialPolynomialOrder_map hf P]

/-- **The separant commutes with an injective coefficient map.** -/
theorem scalarDifferentialPolynomialSeparant_map {f : K →+* L} (hf : Function.Injective f)
    (P : DifferentialPolynomial Unit K) :
    scalarDifferentialPolynomialSeparant (MvPolynomial.map f P)
      = MvPolynomial.map f (scalarDifferentialPolynomialSeparant P) := by
  rw [scalarDifferentialPolynomialSeparant, scalarDifferentialPolynomialSeparant,
    scalarDifferentialPolynomialLeader_map hf P, MvPolynomial.pderiv_map]

end

end GaloisForLFunctions
