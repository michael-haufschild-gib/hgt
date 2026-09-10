import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionOrbitBasis

/-!
# Complete nonconstant polynomial connection conjugacy classification

The coefficient degree is not only a necessary invariant: it is sufficient.
Transporting the orbit bases identifies every nonconstant connection with the
same-degree monomial connection as a real linear endomorphism of polynomials.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Transport the complete orbit basis of one nonconstant connection to another. -/
def gomesPolynomialConnectionOrbitTransport
    (A B : GomesNonconstantPolynomialCoefficient) : ℝ[X] ≃ₗ[ℝ] ℝ[X] :=
  (gomesPolynomialConnectionOrbitBasis A).equiv
    (gomesPolynomialConnectionOrbitBasis B) (Equiv.refl ℕ)

/-- Orbit transport preserves the natural basis index. -/
theorem gomesPolynomialConnectionOrbitTransport_basis
    (A B : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionOrbitTransport A B (gomesPolynomialConnectionOrbitBasis A n) =
      gomesPolynomialConnectionOrbitBasis B n :=
  (gomesPolynomialConnectionOrbitBasis A).equiv_apply n
    (gomesPolynomialConnectionOrbitBasis B) (Equiv.refl ℕ)

/-- The canonical orbit transport intertwines exactly when the coefficient degrees agree. -/
theorem gomesPolynomialConnectionOrbitTransport_intertwines_iff
    (A B : GomesNonconstantPolynomialCoefficient) :
    (gomesPolynomialConnectionOrbitTransport A B).toLinearMap.comp
        (gomesPolynomialFirstOrderLinearMap A.val) =
      (gomesPolynomialFirstOrderLinearMap B.val).comp
        (gomesPolynomialConnectionOrbitTransport A B).toLinearMap ↔
      A.val.natDegree = B.val.natDegree := by
  constructor
  · intro h
    exact gomesPolynomialConnectionIntertwiner_degree A.val B.val
      ⟨gomesPolynomialConnectionOrbitTransport A B, h⟩
  · intro h
    apply (gomesPolynomialConnectionOrbitBasis A).ext
    intro n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      gomesPolynomialConnectionOrbitBasis_shift, gomesPolynomialConnectionOrbitTransport_basis, h]

/-- Degree completely classifies real linear conjugacy in the nonconstant sector. -/
theorem gomesPolynomialConnection_nonconstant_intertwiner_iff
    (A B : GomesNonconstantPolynomialCoefficient) :
    Nonempty (GomesPolynomialConnectionIntertwiner A.val B.val) ↔
      A.val.natDegree = B.val.natDegree := by
  constructor
  · rintro ⟨E⟩
    exact gomesPolynomialConnectionIntertwiner_degree A.val B.val E
  · intro h
    exact ⟨⟨gomesPolynomialConnectionOrbitTransport A B,
      (gomesPolynomialConnectionOrbitTransport_intertwines_iff A B).mpr h⟩⟩

/-- Every nonconstant connection has its same-degree monomial normal form. -/
theorem gomesPolynomialConnection_monomial_normal_form
    (A : GomesNonconstantPolynomialCoefficient) :
    Nonempty (GomesPolynomialConnectionIntertwiner A.val (X ^ A.val.natDegree)) := by
  let B : GomesNonconstantPolynomialCoefficient :=
    ⟨X ^ A.val.natDegree, by
      rw [derivative_ne_zero, natDegree_X_pow]
      exact Nat.ne_of_gt (gomesNonconstantPolynomialCoefficient_degree_pos A)⟩
  apply (gomesPolynomialConnection_nonconstant_intertwiner_iff A B).mpr
  exact (natDegree_X_pow A.val.natDegree).symm

/-- Orbit transport within one coefficient is the identity. -/
theorem gomesPolynomialConnectionOrbitTransport_refl
    (A : GomesNonconstantPolynomialCoefficient) :
    gomesPolynomialConnectionOrbitTransport A A = LinearEquiv.refl ℝ ℝ[X] :=
  (gomesPolynomialConnectionOrbitBasis A).equiv_refl

end GaloisForLFunctions.HTGeometry
