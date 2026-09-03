import GaloisForLFunctions.HTGeometry.EntireFirstOrderWimanInitialData
import GaloisForLFunctions.HTGeometry.PolynomialGaussAscent

/-!
# Irreducible derivative polynomial over the rational state field

The irreducible analytic Wiman relation remains irreducible after singling out the derivative
coordinate and passing from the polynomial state ring to its fraction field.  This is the exact
component-uniqueness bridge required before a prescribed Newton place can be transported to the
actual derivative field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The two indices left after removing the derivative coordinate. -/
noncomputable def firstOrderStateIndexEquiv :
    {j : Fin 3 // j ≠ (2 : Fin 3)} ≃ Fin 2 :=
  Equiv.ofBijective
    (fun j => (⟨j.1.val, by omega⟩ : Fin 2))
    ⟨fun i j hij => by
        apply Subtype.ext
        apply Fin.ext
        have hval := congrArg (fun x : Fin 2 => x.val) hij
        exact hval,
      fun j => by
        let i : Fin 3 := ⟨j.val, by omega⟩
        have hi : i ≠ (2 : Fin 3) := by
          intro h
          have := congrArg Fin.val h
          change j.val = 2 at this
          omega
        exact ⟨⟨i, hi⟩, Fin.ext rfl⟩⟩

/-- Literal iterated polynomial ring `ℂ[U][V]` for the clock and value coordinates. -/
abbrev FirstOrderStatePolynomialRing := Polynomial (Polynomial ℂ)

/-- The remaining-coordinate multivariable ring is exactly the iterated state polynomial ring. -/
noncomputable def firstOrderStatePolynomialEquiv :
    MvPolynomial {j : Fin 3 // j ≠ (2 : Fin 3)} ℂ ≃ₐ[ℂ]
      FirstOrderStatePolynomialRing :=
  (MvPolynomial.renameEquiv ℂ firstOrderStateIndexEquiv).trans
    ((MvPolynomial.finSuccEquiv ℂ 1).trans
      (Polynomial.mapAlgEquiv
        ((MvPolynomial.finSuccEquiv ℂ 0).trans
          (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0))))))

/-- Rational function field in the clock and value coordinates. -/
abbrev FirstOrderRationalStateField := FractionRing FirstOrderStatePolynomialRing

/-- A three-variable relation viewed literally as a polynomial in the derivative coordinate. -/
noncomputable def firstOrderDerivativePolynomialOverStateRing
    (P : MvPolynomial (Fin 3) ℂ) : Polynomial FirstOrderStatePolynomialRing :=
  (mvPolynomialPolynomialEquivAt (2 : Fin 3) P).map
    firstOrderStatePolynomialEquiv.toRingHom

/-- The derivative polynomial after passing to the rational clock/value state field. -/
noncomputable def firstOrderDerivativePolynomial
    (P : MvPolynomial (Fin 3) ℂ) : Polynomial FirstOrderRationalStateField :=
  (firstOrderDerivativePolynomialOverStateRing P).map
    (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField)

set_option maxHeartbeats 1000000 in
/-- The split derivative polynomial has positive degree for every exact Wiman package. -/
theorem firstOrderDerivativePolynomialOverStateRing_natDegree_pos
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    0 < (firstOrderDerivativePolynomialOverStateRing data.P).natDegree := by
  rw [firstOrderDerivativePolynomialOverStateRing]
  rw [Polynomial.natDegree_map_eq_of_injective firstOrderStatePolynomialEquiv.injective,
    mvPolynomialPolynomialEquivAt_apply,
    ← mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt]
  exact Nat.pos_of_ne_zero
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp data.derivative_mem_vars)

/-- The source irreducibility survives splitting off the derivative coordinate. -/
theorem firstOrderDerivativePolynomialOverStateRing_irreducible
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    Irreducible (firstOrderDerivativePolynomialOverStateRing data.P) := by
  exact (data.polynomial_irreducible.map
      (mvPolynomialPolynomialEquivAt (2 : Fin 3))).map
    (Polynomial.mapAlgEquiv firstOrderStatePolynomialEquiv)

/-- The split derivative polynomial is primitive over the polynomial state ring. -/
theorem firstOrderDerivativePolynomialOverStateRing_primitive
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    (firstOrderDerivativePolynomialOverStateRing data.P).IsPrimitive :=
  isPrimitive_of_irreducible
    (firstOrderDerivativePolynomialOverStateRing_irreducible data)
    (firstOrderDerivativePolynomialOverStateRing_natDegree_pos data)

/-- **Irreducible derivative component.**  The exact Wiman relation is irreducible over the
rational state field `ℂ(U,V)`, not merely in `ℂ[U,V,W]`. -/
theorem firstOrderDerivativePolynomial_irreducible
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    Irreducible (firstOrderDerivativePolynomial data.P) := by
  exact GaloisForLFunctions.Polynomial.IsPrimitive.irreducible_fraction_map
    (firstOrderDerivativePolynomialOverStateRing_primitive data)
    (firstOrderDerivativePolynomialOverStateRing_irreducible data)

/-- Passing to the rational state field preserves the positive derivative degree exactly. -/
theorem firstOrderDerivativePolynomial_natDegree
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    (firstOrderDerivativePolynomial data.P).natDegree =
      (firstOrderDerivativePolynomialOverStateRing data.P).natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective
      FirstOrderStatePolynomialRing FirstOrderRationalStateField) _

/-- The rational-state derivative polynomial is nonconstant. -/
theorem firstOrderDerivativePolynomial_natDegree_pos
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    0 < (firstOrderDerivativePolynomial data.P).natDegree := by
  rw [firstOrderDerivativePolynomial_natDegree data]
  exact firstOrderDerivativePolynomialOverStateRing_natDegree_pos data

end

end GaloisForLFunctions.HTGeometry
