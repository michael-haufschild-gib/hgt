import GaloisForLFunctions.HTGeometry.ProductLawBaseCase

/-!
# From the rational model back to the polynomial one

The product law of a cascade of first-order linear entire maps is polynomial in the states, so its
model lives in the polynomial ring; the fraction field was needed only to run the determinant
argument.  The two laws agree, because two derivations of a polynomial ring into any module that agree
on the variables are equal, so the polynomial jets map onto the rational ones.

Algebraic independence over `ℂ` therefore transfers back along the (injective) inclusion, and the
analytic transfer theorem applies to the polynomial model as it stands.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The product law on the polynomial ring. -/
noncomputable def polyProdDerivation :
    Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun k =>
    (∏ j ∈ Finset.range k, univFactor (Q j) j) * univFactor (v k) k

@[simp] theorem polyProdDerivation_X (k : ℕ) :
    polyProdDerivation Q v (MvPolynomial.X k)
      = (∏ j ∈ Finset.range k, univFactor (Q j) j) * univFactor (v k) k :=
  MvPolynomial.mkDerivation_X ℂ _ k

/-- The polynomial law's value at a variable maps to the rational jet. -/
theorem algebraMap_polyProdDerivation_X (k : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField
        ((∏ j ∈ Finset.range k, univFactor (Q j) j) * univFactor (v k) k)
      = prodJet Q v k := by
  rw [map_mul, map_prod, prodJet_eq, prodHead]
  rfl

/-- **The polynomial law maps onto the rational one.** -/
theorem algebraMap_polyProdDerivation (P : MvPolynomial ℕ ℂ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (polyProdDerivation Q v P)
      = prodDerivation Q v (algebraMap (MvPolynomial ℕ ℂ) CascadeField P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) c from rfl,
        (polyProdDerivation Q v).map_algebraMap, map_zero,
        ← IsScalarTower.algebraMap_apply ℂ (MvPolynomial ℕ ℂ) CascadeField,
        (prodDerivation Q v).map_algebraMap]
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p k hp =>
      have hsmul : (polyProdDerivation Q v) (p * MvPolynomial.X k)
          = p * (polyProdDerivation Q v) (MvPolynomial.X k)
            + MvPolynomial.X k * (polyProdDerivation Q v) p := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      have hfield : prodDerivation Q v
          (algebraMap (MvPolynomial ℕ ℂ) CascadeField p
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k))
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField p
              * prodDerivation Q v (algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k))
            + algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k)
              * prodDerivation Q v (algebraMap (MvPolynomial ℕ ℂ) CascadeField p) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      rw [hsmul, map_add, map_mul, map_mul, hp, polyProdDerivation_X,
        algebraMap_polyProdDerivation_X, map_mul, hfield,
        show algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k) = fx k from rfl,
        prodDerivation_fx]

/-- The jets of the polynomial law map onto the jets of the rational one. -/
theorem algebraMap_iterate_polyProdDerivation (P : MvPolynomial ℕ ℂ) (i : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField
        (((polyProdDerivation Q v : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) P)
      = ((prodDerivation Q v : CascadeField → CascadeField)^[i])
        (algebraMap (MvPolynomial ℕ ℂ) CascadeField P) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        algebraMap_polyProdDerivation, ih]

/-- **Algebraic independence transfers back to the polynomial model.** -/
theorem algebraicIndependent_of_field {ι : Type*} {x : ι → MvPolynomial ℕ ℂ}
    (h : AlgebraicIndependent ℂ
      (fun i => algebraMap (MvPolynomial ℕ ℂ) CascadeField (x i))) :
    AlgebraicIndependent ℂ x := by
  refine AlgebraicIndependent.of_comp
    (IsScalarTower.toAlgHom ℂ (MvPolynomial ℕ ℂ) CascadeField) ?_
  exact h

end GaloisForLFunctions.HTGeometry
