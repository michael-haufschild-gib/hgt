import GaloisForLFunctions.HTGeometry.WickFieldTheorem
import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute

/-!
# The bosonic Fock model: a concrete creation/annihilation system with a vacuum

The polynomial algebra `MvPolynomial ι K` is the Fock space of a free boson with modes indexed by
`ι`: the monomials are the occupation-number states, the constant `1` is the vacuum, multiplication
by `X i` creates a quantum in mode `i`, and `∂/∂X i` destroys one.  These operators satisfy the
canonical commutation relations exactly,

```text
∂ᵢ (Xⱼ · p) = Xⱼ · ∂ᵢ p + δᵢⱼ p ,
```

and the constant term of `T 1` is a vacuum expectation: a creation operator on the left contributes
a factor `X i` with no constant term, and an annihilation operator on the right differentiates the
vacuum to zero.

This makes `WickSystem` and `WickVacuum` non-vacuous and specialises Wick's theorem to the
statement that the vacuum expectation of an ordered word in the `Xᵢ` and `∂ᵢ` is the sum over the
perfect matchings of the word of the products of the Kronecker propagators `δᵢⱼ`.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable (K : Type u) [CommRing K] (ι : Type w) [DecidableEq ι]

/-- Creation: multiplication by the variable `X i` on the polynomial Fock space. -/
noncomputable def fockCre (i : ι) : Module.End K (MvPolynomial ι K) :=
  LinearMap.mulLeft K (X i)

/-- Annihilation: the partial derivative in the direction `X i`. -/
noncomputable def fockAnn (i : ι) : Module.End K (MvPolynomial ι K) :=
  (pderiv i : Derivation K (MvPolynomial ι K) (MvPolynomial ι K)).toLinearMap

omit [DecidableEq ι] in
@[simp] theorem fockCre_apply (i : ι) (p : MvPolynomial ι K) :
    fockCre K ι i p = X i * p := rfl

omit [DecidableEq ι] in
@[simp] theorem fockAnn_apply (i : ι) (p : MvPolynomial ι K) :
    fockAnn K ι i p = pderiv i p := rfl

/-- **The bosonic Fock creation/annihilation system.**  The elementary contraction is the Kronecker
delta: the propagator of a free boson between two modes. -/
noncomputable def bosonicFock : WickSystem K (Module.End K (MvPolynomial ι K)) ι where
  cre := fockCre K ι
  ann := fockAnn K ι
  κ i j := if j = i then 1 else 0
  cre_mul_cre i j := by
    refine LinearMap.ext fun p => ?_
    simp only [Module.End.mul_apply, fockCre_apply]
    rw [← mul_assoc, ← mul_assoc, mul_comm (X i) (X j)]
  ann_mul_ann i j := by
    refine LinearMap.ext fun p => ?_
    simp only [Module.End.mul_apply, fockAnn_apply]
    exact GaloisForLFunctions.pderiv_comm i j p
  ann_mul_cre i j := by
    refine LinearMap.ext fun p => ?_
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      fockAnn_apply, fockCre_apply, pderiv_mul]
    by_cases h : j = i
    · subst h
      simp [add_comm]
    · simp [pderiv_X_of_ne h, h]

@[simp] theorem bosonicFock_cre (i : ι) : (bosonicFock K ι).cre i = fockCre K ι i := rfl
@[simp] theorem bosonicFock_ann (i : ι) : (bosonicFock K ι).ann i = fockAnn K ι i := rfl

@[simp] theorem bosonicFock_contract_ann_cre (i j : ι) :
    (bosonicFock K ι).contract (.ann i) (.cre j) = if j = i then 1 else 0 := rfl

/-- The vacuum expectation on the polynomial Fock space: the constant term of the image of `1`. -/
noncomputable def fockVacuumFunctional : Module.End K (MvPolynomial ι K) →ₗ[K] K where
  toFun T := constantCoeff (T 1)
  map_add' T S := by simp
  map_smul' c T := by simp [MvPolynomial.smul_eq_C_mul]

omit [DecidableEq ι] in
@[simp] theorem fockVacuumFunctional_apply (T : Module.End K (MvPolynomial ι K)) :
    fockVacuumFunctional K ι T = constantCoeff (T 1) := rfl

/-- **The Fock vacuum.**  Creation operators on the left have no constant term; annihilation
operators on the right differentiate the vacuum away. -/
noncomputable def fockVacuum : WickVacuum (bosonicFock K ι) where
  ω := fockVacuumFunctional K ι
  ω_one := by simp
  ω_cre i x := by
    simp only [fockVacuumFunctional_apply, Module.End.mul_apply, bosonicFock_cre, fockCre_apply,
      map_mul, constantCoeff_X, zero_mul]
  ω_ann i x := by
    simp only [fockVacuumFunctional_apply, Module.End.mul_apply, bosonicFock_ann, fockAnn_apply,
      pderiv_one, map_zero]

/-- **Wick's theorem on the bosonic Fock space.**  The constant term of an ordered word in the
multiplication and differentiation operators, applied to the vacuum `1`, is the sum over the perfect
matchings of the word of the products of the Kronecker propagators. -/
theorem bosonicFock_vacuum_prod_op (l : List (WickMode ι)) :
    constantCoeff ((l.map (bosonicFock K ι).op).prod (1 : MvPolynomial ι K))
      = completePairing (bosonicFock K ι).contract l :=
  (fockVacuum K ι).vacuum_prod_op l

@[simp] theorem bosonicFock_κ (i j : ι) :
    (bosonicFock K ι).κ i j = if j = i then 1 else 0 := rfl

/-- The free bosonic field of a mode: creation plus annihilation, i.e. multiplication by the
variable plus differentiation in its direction. -/
theorem bosonicFock_field_apply (i : ι) (p : MvPolynomial ι K) :
    (bosonicFock K ι).field i p = X i * p + pderiv i p := rfl

/-- **Wick's theorem for the free bosonic field.**  The vacuum expectation of a product of the
fields `Xᵢ · + ∂ᵢ` is the sum over the perfect matchings of the word of the products of the
Kronecker propagators. -/
theorem bosonicFock_vacuum_prod_field (l : List ι) :
    constantCoeff ((l.map (bosonicFock K ι).field).prod (1 : MvPolynomial ι K))
      = completePairing (fun i j => if j = i then (1 : K) else 0) l :=
  (fockVacuum K ι).vacuum_prod_field l

end GaloisForLFunctions.HTGeometry
