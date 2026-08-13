import GaloisForLFunctions.HTGeometry.GenericReparametrization
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Base automorphisms act on the generic reparametrisation

An automorphism of a differential field that commutes with its derivation extends to the generic
reparametrisation, acting on the coefficients and fixing every jet coordinate, and the extension
still commutes with the derivation.

This is what makes the reparametrisation useful for deck theory: the deck transformations of the
base — for the plane, the translations of the variable — survive the passage to a
differential-generic point, with no formula for their action on the coordinates.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

/-- Two integer derivations of a multivariate polynomial ring that agree on the constants and on the
variables are equal. -/
theorem mvPolynomial_derivation_ext {σ K M : Type*} [Field K] [AddCommGroup M]
    [Module (MvPolynomial σ K) M] {D₁ D₂ : Derivation ℤ (MvPolynomial σ K) M}
    (hC : ∀ a : K, D₁ (MvPolynomial.C a) = D₂ (MvPolynomial.C a))
    (hX : ∀ i : σ, D₁ (MvPolynomial.X i) = D₂ (MvPolynomial.X i)) : D₁ = D₂ := by
  ext p
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [Derivation.leibniz, Derivation.leibniz, hp, hX i]

namespace ReparamField

universe u

variable {K : Type u} [Field K] [Differential K]

/-- A base automorphism acts on the jet polynomial ring through its coefficients. -/
noncomputable def polyEquiv (e : K ≃+* K) : ReparamPoly K ≃+* ReparamPoly K :=
  MvPolynomial.mapEquiv ℕ e

@[simp] theorem polyEquiv_C (e : K ≃+* K) (a : K) :
    polyEquiv e (MvPolynomial.C a : ReparamPoly K) = MvPolynomial.C (e a) := by
  simp [polyEquiv]

@[simp] theorem polyEquiv_X (e : K ≃+* K) (i : ℕ) :
    polyEquiv e (MvPolynomial.X i : ReparamPoly K) = MvPolynomial.X i := by
  simp [polyEquiv]

/-- A base automorphism acts on the generic reparametrisation. -/
noncomputable def fieldEquiv (e : K ≃+* K) : ReparamField K ≃+* ReparamField K :=
  IsFractionRing.ringEquivOfRingEquiv (polyEquiv e)

theorem fieldEquiv_algebraMap (e : K ≃+* K) (p : ReparamPoly K) :
    fieldEquiv e (algebraMap (ReparamPoly K) (ReparamField K) p)
      = algebraMap (ReparamPoly K) (ReparamField K) (polyEquiv e p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (polyEquiv e) p

@[simp] theorem fieldEquiv_jet (e : K ≃+* K) (i : ℕ) :
    fieldEquiv e (jet i : ReparamField K) = jet i := by
  rw [jet, fieldEquiv_algebraMap, polyEquiv_X]

theorem fieldEquiv_base (e : K ≃+* K) (a : K) :
    fieldEquiv e (algebraMap K (ReparamField K) a) = algebraMap K (ReparamField K) (e a) := by
  have hb : (algebraMap K (ReparamField K) a)
      = algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.C a) := by
    rw [IsScalarTower.algebraMap_apply K (ReparamPoly K) (ReparamField K)]
    rfl
  have hb' : (algebraMap K (ReparamField K) (e a))
      = algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.C (e a)) := by
    rw [IsScalarTower.algebraMap_apply K (ReparamPoly K) (ReparamField K)]
    rfl
  rw [hb, hb', fieldEquiv_algebraMap, polyEquiv_C]

@[simp] theorem fieldEquiv_symm_jet (e : K ≃+* K) (i : ℕ) :
    (fieldEquiv e).symm (jet i : ReparamField K) = jet i := by
  apply (fieldEquiv e).injective
  rw [RingEquiv.apply_symm_apply, fieldEquiv_jet]

theorem fieldEquiv_symm_base (e : K ≃+* K) (a : K) :
    (fieldEquiv e).symm (algebraMap K (ReparamField K) (e a)) = algebraMap K (ReparamField K) a := by
  apply (fieldEquiv e).injective
  rw [RingEquiv.apply_symm_apply, fieldEquiv_base]

/-- The conjugate of the reparametrisation derivation by a base automorphism. -/
noncomputable def conjDerivation (e : K ≃+* K) :
    Derivation ℤ (ReparamField K) (ReparamField K) := by
  let D : ReparamField K →+ ReparamField K :=
    { toFun := fun z => (fieldEquiv e).symm (fieldDerivation K (fieldEquiv e z))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  refine Derivation.mk' D.toIntLinearMap ?_
  intro x y
  show (fieldEquiv e).symm (fieldDerivation K (fieldEquiv e (x * y)))
    = x • (fieldEquiv e).symm (fieldDerivation K (fieldEquiv e y))
      + y • (fieldEquiv e).symm (fieldDerivation K (fieldEquiv e x))
  rw [map_mul, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul, RingEquiv.symm_apply_apply]

@[simp] theorem conjDerivation_apply (e : K ≃+* K) (z : ReparamField K) :
    conjDerivation e z = (fieldEquiv e).symm (fieldDerivation K (fieldEquiv e z)) := rfl

/-- **A derivation-preserving base automorphism extends to a derivation-preserving automorphism.** -/
theorem fieldEquiv_deriv (e : K ≃+* K)
    (he : ∀ a : K, e (Differential.deriv a) = Differential.deriv (e a)) (z : ReparamField K) :
    fieldEquiv e (z′) = (fieldEquiv e z)′ := by
  have hjet : ∀ i : ℕ,
      conjDerivation e (jet i : ReparamField K) = fieldDerivation K (jet i) := by
    intro i
    rw [conjDerivation_apply, fieldEquiv_jet, ← deriv_eq, deriv_jet, fieldEquiv_symm_jet]
  have hbase : ∀ a : K, conjDerivation e (algebraMap K (ReparamField K) a)
      = fieldDerivation K (algebraMap K (ReparamField K) a) := by
    intro a
    rw [conjDerivation_apply, fieldEquiv_base]
    simp only [← deriv_eq]
    rw [deriv_algebraMap, deriv_algebraMap, ← he a, map_mul, fieldEquiv_symm_jet,
      fieldEquiv_symm_base]
  have hconj : conjDerivation e = fieldDerivation K := by
    refine GaloisForLFunctions.fractionRing_derivation_ext (A := ReparamPoly K)
      (conjDerivation e) (fieldDerivation K) ?_
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hb : (algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.C a))
            = algebraMap K (ReparamField K) a := by
          rw [IsScalarTower.algebraMap_apply K (ReparamPoly K) (ReparamField K)]
          rfl
        rw [hb]
        exact hbase a
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
        have hb : (algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.X i))
            = (jet i : ReparamField K) := rfl
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hb, hjet i]
  have hz := congrArg (fun D => D z) hconj
  simp only [conjDerivation_apply] at hz
  rw [deriv_eq, ← hz]
  exact (fieldEquiv e).apply_symm_apply _

end ReparamField

end GaloisForLFunctions.HTGeometry
