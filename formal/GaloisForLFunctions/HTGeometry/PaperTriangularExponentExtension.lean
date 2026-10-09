import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Triangular extensions of injective monomial substitutions

Adjoin extra variables multiplied by one fixed core monomial. Their exponents
remain visible in the extra coordinates. After recovering those exponents,
the common core contribution cancels. This constructs larger independent
families for the paper's associated-graded mechanism without dividing in a
coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α β : Type*} [Fintype β]

private def triangularExponentProductMap (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) :
    ((α →₀ ℕ) × (β →₀ ℕ)) →+ ((α →₀ ℕ) × (β →₀ ℕ)) where
  toFun d := (A d.1 + (∑ j, d.2 j) • v, d.2)
  map_zero' := by simp
  map_add' d e := by
    simp [Finset.sum_add_distrib, add_nsmul, add_assoc, add_left_comm, add_comm]

/-- Extend an exponent map by extra coordinates with a common core contribution. -/
def paperTriangularExponentMap (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) :
    (α ⊕ β →₀ ℕ) →+ (α ⊕ β →₀ ℕ) :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm.toAddMonoidHom.comp
    ((triangularExponentProductMap A v).comp Finsupp.sumFinsuppAddEquivProdFinsupp.toAddMonoidHom)

/-- The extra coordinates recover themselves before the original exponent map is inverted. -/
theorem paperTriangularExponentMap_injective
    (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) (hA : Function.Injective A) :
    Function.Injective (paperTriangularExponentMap (β := β) A v) := by
  have ht : Function.Injective (triangularExponentProductMap (β := β) A v) := by
    intro d e h
    change (A d.1 + (∑ j, d.2 j) • v, d.2) =
      (A e.1 + (∑ j, e.2 j) • v, e.2) at h
    obtain ⟨hl, hr⟩ := Prod.mk.inj h
    rw [hr] at hl
    exact Prod.ext (hA (add_right_cancel hl)) hr
  exact Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective.comp
    (ht.comp Finsupp.sumFinsuppAddEquivProdFinsupp.injective)

/-- A core variable keeps its original transformed core exponent. -/
theorem paperTriangularExponentMap_single_inl
    (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) (i : α) :
    paperTriangularExponentMap (β := β) A v (Finsupp.single (Sum.inl i) 1) =
      Finsupp.sumElim (A (Finsupp.single i 1)) 0 := by
  have hs : (Finsupp.sumFinsuppAddEquivProdFinsupp
      (Finsupp.single (Sum.inl i) 1 : α ⊕ β →₀ ℕ)) = (Finsupp.single i 1, 0) := by
    apply Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective
    rw [AddEquiv.symm_apply_apply]
    exact (Finsupp.sumElim_single_zero i 1).symm
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm
    (triangularExponentProductMap A v (Finsupp.sumFinsuppAddEquivProdFinsupp _)) = _
  rw [hs]
  simp only [triangularExponentProductMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finsupp.zero_apply, Finset.sum_const_zero, zero_nsmul, add_zero]
  rfl

/-- An extra variable gains exactly one copy of the chosen core monomial. -/
theorem paperTriangularExponentMap_single_inr
    (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) (j : β) :
    paperTriangularExponentMap A v (Finsupp.single (Sum.inr j) 1) =
      Finsupp.sumElim v (Finsupp.single j 1) := by
  classical
  have hs : (Finsupp.sumFinsuppAddEquivProdFinsupp
      (Finsupp.single (Sum.inr j) 1 : α ⊕ β →₀ ℕ)) = (0, Finsupp.single j 1) := by
    apply Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective
    rw [AddEquiv.symm_apply_apply]
    exact (Finsupp.sumElim_zero_single j 1).symm
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm
    (triangularExponentProductMap A v (Finsupp.sumFinsuppAddEquivProdFinsupp _)) = _
  rw [hs]
  simp only [triangularExponentProductMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_zero, Finsupp.single_apply]
  simp

variable (K : Type*) [CommSemiring K]

/-- The characteristic-free polynomial substitution induced by the triangular exponent map. -/
def paperTriangularMonomialMap (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) :
    MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial (α ⊕ β) K :=
  AddMonoidAlgebra.mapDomainAlgHom K K (paperTriangularExponentMap A v)

/-- Triangular extension preserves injectivity over arbitrary commutative coefficient semirings. -/
theorem paperTriangularMonomialMap_injective
    (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) (hA : Function.Injective A) :
    Function.Injective (paperTriangularMonomialMap (β := β) K A v) :=
  AddMonoidAlgebra.mapDomain_injective (paperTriangularExponentMap_injective A v hA)

/-- The polynomial images are the monomials specified by the extended exponent map. -/
theorem paperTriangularMonomialMap_X
    (A : (α →₀ ℕ) →+ (α →₀ ℕ)) (v : α →₀ ℕ) (i : α ⊕ β) :
    paperTriangularMonomialMap K A v (MvPolynomial.X i) =
      MvPolynomial.monomial (paperTriangularExponentMap A v (Finsupp.single i 1)) 1 := by
  change AddMonoidAlgebra.mapDomain (paperTriangularExponentMap A v)
    (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : K)) = _
  exact AddMonoidAlgebra.mapDomain_single

end

end GaloisForLFunctions.HTGeometry
