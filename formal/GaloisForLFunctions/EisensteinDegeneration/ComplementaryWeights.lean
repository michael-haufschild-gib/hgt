import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Fintype.BigOperators

/-!
# Complementary weights and regulator cancellation

Weight each class by the regulator values of every other component. All
weighted classes then have the same regulator, without dividing by any
value. Their differences lie in the regulator kernel. For a two-stage
decomposition, the nested complementary weight equals the product of all
factors except the chosen component.

These are the algebraic mechanisms of Polo–Rivero, Proposition 7.7,
Proposition 8.4 and the four-component expansion of Definition 8.5. The
identities concern the weights and classes already supplied; they make no
claim that geometric specialization maps commute.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open scoped BigOperators

section Weights

variable {R ι κ : Type*} [CommMonoid R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The product of the factors complementary to one component. -/
def complementaryWeight (L : ι → R) (i : ι) : R :=
  ∏ j ∈ Finset.univ.erase i, L j

/-- Complementary weighting works at zeros as well as at nonzero values. -/
theorem complementaryWeight_mul (L : ι → R) (i : ι) :
    complementaryWeight L i * L i = ∏ j, L j :=
  Finset.prod_erase_mul Finset.univ L (Finset.mem_univ i)

/-- The two-stage weight is exactly the product over every component except `(i,j)`. -/
theorem nested_complementaryWeight (L : ι → κ → R) (i : ι) (j : κ) :
    complementaryWeight (fun a => ∏ b, L a b) i * complementaryWeight (L i) j =
      complementaryWeight (fun p : ι × κ => L p.1 p.2) (i, j) := by
  let A : Finset (ι × κ) := (Finset.univ.erase i) ×ˢ Finset.univ
  let B : Finset (ι × κ) := {i} ×ˢ (Finset.univ.erase j)
  have hdisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hpA).1).1
      (Finset.mem_singleton.mp (Finset.mem_product.mp hpB).1)
  have hsplit : (Finset.univ : Finset (ι × κ)).erase (i, j) = A ∪ B := by
    ext ⟨a, b⟩
    simp only [A, B, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_product, Finset.mem_singleton]
    by_cases h : a = i
    · subst a
      simp
    · simp [h]
  change (∏ a ∈ Finset.univ.erase i, ∏ b, L a b) *
      (∏ b ∈ Finset.univ.erase j, L i b) =
    ∏ p ∈ (Finset.univ : Finset (ι × κ)).erase (i, j), L p.1 p.2
  rw [hsplit, Finset.prod_union hdisjoint]
  simp only [A, B, Finset.prod_product, Finset.prod_singleton]

end Weights

section Classes

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Weight a class by the regulator values of all the other classes. -/
def weightedComponent (reg : M →ₗ[R] R) (x : ι → M) (i : ι) : M :=
  complementaryWeight (fun j => reg (x j)) i • x i

/-- All complementary-weighted components have the same product regulator. -/
theorem weightedComponent_regulator (reg : M →ₗ[R] R) (x : ι → M) (i : ι) :
    reg (weightedComponent reg x i) = ∏ j, reg (x j) := by
  rw [weightedComponent, map_smul, smul_eq_mul]
  exact complementaryWeight_mul _ i

/-- The weighted difference satisfies the local condition defined by the regulator kernel. -/
theorem weightedComponent_difference_mem_kernel (reg : M →ₗ[R] R) (x : ι → M) (i j : ι) :
    weightedComponent reg x i - weightedComponent reg x j ∈ reg.ker := by
  rw [LinearMap.mem_ker, map_sub, weightedComponent_regulator,
    weightedComponent_regulator, sub_self]

/-- The weighted components give one and the same class in the quotient detected by the
regulator; no nonvanishing or rank assumption is needed for this quotient statement. -/
theorem weightedComponent_quotient_eq (reg : M →ₗ[R] R) (x : ι → M) (i j : ι) :
    (Submodule.Quotient.mk (weightedComponent reg x i) : M ⧸ reg.ker) =
      Submodule.Quotient.mk (weightedComponent reg x j) := by
  apply reg.quotKerEquivRange.injective
  apply Subtype.ext
  change reg (weightedComponent reg x i) = reg (weightedComponent reg x j)
  rw [weightedComponent_regulator, weightedComponent_regulator]

/-- Two successive complementary weightings agree with weighting the full component family
at once. This includes the four components of two binary decompositions. -/
theorem nested_weightedComponent (reg : M →ₗ[R] R) (x : ι → κ → M) (i : ι) (j : κ) :
    complementaryWeight (fun a => ∏ b, reg (x a b)) i •
      weightedComponent reg (x i) j =
        weightedComponent reg (fun p : ι × κ => x p.1 p.2) (i, j) := by
  rw [weightedComponent, smul_smul, nested_complementaryWeight]
  rfl

end Classes

end GaloisForLFunctions.EisensteinDegeneration
