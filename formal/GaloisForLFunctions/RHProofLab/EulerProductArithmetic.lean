import Mathlib.Tactic

/-!
# Finite Euler-product arithmetic

This module is a proof lab for the finite algebra behind Euler products.  It
does not assert an Euler product for any analytic object.  It isolates the
combinatorial part that an RH-relevant construction repeatedly needs: local
factor products expand into squarefree subset monomials, and disjoint prime
blocks multiply independently.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHProofLab

noncomputable section

section FiniteEulerProduct

variable {ι R : Type*} [DecidableEq ι] [CommSemiring R]

/-- A finite toy Euler product with one local coefficient per index. -/
def finiteLocalEulerProduct (S : Finset ι) (a : ι → R) : R :=
  ∏ i ∈ S, (1 + a i)

/-- The squarefree monomial attached to a subset of local indices. -/
def squarefreeMonomial (a : ι → R) (T : Finset ι) : R :=
  ∏ i ∈ T, a i

/-- The coefficient of a squarefree subset in the finite Euler expansion. -/
def squarefreeEulerCoeff (S T : Finset ι) (a : ι → R) : R :=
  if T ⊆ S then squarefreeMonomial a T else 0

/-- A subset has exactly its squarefree monomial as coefficient. -/
@[aesop safe]
theorem squarefreeEulerCoeff_of_subset
    {S T : Finset ι} {a : ι → R} (hT : T ⊆ S) :
    squarefreeEulerCoeff S T a = squarefreeMonomial a T := by
  simp [squarefreeEulerCoeff, hT]

/-- A non-subset has coefficient zero in the finite Euler expansion. -/
@[aesop safe]
theorem squarefreeEulerCoeff_of_not_subset
    {S T : Finset ι} {a : ι → R} (hT : ¬ T ⊆ S) :
    squarefreeEulerCoeff S T a = 0 := by
  simp [squarefreeEulerCoeff, hT]

/-- The finite Euler product expands as the sum of all squarefree subset monomials. -/
@[aesop safe]
theorem finiteLocalEulerProduct_subsetExpansion
    (S : Finset ι) (a : ι → R) :
    finiteLocalEulerProduct S a =
      ∑ T ∈ S.powerset, squarefreeMonomial a T := by
  rw [show finiteLocalEulerProduct S a = ∏ i ∈ S, (a i + 1) by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [add_comm]]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro T _hT
  simp [squarefreeMonomial]

/-- The same expansion stated with the explicit squarefree coefficient function. -/
@[aesop safe]
theorem finiteLocalEulerProduct_squarefreeCoeffExpansion
    (S : Finset ι) (a : ι → R) :
    finiteLocalEulerProduct S a =
      ∑ T ∈ S.powerset, squarefreeEulerCoeff S T a := by
  rw [finiteLocalEulerProduct_subsetExpansion]
  refine Finset.sum_congr rfl ?_
  intro T hT
  exact (squarefreeEulerCoeff_of_subset (Finset.mem_powerset.mp hT)).symm

/-- Inserting one new local index multiplies the finite Euler product by its local factor. -/
@[aesop safe]
theorem finiteLocalEulerProduct_insert
    {S : Finset ι} {i : ι} {a : ι → R} (hi : i ∉ S) :
    finiteLocalEulerProduct (insert i S) a =
      (1 + a i) * finiteLocalEulerProduct S a := by
  simp [finiteLocalEulerProduct, hi]

/-- Disjoint finite local blocks multiply independently. -/
@[aesop safe]
theorem finiteLocalEulerProduct_union_of_disjoint
    {A B : Finset ι} {a : ι → R} (hdisj : Disjoint A B) :
    finiteLocalEulerProduct (A ∪ B) a =
      finiteLocalEulerProduct A a * finiteLocalEulerProduct B a := by
  simp [finiteLocalEulerProduct, Finset.prod_union hdisj]

/-- Squarefree monomials also split over disjoint unions. -/
@[aesop safe]
theorem squarefreeMonomial_union_of_disjoint
    {A B : Finset ι} {a : ι → R} (hdisj : Disjoint A B) :
    squarefreeMonomial a (A ∪ B) =
      squarefreeMonomial a A * squarefreeMonomial a B := by
  simp [squarefreeMonomial, Finset.prod_union hdisj]

end FiniteEulerProduct

end

end GaloisForLFunctions.RHProofLab
