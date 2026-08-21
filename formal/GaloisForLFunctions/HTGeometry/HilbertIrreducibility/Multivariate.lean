import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Kronecker
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Main
import GaloisForLFunctions.HTGeometry.PrimeSubsetFactor
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Hilbert irreducibility in several variables

Kronecker substitution reduces the specialization of one variable of a multivariate irreducible
polynomial to the two-variable case: a factorization of the specialized polynomial is transported,
through the degree-bounded bijection `kron`, to a factorization of the original one.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial MvPolynomial

/-- A nonzero polynomial over `ℚ[X]` is a constant in `Y` times a finite family of irreducible
factors of positive `Y`-degree. -/
theorem exists_factorisation {P : Polynomial (Polynomial ℚ)} (hP : P ≠ 0) :
    ∃ (n : ℕ) (g₀ : Polynomial ℚ) (g : Fin n → Polynomial (Polynomial ℚ)),
      g₀ ≠ 0 ∧ (∀ i, Irreducible (g i)) ∧ (∀ i, 1 ≤ (g i).natDegree) ∧
      P = Polynomial.C g₀ * ∏ i, g i := by
  classical
  set L := UniqueFactorizationMonoid.factors P with hL
  have hirr : ∀ q ∈ L, Irreducible q := fun q hq =>
    UniqueFactorizationMonoid.irreducible_of_factor q hq
  set L1 : Multiset (Polynomial (Polynomial ℚ)) := L.filter (fun q => 1 ≤ q.natDegree) with hL1
  set L0 : Multiset (Polynomial (Polynomial ℚ)) := L.filter (fun q => ¬ (1 ≤ q.natDegree)) with hL0
  have hsplit : L1 + L0 = L := Multiset.filter_add_not _ L
  have hprodL : L0.prod * L1.prod = L.prod := by
    rw [← hsplit, Multiset.prod_add, mul_comm]
  have h0ne : (0 : Polynomial (Polynomial ℚ)) ∉ L0 := fun h0 =>
    (hirr 0 (Multiset.mem_of_mem_filter h0)).ne_zero rfl
  have hdeg0 : L0.prod.natDegree = 0 := by
    rw [Polynomial.natDegree_multiset_prod L0 h0ne]
    refine Multiset.sum_eq_zero ?_
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
    have := (Multiset.mem_filter.mp hq).2
    omega
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
  have hL0ne : L0.prod ≠ 0 := Multiset.prod_ne_zero h0ne
  have hane : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact hL0ne ha.symm
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hP
  obtain ⟨r, hr, hrC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hrne : r ≠ 0 := hr.ne_zero
  have hlist : L1.prod = ∏ i : Fin L1.toList.length, L1.toList.get i := by
    rw [← Multiset.prod_toList]
    conv_lhs => rw [← List.ofFn_get L1.toList]
    rw [List.prod_ofFn]
  refine ⟨L1.toList.length, a * r, fun i => L1.toList.get i, mul_ne_zero hane hrne, ?_, ?_, ?_⟩
  · intro i
    exact hirr _ (Multiset.mem_of_mem_filter (Multiset.mem_toList.mp (List.get_mem _ i)))
  · intro i
    exact (Multiset.mem_filter.mp (Multiset.mem_toList.mp (List.get_mem _ i))).2
  · rw [← hlist, map_mul, ← hu, ← hprodL, ← ha, hrC]
    ring

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
