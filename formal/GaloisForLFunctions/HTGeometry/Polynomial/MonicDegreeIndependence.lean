import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# Distinct-degree monic polynomials over rings

The largest-degree term of a finite relation has coefficient equal to its scalar.
Thus monic polynomials of distinct degrees remain independent over rings with zero
divisors, including residue rings modulo prime powers.
-/

namespace GaloisForLFunctions

open Polynomial

/-- Distinct-degree monic polynomials are independent over every commutative ring. -/
theorem linearIndependent_monic_of_natDegree_injective
    {ι R : Type*} [Fintype ι] [CommRing R] {p : ι → R[X]}
    (hm : ∀ i, (p i).Monic) (hd : Function.Injective fun i => (p i).natDegree) :
    LinearIndependent R p := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := h
  let s := Finset.univ.filter fun i => c i ≠ 0
  have hs : s.Nonempty := ⟨i, by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => (p i).natDegree) hs
  have hcoeff := congrArg (fun q : R[X] => q.coeff (p j).natDegree) hc
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_zero] at hcoeff
  have hsingle : ∑ i, c i * (p i).coeff (p j).natDegree = c j := by
    rw [Finset.sum_eq_single j]
    · rw [(hm j).coeff_natDegree, mul_one]
    · intro k _ hkj
      by_cases hk : c k = 0
      · rw [hk, zero_mul]
      · have hks : k ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hk
        have hlt : (p k).natDegree < (p j).natDegree :=
          lt_of_le_of_ne (hmax k hks) (fun h => hkj (hd h))
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    · intro hj'
      exact (hj' (Finset.mem_univ j)).elim
  rw [hsingle] at hcoeff
  exact (Finset.mem_filter.mp hj).2 hcoeff

end GaloisForLFunctions
