import GaloisForLFunctions.HTGeometry.UniformizerPowerBasis

/-!
# The minimal polynomial of a uniformizer has degree the ramification index

The minimal polynomial divides any monic relation, so its degree is at most the ramification index.
It cannot be smaller: a relation of smaller degree would be a nontrivial dependence among powers of
the uniformizer below the index, and those are independent.

This is the degree identification the different needs, since the tame computation of the derivative
applies to a monic polynomial whose degree is exactly the ramification index.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

/-- **The minimal polynomial of a uniformizer has degree the ramification index.** -/
theorem natDegree_minpoly_eq_ramificationIndex {πA : A} (hπA : Irreducible πA) (e : ℕ)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1)
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e) (hroot : aeval x g = 0) :
    (minpoly A x).natDegree = e := by
  have hint : IsIntegral A x := ⟨g, hmonic, hroot⟩
  have hle : (minpoly A x).natDegree ≤ e := by
    have hdeg' := minpoly.min A x hmonic hroot
    have hnat := Polynomial.natDegree_le_natDegree hdeg'
    rwa [hdeg] at hnat
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hsum : ∑ i : Fin e, (minpoly A x).coeff (i : ℕ) • x ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (minpoly A x).coeff j • x ^ j) e]
    have hrange : Finset.range ((minpoly A x).natDegree + 1) ⊆ Finset.range e := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    rw [← Finset.sum_subset hrange ?_]
    · rw [← Polynomial.aeval_eq_sum_range]
      exact minpoly.aeval A x
    · intro i _ hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hi), zero_smul]
  have hli := linearIndependent_pow hπA e hram hx
  rw [linearIndependent_iff'] at hli
  have hzero := hli Finset.univ (fun i => (minpoly A x).coeff (i : ℕ)) hsum
    ⟨(minpoly A x).natDegree, hlt⟩ (Finset.mem_univ _)
  rw [(minpoly.monic hint).coeff_natDegree] at hzero
  exact one_ne_zero hzero

end GaloisForLFunctions.HTGeometry
