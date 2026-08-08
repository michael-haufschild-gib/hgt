import GaloisForLFunctions.HTGeometry.StanleyReisnerExponentDetector

/-!
# Multiplying an independent family by a nonzero element of a domain

In an integral domain over a field, translating a linearly independent family by a fixed nonzero
factor preserves linear independence: a vanishing combination of the translates factors as
`(sum c_i f_i) * q`, and a domain lets the nonzero `q` be cancelled.

This is the algebraic step behind the freeness of a complete integral facet orbit.  In the facet
quotient the separator has nonzero class and the quotient is a domain, so the orbit of a separator
under distinct Laurent monomials is independent exactly when the monomials are.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Independence survives multiplication by a nonzero element of a domain.** -/
theorem linearIndependent_mul_const_of_ne_zero {k A ι : Type*} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] {f : ι → A} (hf : LinearIndependent k f) {q : A} (hq : q ≠ 0) :
    LinearIndependent k fun i => f i * q := by
  rw [linearIndependent_iff'] at hf ⊢
  intro s c hsum i hi
  have hfactor : (∑ j ∈ s, c j • f j) * q = 0 := by
    rw [Finset.sum_mul]
    refine hsum.symm ▸ ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc]
  have hzero : (∑ j ∈ s, c j • f j) = 0 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact h
    · exact absurd h hq
  exact hf s c hzero i hi

/-- **Freeness of a separator orbit.**  If the translating family is independent and the separator
has nonzero class in a domain, the whole orbit is independent. -/
theorem linearIndependent_orbit_of_separator {k A ι : Type*} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] {t : ι → A} (ht : LinearIndependent k t) {q : A} (hq : q ≠ 0) :
    LinearIndependent k fun i => t i * q :=
  linearIndependent_mul_const_of_ne_zero ht hq

end GaloisForLFunctions.HTGeometry
