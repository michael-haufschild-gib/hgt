import GaloisForLFunctions.HTGeometry.DifferentialHopfPrimitive
import GaloisForLFunctions.HTGeometry.ParameterizedSpecialization

/-!
# Cassidy's additive classification, evaluated

`DifferentialHopfPrimitive.nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation` is Cassidy's
classification of differential algebraic subgroups of the additive group, in coordinate-ideal form:
every nonzero additive differential Hopf ideal contains a nonzero *linear* differential polynomial.

This file evaluates that statement at a point.  If such an ideal vanishes on a family, the family
satisfies a nonzero finite constant-coefficient linear relation among its jets -- which is the form
in which the classification is used in a hypertranscendence argument, and the form matching
`LogDerivRelationSubgroup.jetOperator`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Cassidy's additive classification, in evaluated form.** -/
theorem exists_nonzero_jet_linear_relation_of_additiveHopfIdeal
    {ι C L : Type*} [Field C] [CharZero C] [CommRing L] [Algebra C L] [Differential L]
    {I : Ideal (DifferentialPolynomial ι C)}
    (hHopf : IsAdditiveDifferentialHopfIdeal I) (hI : I ≠ ⊥)
    (x : ι → L) (hvanish : I ≤ differentialRelationIdeal x) :
    ∃ (P : DifferentialPolynomial ι C) (j : ↥P.support → ι × ℕ), P ≠ 0 ∧
      (∑ s ∈ (Finset.univ : Finset ↥P.support),
        algebraMap C L (MvPolynomial.coeff s.1 P)
          * differentialJet (j s).2 (x (j s).1)) = 0 := by
  classical
  obtain ⟨P, hPI, hP0, j, hj⟩ :=
    nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation hHopf hI
  refine ⟨P, j, hP0, ?_⟩
  have hzero : differentialPolynomialEval (C := C) x P = 0 := by
    have := hvanish hPI
    rw [mem_differentialRelationIdeal_iff] at this
    exact this
  rw [hj, map_sum] at hzero
  rw [← hzero]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, differentialPolynomialEval_X]
  congr 1
  simp [differentialPolynomialEval]

end

end GaloisForLFunctions.HTGeometry
