import GaloisForLFunctions.RHTower.WeilLogShiftFinitePolynomialQuotient
import GaloisForLFunctions.HTGeometry.TiltedEqualityRigidity

/-! # Exact equality fibres of canonical finite polynomial tilts -/

namespace RHTower

open MeasureTheory GaloisForLFunctions.HTGeometry

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_eq_iff_values
    (r k : ℕ) (p q : Polynomial ℝ) :
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => p.eval (z 0)) =
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => q.eval (z 0)) ↔
    ∀ i, p.eval (finiteWeilCanonicalFluctuationPoint r k i 0) -
        q.eval (finiteWeilCanonicalFluctuationPoint r k i 0) =
      p.eval (finiteWeilCanonicalFluctuationPoint r k 0 0) -
        q.eval (finiteWeilCanonicalFluctuationPoint r k 0 0) := by
  rw [tilted_eq_iff_sub_ae_const
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)
    (fun z => p.eval (z 0)) (fun z => q.eval (z 0))
    (finiteWeilCanonicalObservableLaw_integrable r k
      (finiteWeilCanonicalFluctuationPoint r k) _)
    (finiteWeilCanonicalObservableLaw_integrable r k
      (finiteWeilCanonicalFluctuationPoint r k) _)]
  simp only [finiteWeilCanonicalJointProbabilityLaw, finiteWeilCanonicalObservableLaw_ae_iff]
  constructor
  · rintro ⟨c, hc⟩ i
    exact (hc i).trans (hc 0).symm
  · intro h
    exact ⟨_, h⟩

/-- Additive constants and multiples of the nodal polynomial are the entire equality fibre. -/
theorem finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_eq_iff_unique_factor
    (r k : ℕ) (p q : Polynomial ℝ) :
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => p.eval (z 0)) =
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => q.eval (z 0)) ↔
    ∃! h : Polynomial ℝ,
      p - q = Polynomial.C ((p - q).eval (finiteWeilCanonicalFluctuationPoint r k 0 0)) +
        Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) * h := by
  rw [finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_eq_iff_values]
  simpa only [Polynomial.eval_sub] using finite_node_polynomial_constant_iff_unique_factor
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) 0 (p - q)

end RHTower
