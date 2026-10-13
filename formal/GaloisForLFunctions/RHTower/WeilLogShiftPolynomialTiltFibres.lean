import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltRealization

/-! # All polynomial potentials realizing a prescribed finite law -/

namespace RHTower

open MeasureTheory GaloisForLFunctions.HTGeometry.FourierLLogL

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_atomic_iff_unique_factor
    (r k : ℕ) (Q : Law (Fin (r + 1))) (p : Polynomial ℝ) :
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => p.eval (z 0)) =
      (Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) ↔
    (∀ i, 0 < Q i) ∧ ∃! h : Polynomial ℝ,
      p - finiteWeilCanonicalLogDensityPolynomial r k Q =
        Polynomial.C ((p - finiteWeilCanonicalLogDensityPolynomial r k Q).eval
          (finiteWeilCanonicalFluctuationPoint r k 0 0)) +
        Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) * h := by
  constructor
  · intro heq
    have hQ := Law.pos_of_atomicProbability_tilted_eq
      (finiteWeilCanonicalEdgeLaw r k) Q (finiteWeilCanonicalFluctuationPoint r k)
      (fun i j hij => finiteWeilCanonicalFluctuationPoint_fst_injective r k
        (congrArg (fun z : E => z 0) hij))
      (fun i => finiteWeilCanonicalEdgeMass_pos r k i) (fun z : E => p.eval (z 0)) heq
    refine ⟨hQ, (finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_eq_iff_unique_factor
      r k p (finiteWeilCanonicalLogDensityPolynomial r k Q)).mp ?_⟩
    exact heq.trans (finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k Q hQ).symm
  · rintro ⟨hQ, hfactor⟩
    exact ((finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_eq_iff_unique_factor
      r k p (finiteWeilCanonicalLogDensityPolynomial r k Q)).mpr hfactor).trans
      (finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k Q hQ)

end RHTower
