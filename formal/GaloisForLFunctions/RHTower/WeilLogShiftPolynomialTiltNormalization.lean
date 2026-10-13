import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltFibres

/-! # The unique normalized polynomial parameter for every positive finite law -/

namespace RHTower

open MeasureTheory GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem finiteWeilCanonicalLogDensityPolynomial_partition_eq_one_of_pos
    (r k : ℕ) (Q : Law (Fin (r + 1))) (hQ : ∀ i, 0 < Q i) :
    (∫ z, Real.exp ((finiteWeilCanonicalLogDensityPolynomial r k Q).eval (z 0))
      ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) = 1 := by
  rw [finiteWeilCanonicalJointProbabilityLaw, finiteWeilCanonicalObservableLaw_integral_real]
  calc
    (∑ i, finiteWeilCanonicalEdgeMass r k i *
        Real.exp ((finiteWeilCanonicalLogDensityPolynomial r k Q).eval
          (finiteWeilCanonicalFluctuationPoint r k i 0))) = ∑ i, Q i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [finiteWeilCanonicalLogDensityPolynomial_eval_at_atom,
        Real.exp_log (div_pos (hQ i) (finiteWeilCanonicalEdgeMass_pos r k i)),
        mul_comm, div_mul_cancel₀ _ (finiteWeilCanonicalEdgeMass_pos r k i).ne']
    _ = 1 := Q.total

/-- Degree and partition normalization remove every ambiguity in a polynomial potential. -/
theorem finiteWeilCanonicalJointProbabilityLaw_normalized_polynomial_tilt_iff
    (r k : ℕ) (Q : Law (Fin (r + 1))) (p : Polynomial ℝ) :
    (p.degree < (r + 1 : ℕ) ∧
      (∫ z, Real.exp (p.eval (z 0))
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) = 1 ∧
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => p.eval (z 0)) =
        (Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E)) ↔
    (∀ i, 0 < Q i) ∧ p = finiteWeilCanonicalLogDensityPolynomial r k Q := by
  constructor
  · rintro ⟨hdegree, hpartition, heq⟩
    have hQ := ((finiteWeilCanonicalJointProbabilityLaw_polynomial_tilt_atomic_iff_unique_factor
      r k Q p).mp heq).1
    have hcanonical := finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k Q hQ
    have hcanonicalPartition := finiteWeilCanonicalLogDensityPolynomial_partition_eq_one_of_pos
      r k Q hQ
    have hlogp := log_rnDeriv_tilted_left_self
      (μ := (finiteWeilCanonicalJointProbabilityLaw r k : Measure E))
      (finiteWeilCanonicalObservableLaw_integrable r k (finiteWeilCanonicalFluctuationPoint r k)
        (fun z : E => Real.exp (p.eval (z 0))))
    have hlogq := log_rnDeriv_tilted_left_self
      (μ := (finiteWeilCanonicalJointProbabilityLaw r k : Measure E))
      (finiteWeilCanonicalObservableLaw_integrable r k (finiteWeilCanonicalFluctuationPoint r k)
        (fun z : E => Real.exp ((finiteWeilCanonicalLogDensityPolynomial r k Q).eval (z 0))))
    rw [heq] at hlogp
    rw [hcanonical] at hlogq
    have hae : ∀ᵐ z ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E),
        p.eval (z 0) = (finiteWeilCanonicalLogDensityPolynomial r k Q).eval (z 0) := by
      filter_upwards [hlogp, hlogq] with z hp hq
      simpa only [hpartition, hcanonicalPartition, Real.log_one, sub_zero] using hp.symm.trans hq
    have hnodes := (finiteWeilCanonicalObservableLaw_ae_iff r k
      (finiteWeilCanonicalFluctuationPoint r k)
      (fun z : E => p.eval (z 0) =
        (finiteWeilCanonicalLogDensityPolynomial r k Q).eval (z 0))).mp hae
    refine ⟨hQ, ?_⟩
    apply (Lagrange.eq_interpolate_iff (s := Finset.univ) (f := p)
      (fun i => Real.log (Q i / finiteWeilCanonicalEdgeMass r k i))
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn).mp
    refine ⟨by simpa only [Finset.card_univ, Fintype.card_fin] using hdegree, ?_⟩
    intro i _
    exact (hnodes i).trans (finiteWeilCanonicalLogDensityPolynomial_eval_at_atom r k Q i)
  · rintro ⟨hQ, rfl⟩
    exact ⟨finiteWeilCanonicalLogDensityPolynomial_degree_lt r k Q,
      finiteWeilCanonicalLogDensityPolynomial_partition_eq_one_of_pos r k Q hQ,
      finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k Q hQ⟩

theorem finiteWeilCanonicalJointProbabilityLaw_existsUnique_normalized_polynomial_tilt_iff
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    (∃! p : Polynomial ℝ, p.degree < (r + 1 : ℕ) ∧
      (∫ z, Real.exp (p.eval (z 0))
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) = 1 ∧
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => p.eval (z 0)) =
        (Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E)) ↔
    ∀ i, 0 < Q i := by
  constructor
  · rintro ⟨p, hp, _⟩
    exact ((finiteWeilCanonicalJointProbabilityLaw_normalized_polynomial_tilt_iff r k Q p).mp hp).1
  · intro hQ
    refine ⟨finiteWeilCanonicalLogDensityPolynomial r k Q,
      (finiteWeilCanonicalJointProbabilityLaw_normalized_polynomial_tilt_iff r k Q _).mpr
        ⟨hQ, rfl⟩, ?_⟩
    intro p hp
    exact ((finiteWeilCanonicalJointProbabilityLaw_normalized_polynomial_tilt_iff r k Q p).mp hp).2

end RHTower
