import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltNormalization
import GaloisForLFunctions.HTGeometry.FiniteLawPositiveApproximation
import GaloisForLFunctions.HTGeometry.AtomicProbabilityMixture

/-! # Every finite support law is a total-variation limit of normalized polynomial tilts -/

namespace RHTower

open Filter MeasureTheory GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped Topology

local notation "E" => EuclideanSpace ℝ (Fin 2)

noncomputable def finiteWeilCanonicalApproximationPolynomial
    (r k : ℕ) (Q : Law (Fin (r + 1))) (n : ℕ) : Polynomial ℝ :=
  finiteWeilCanonicalLogDensityPolynomial r k (Q.uniformApproximation n)

theorem finiteWeilCanonicalApproximationPolynomial_degree_lt
    (r k : ℕ) (Q : Law (Fin (r + 1))) (n : ℕ) :
    (finiteWeilCanonicalApproximationPolynomial r k Q n).degree < (r + 1 : ℕ) :=
  finiteWeilCanonicalLogDensityPolynomial_degree_lt r k (Q.uniformApproximation n)

theorem finiteWeilCanonicalApproximationPolynomial_partition_eq_one
    (r k : ℕ) (Q : Law (Fin (r + 1))) (n : ℕ) :
    (∫ z, Real.exp ((finiteWeilCanonicalApproximationPolynomial r k Q n).eval (z 0))
      ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) = 1 :=
  finiteWeilCanonicalLogDensityPolynomial_partition_eq_one_of_pos r k
    (Q.uniformApproximation n) (Q.uniformApproximation_pos n)

theorem finiteWeilCanonicalApproximationPolynomial_tilt_eq_atomic
    (r k : ℕ) (Q : Law (Fin (r + 1))) (n : ℕ) :
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval (z 0)) =
      ((Q.uniformApproximation n).atomicProbability
        (finiteWeilCanonicalFluctuationPoint r k) : Measure E) :=
  finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k
    (Q.uniformApproximation n) (Q.uniformApproximation_pos n)

theorem finiteWeilCanonicalApproximationPolynomial_event_error_le
    (r k : ℕ) (Q : Law (Fin (r + 1))) (n : ℕ) (s : Set E) :
    |(((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval (z 0))) s).toReal -
      ((Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) s).toReal| ≤
        1 / ((n : ℝ) + 1) := by
  rw [finiteWeilCanonicalApproximationPolynomial_tilt_eq_atomic]
  exact Law.atomicProbability_mixture_event_le (Law.uniform (Fin (r + 1))) Q
    (finiteWeilCanonicalFluctuationPoint r k) _ _ _ s

theorem finiteWeilCanonicalApproximationPolynomial_event_sup_le
    (r k : ℕ) (Q : Law (Fin (r + 1))) (n : ℕ) :
    (⨆ s : Set E,
      |(((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval (z 0))) s).toReal -
        ((Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) s).toReal|) ≤
          1 / ((n : ℝ) + 1) :=
  ciSup_le (fun s => finiteWeilCanonicalApproximationPolynomial_event_error_le r k Q n s)

theorem tendsto_finiteWeilCanonicalApproximationPolynomial_event_sup
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    Tendsto (fun n : ℕ => ⨆ s : Set E,
      |(((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval (z 0))) s).toReal -
        ((Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) s).toReal|)
      atTop (𝓝 0) := by
  apply squeeze_zero ?_
    (fun n => finiteWeilCanonicalApproximationPolynomial_event_sup_le r k Q n)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  intro n
  have hb : BddAbove (Set.range (fun s : Set E =>
      |(((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => (finiteWeilCanonicalApproximationPolynomial r k Q n).eval (z 0))) s).toReal -
        ((Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) s).toReal|)) := by
    refine ⟨1 / ((n : ℝ) + 1), ?_⟩
    rintro _ ⟨s, rfl⟩
    exact finiteWeilCanonicalApproximationPolynomial_event_error_le r k Q n s
  exact le_ciSup_of_le hb (∅ : Set E) (abs_nonneg _)

/-- Boundary laws are limits of normalized potentials of the same bounded degree. -/
theorem finiteWeilCanonicalJointProbabilityLaw_exists_polynomial_tilt_tv_approximation
    (r k : ℕ) (Q : Law (Fin (r + 1))) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ n, (p n).degree < (r + 1 : ℕ)) ∧
      (∀ n, (∫ z, Real.exp ((p n).eval (z 0))
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) = 1) ∧
      Tendsto (fun n : ℕ => ⨆ s : Set E,
        |(((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
            (fun z => (p n).eval (z 0))) s).toReal -
          ((Q.atomicProbability (finiteWeilCanonicalFluctuationPoint r k) : Measure E) s).toReal|)
        atTop (𝓝 0) :=
  ⟨finiteWeilCanonicalApproximationPolynomial r k Q,
    finiteWeilCanonicalApproximationPolynomial_degree_lt r k Q,
    finiteWeilCanonicalApproximationPolynomial_partition_eq_one r k Q,
    tendsto_finiteWeilCanonicalApproximationPolynomial_event_sup r k Q⟩

end RHTower
