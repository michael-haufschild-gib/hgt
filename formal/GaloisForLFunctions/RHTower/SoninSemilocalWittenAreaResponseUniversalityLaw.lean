import GaloisForLFunctions.RHTower.SoninProlateCommutatorEnergy
import GaloisForLFunctions.RHTower.SoninSemilocalTraceObstruction

/-!
# Sonin semilocal Witten-area response universality

The central prolate free-fermion variance, the zero-mode-subtracted supersymmetric partition, and
the semilocal prime-power response bound are three faces of one aperture-area budget.  The local
variance lies in the exact occupation simplex, the full Witten partition is `8 a²`, and the same
partition uniformly controls every arithmetic response.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- The local free-fermion number variance of the central Sonin prolate compression. -/
def centralSoninFreeFermionVariance (a : ℝ) : ℝ :=
  Complex.re
    (opTrace
      (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a) -
        soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a) *
          soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)))

/-- The full zero-mode-subtracted Witten energy of the central Sonin correction. -/
def centralSoninWittenAreaBudget (a : ℝ) : ℝ :=
  hsNormSq
      (soninAlternatingBlock (centralPhysicalForbidden a)
        (centralFourierForbidden a)) +
    hsNormSq (centralSoninExteriorCompression a) +
      2 * centralSoninFreeFermionVariance a

/-- The free-fermion variance is exactly the transition-corner Hilbert--Schmidt energy. -/
theorem centralSoninFreeFermionVariance_eq_transition_hsNormSq
    (a : ℝ) (ha : 0 < a) :
    centralSoninFreeFermionVariance a =
      hsNormSq
        (crossBoundary (centralFourierForbidden a).starProjection
          (centralPhysicalForbidden a).starProjection) := by
  exact re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a ha

/-- The aperture area confines local number variance to the exact interval `[0, 4a²]`. -/
theorem centralSoninFreeFermionVariance_mem_areaInterval
    (a : ℝ) (ha : 0 < a) :
    0 ≤ centralSoninFreeFermionVariance a ∧
      centralSoninFreeFermionVariance a ≤ 4 * a ^ 2 := by
  have hvariance :=
    centralSoninFreeFermionVariance_eq_transition_hsNormSq a ha
  have hbudget :=
    hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq a ha
  have hprolate : 0 ≤
      hsNormSq
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) :=
    hsNormSq_nonneg _
  constructor
  · rw [hvariance]
    exact hsNormSq_nonneg _
  · change
      Complex.re
          (opTrace
            (soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a) -
              soninAlternatingBlock (centralPhysicalForbidden a)
                    (centralFourierForbidden a) *
                soninAlternatingBlock (centralPhysicalForbidden a)
                  (centralFourierForbidden a))) ≤
        4 * a ^ 2
    linarith

/-- The complete Witten partition is exactly the Shannon time--frequency aperture area `8a²`. -/
theorem centralSoninWittenAreaBudget_eq_eight_mul_sq
    (a : ℝ) (ha : 0 < a) :
    centralSoninWittenAreaBudget a = 8 * a ^ 2 := by
  calc
    centralSoninWittenAreaBudget a =
        hsNormSq (centralSoninProjectionCorrection a) := by
      exact
        (hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_re_opTrace_prolateImpurity
          a ha).symm
    _ = 8 * a ^ 2 :=
      hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq a ha

/-- Every prime-power semilocal response is controlled by the same exact Witten-area partition. -/
theorem norm_soninSemilocalGeometricTraceResponse_le_wittenAreaBudget
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ‖soninSemilocalGeometricTraceResponse a pk‖ ≤
      Real.sqrt (centralSoninWittenAreaBudget a) *
        Real.sqrt (1024 * centralSoninWittenAreaBudget a) := by
  have h :=
    norm_soninSemilocalGeometricTraceResponse_le_compressions_add_two_mul_transition
      a ha pk
  rw [← centralSoninFreeFermionVariance_eq_transition_hsNormSq a ha] at h
  exact h

/-- **Sonin semilocal Witten-area response universality.**  Local free-fermion fluctuation,
retained prolate occupation, the full supersymmetric partition, and every arithmetic response
share one exact aperture-area budget. -/
theorem soninSemilocal_wittenArea_responseUniversality
    (a : ℝ) (ha : 0 < a) :
    (0 ≤ centralSoninFreeFermionVariance a ∧
        centralSoninFreeFermionVariance a ≤ 4 * a ^ 2) ∧
      (hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
          centralSoninFreeFermionVariance a = 4 * a ^ 2) ∧
      centralSoninWittenAreaBudget a = 8 * a ^ 2 ∧
      ∀ pk : Nat.Primes × ℕ,
        ‖soninSemilocalGeometricTraceResponse a pk‖ ≤
          Real.sqrt (centralSoninWittenAreaBudget a) *
            Real.sqrt (1024 * centralSoninWittenAreaBudget a) := by
  refine ⟨centralSoninFreeFermionVariance_mem_areaInterval a ha, ?_, ?_,
    norm_soninSemilocalGeometricTraceResponse_le_wittenAreaBudget a ha⟩
  · exact hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq a ha
  · exact centralSoninWittenAreaBudget_eq_eight_mul_sq a ha

end

end RHTower
