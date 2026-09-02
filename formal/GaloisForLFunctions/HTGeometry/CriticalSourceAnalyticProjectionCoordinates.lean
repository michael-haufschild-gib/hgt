import GaloisForLFunctions.HTGeometry.CriticalSourceBlockComplexPoints
import GaloisForLFunctions.HTGeometry.CriticalSourceReciprocalNumeratorCanonical
import GaloisForLFunctions.HTGeometry.MvPolynomialAwayComplexPoints

/-!
# Marked analytic coordinates of the critical source chart

The two torus coordinates of the actual source-to-observation map are evaluated explicitly on
principal-open points: they are the marked raw coordinate `x_m` and, when `x₀ = 1`, the cleared
reciprocal numerator `q_n`.  These formulas let explicit raw-coordinate loops be read directly in
the analytic torus chart.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

set_option maxHeartbeats 1000000

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]

/-- The source chart projected directly to analytic torus-affine observation coordinates. -/
def criticalSourceAnalyticProjection :
    AlgSpec (criticalSourceChartRing ℂ m n) →
      ComplexTorusAffineChart (n + m - 2) :=
  criticalObservationComplexPointHomeomorph m n ∘ criticalSourceChartProjection

/-- The direct source analytic projection is continuous. -/
theorem continuous_criticalSourceAnalyticProjection :
    Continuous (criticalSourceAnalyticProjection (m := m) (n := n)) :=
  (criticalObservationComplexPointHomeomorph m n).continuous.comp
    (AlgSpec.continuous_precomp _)

/-- The direct source analytic projection as a bundled continuous map. -/
def criticalSourceAnalyticProjectionContinuousMap :
    C(AlgSpec (criticalSourceChartRing ℂ m n),
      ComplexTorusAffineChart (n + m - 2)) :=
  ⟨criticalSourceAnalyticProjection, continuous_criticalSourceAnalyticProjection⟩

/-- On an evaluation point, the first analytic torus coordinate is `x_m`. -/
theorem criticalSourceAnalyticProjection_awayAlgPoint_first_val
    {v : Fin (m + n) → ℂ}
    (hv : MvPolynomial.eval v (criticalSourceChartPoly ℂ m n) ≠ 0) :
    ((criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv)).1 : ℂ) =
        v ⟨m, by
          have hm : 0 < m := Fact.out
          have hn : 0 < n := Fact.out
          omega⟩ := by
  rw [criticalSourceAnalyticProjection, Function.comp_apply,
    criticalObservationComplexPointHomeomorph_first_val]
  change AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv
      (algebraMap (criticalObservationChartRing ℂ m n)
        (criticalSourceChartRing ℂ m n)
        (algebraMap (criticalObservationRing ℂ m n)
          (criticalObservationChartRing ℂ m n)
          (X (Sum.inl (⟨0, Fact.out⟩ : Fin n))))) = _
  rw [show algebraMap (criticalObservationChartRing ℂ m n)
      (criticalSourceChartRing ℂ m n)
      (algebraMap (criticalObservationRing ℂ m n)
        (criticalObservationChartRing ℂ m n)
        (X (Sum.inl (⟨0, Fact.out⟩ : Fin n)))) =
      observationRingToChart ℂ (m := m) (n := n)
        (X (Sum.inl (⟨0, Fact.out⟩ : Fin n))) from
    IsLocalization.Away.lift_eq _ _ _]
  rw [observationRingToChart, MvPolynomial.aeval_X]
  change AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv
      (algebraMap (MvPolynomial (Fin (m + n)) ℂ)
        (criticalSourceChartRing ℂ m n) (X ⟨m, by
          have hn : 0 < n := Fact.out
          omega⟩)) = _
  rw [AlgSpec.awayAlgPoint_algebraMap, MvPolynomial.eval_X]

/-- At `x₀ = 1`, the second analytic torus coordinate is the cleared `n`-th reciprocal
numerator. -/
theorem criticalSourceAnalyticProjection_awayAlgPoint_second_val
    {v : Fin (m + n) → ℂ}
    (hv : MvPolynomial.eval v (criticalSourceChartPoly ℂ m n) ≠ 0)
    (hv0 : v ⟨0, by
      have hm : 0 < m := Fact.out
      have hn : 0 < n := Fact.out
      omega⟩ = 1) :
    ((criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv)).2.1 : ℂ) =
        MvPolynomial.eval v (criticalReciprocalNumerator ℂ (m + n) n) := by
  rw [criticalSourceAnalyticProjection, Function.comp_apply,
    criticalObservationComplexPointHomeomorph_second_val]
  change AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv
      (algebraMap (criticalObservationChartRing ℂ m n)
        (criticalSourceChartRing ℂ m n)
        (algebraMap (criticalObservationRing ℂ m n)
          (criticalObservationChartRing ℂ m n)
          (X (Sum.inr (⟨0, Fact.out⟩ : Fin m))))) = _
  rw [show algebraMap (criticalObservationChartRing ℂ m n)
      (criticalSourceChartRing ℂ m n)
      (algebraMap (criticalObservationRing ℂ m n)
        (criticalObservationChartRing ℂ m n)
        (X (Sum.inr (⟨0, Fact.out⟩ : Fin m)))) =
      observationRingToChart ℂ (m := m) (n := n)
        (X (Sum.inr (⟨0, Fact.out⟩ : Fin m))) from
    IsLocalization.Away.lift_eq _ _ _]
  rw [observationRingToChart, MvPolynomial.aeval_X]
  change AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv
      (chartRecip ℂ (m := m) (n := n) (k := n) (by
        have hm : 0 < m := Fact.out
        omega)) = _
  have hinv : AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv
      (chartInvX0 ℂ (m := m) (n := n)) = 1 := by
    have h := congrArg (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n) hv)
      (isUnit_algebraMap_chartX0 ℂ (m := m) (n := n)).val_inv_mul
    rw [map_mul, map_one, AlgSpec.awayAlgPoint_algebraMap,
      MvPolynomial.eval_X, hv0, mul_one] at h
    simpa [chartInvX0] using h
  rw [chartRecip, map_mul, map_pow,
    AlgSpec.awayAlgPoint_algebraMap, hinv, one_pow, mul_one]
  rw [criticalSourceRecipNumerator_eq_criticalReciprocalNumerator]

variable [Fact (1 < m)] [Fact (1 < n)]
variable {B : Set (criticalGeometricSheet ℂ m n)}

/-- The block-mediated source projection is the same direct source observation map. -/
theorem criticalSourceBlockAnalyticProjection_eq_source
    (hB : MulAction.IsBlock (criticalGeometricMonodromy ℂ m n) B)
    (hmem : criticalSourceNormalClosureEmbedding ℂ m n ∈ B) :
    criticalSourceBlockAnalyticProjection hB hmem =
      criticalSourceAnalyticProjection := by
  funext x
  change criticalObservationComplexPointHomeomorph m n
      (criticalBlockNormalizationProjection B
        (criticalSourceToBlockNormalization hB hmem x)) =
    criticalObservationComplexPointHomeomorph m n (criticalSourceChartProjection x)
  congr 1
  exact congrFun
    (criticalBlockNormalizationProjection_comp_sourceToBlock hB hmem) x

end

end GaloisForLFunctions.HTGeometry
