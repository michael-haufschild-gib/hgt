import GaloisForLFunctions.RHTower.CompletedSeamCompactThorinMarkovEquivalence
import GaloisForLFunctions.RHTower.PrimeArchEuclideanSpectralRH
import GaloisForLFunctions.RHTower.PrimeArchEndpointCalibratedHausdorffRH
import GaloisForLFunctions.RHTower.PrimeArchHausdorffBernsteinKMSRH
import GaloisForLFunctions.RHTower.XiHedenmalmMomentDeterminacy

/-!
# The canonical compact Xi measure realizes the Markov and Thorin source germs

The positive Xi thermal nodes already used by the Euclidean spectral construction lie in `(0, 1)`.
Putting mass `lambda_j` at `lambda_j` therefore gives a finite measure on `[0, 1]`.  Under RH its
`n`-th moment is the normalized completed prime--Gamma moment.  Analytic jet determinacy then
identifies its Markov transform with the completed source moment germ.

Consequently, the compact Markov-germ and compact Thorin-exponent interfaces are each exactly
equivalent to RH.  This supplies their previously missing producer from source-defined data.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Canonical compact moment measure: mass `lambda_j` at the Xi thermal node `lambda_j`. -/
def primeArchXiCompactMomentMeasure : Measure ℝ :=
  Measure.sum fun j : ℕ =>
    ENNReal.ofReal (xiThermalNode (xiThermalEnumeration j)) •
      Measure.dirac (xiThermalNode (xiThermalEnumeration j))

/-- Every power is integrable against the canonical compact Xi measure. -/
theorem integrable_primeArchXiCompactMomentMeasure (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) primeArchXiCompactMomentMeasure := by
  rw [primeArchXiCompactMomentMeasure]
  apply integrable_sum_dirac (fun j => by simp [ENNReal.ofReal_ne_top])
  convert (hasSum_xiThermalEnumeration_positiveMoment n).summable using 1
  funext j
  rw [ENNReal.toReal_ofReal (xiThermalNode_pos _).le]
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos (xiThermalNode_pos _)]
  ring

/-- The canonical compact Xi measure is finite. -/
theorem primeArchXiCompactMomentMeasure_finite :
    IsFiniteMeasure primeArchXiCompactMomentMeasure := by
  apply (integrable_const_iff_isFiniteMeasure
    (μ := primeArchXiCompactMomentMeasure) (c := (1 : ℝ)) one_ne_zero).mp
  simpa only [pow_zero] using integrable_primeArchXiCompactMomentMeasure 0

/-- The canonical compact Xi measure is carried by `[0, 1]`. -/
theorem ae_primeArchXiCompactMomentMeasure_mem_zero_one :
    ∀ᵐ x : ℝ ∂primeArchXiCompactMomentMeasure, 0 ≤ x ∧ |x| ≤ 1 := by
  rw [primeArchXiCompactMomentMeasure, Measure.ae_sum_iff]
  intro j
  apply Measure.ae_smul_measure
  rw [ae_dirac_iff (by
    exact measurableSet_Ici.inter
      (measurableSet_le measurable_id.abs measurable_const) :
      MeasurableSet {x : ℝ | 0 ≤ x ∧ |x| ≤ 1})]
  exact ⟨(xiThermalNode_pos _).le,
    by
      rw [abs_of_pos (xiThermalNode_pos _)]
      exact (xiThermalNode_lt_one _).le⟩

/-- The source endpoint height bound places the canonical Xi measure in the much smaller interval
`[0, 2/41]`.  This is the support aperture needed to transport its Markov transform between the
completed seam center and the Cassini theta boundary. -/
theorem ae_primeArchXiCompactMomentMeasure_mem_zero_two_over_fortyOne :
    ∀ᵐ x : ℝ ∂primeArchXiCompactMomentMeasure,
      0 ≤ x ∧ |x| ≤ 2 / 41 := by
  rw [primeArchXiCompactMomentMeasure, Measure.ae_sum_iff]
  intro j
  apply Measure.ae_smul_measure
  rw [ae_dirac_iff (by
    exact measurableSet_Ici.inter
      (measurableSet_le measurable_id.abs measurable_const) :
      MeasurableSet {x : ℝ | 0 ≤ x ∧ |x| ≤ 2 / 41})]
  have hpos := xiThermalNode_pos (xiThermalEnumeration j)
  refine ⟨hpos.le, ?_⟩
  rw [abs_of_pos hpos]
  exact (xiThermalNode_le_primeArchEndpointHausdorffRadius _).trans
    primeArchEndpointHausdorffRadius_lt_two_over_fortyOne.le

/-- Under RH, all moments of the canonical compact Xi measure are the normalized source moments. -/
theorem integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂primeArchXiCompactMomentMeasure =
      normalizedPrimeArchMoment n := by
  rw [primeArchXiCompactMomentMeasure,
    integral_sum_dirac (fun j => by simp [ENNReal.ofReal_ne_top])]
  calc
    (∑' j : ℕ,
        (ENNReal.ofReal (xiThermalNode (xiThermalEnumeration j))).toReal •
          xiThermalNode (xiThermalEnumeration j) ^ n) =
        ∑' j : ℕ, xiThermalNode (xiThermalEnumeration j) ^ (n + 1) := by
      apply tsum_congr
      intro j
      rw [ENNReal.toReal_ofReal (xiThermalNode_pos _).le]
      simp only [smul_eq_mul]
      ring
    _ = normalizedPrimeArchMoment n :=
      (hasSum_xiThermalEnumeration_pow_of_rh hRH n).tsum_eq

/-- Under RH, the canonical compact Xi Markov transform has the complete source Taylor jet. -/
theorem iteratedDeriv_primeArchXiCompactMarkovTransform_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    iteratedDeriv n
        (compactMarkovTransform primeArchXiCompactMomentMeasure) 0 =
      iteratedDeriv n completedSeamMomentGerm 0 := by
  letI : IsFiniteMeasure primeArchXiCompactMomentMeasure :=
    primeArchXiCompactMomentMeasure_finite
  have hbound : ∀ᵐ x : ℝ ∂primeArchXiCompactMomentMeasure, |x| ≤ 1 :=
    ae_primeArchXiCompactMomentMeasure_mem_zero_one.mono fun _ hx => hx.2
  have hintc :
      (∫ x : ℝ, (x : ℂ) ^ n ∂primeArchXiCompactMomentMeasure) =
        ((∫ x : ℝ, x ^ n ∂primeArchXiCompactMomentMeasure : ℝ) : ℂ) := by
    simpa using (integral_ofReal (X := ℝ)
      (μ := primeArchXiCompactMomentMeasure) (𝕜 := ℂ)
      (f := fun x : ℝ => x ^ n))
  rw [iteratedDeriv_compactMarkovTransform
      primeArchXiCompactMomentMeasure zero_lt_one hbound n
      (by norm_num : ‖(0 : ℂ)‖ < 1 / (2 * (1 : ℝ))),
    compactMarkovKernelMoment_zero_node,
    hintc,
    integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH n,
    iteratedDeriv_completedSeamMomentGerm]

/-- RH identifies the completed source moment germ with the canonical compact Xi Markov transform. -/
theorem completedSeamMomentGerm_eventuallyEq_primeArchXiCompactMarkovTransform_of_rh
    (hRH : RiemannHypothesis) :
    completedSeamMomentGerm =ᶠ[𝓝 0]
      compactMarkovTransform primeArchXiCompactMomentMeasure := by
  letI : IsFiniteMeasure primeArchXiCompactMomentMeasure :=
    primeArchXiCompactMomentMeasure_finite
  have hbound : ∀ᵐ x : ℝ ∂primeArchXiCompactMomentMeasure, |x| ≤ 1 :=
    ae_primeArchXiCompactMomentMeasure_mem_zero_one.mono fun _ hx => hx.2
  apply analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
    analyticAt_completedSeamMomentGerm
    (analyticAt_compactMarkovTransform
      primeArchXiCompactMomentMeasure zero_lt_one hbound)
  intro n
  exact (iteratedDeriv_primeArchXiCompactMarkovTransform_eq_of_riemannHypothesis
    hRH n).symm

/-- RH supplies the compact Markov-germ source interface using the canonical Xi measure. -/
theorem primeArchCompactMarkovGermRepresentation_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchCompactMarkovGermRepresentation :=
  ⟨primeArchXiCompactMomentMeasure, 1,
    primeArchXiCompactMomentMeasure_finite, zero_lt_one,
    ae_primeArchXiCompactMomentMeasure_mem_zero_one,
    completedSeamMomentGerm_eventuallyEq_primeArchXiCompactMarkovTransform_of_rh hRH⟩

/-- Compact Markov-germ realization of the completed source is exactly RH. -/
theorem primeArchCompactMarkovGermRepresentation_iff_riemannHypothesis :
    PrimeArchCompactMarkovGermRepresentation ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_primeArchCompactMarkovGermRepresentation,
    primeArchCompactMarkovGermRepresentation_of_riemannHypothesis⟩

/-- Compact Thorin-exponent realization of the completed source is exactly RH. -/
theorem primeArchCompactThorinExponentRepresentation_iff_riemannHypothesis :
    PrimeArchCompactThorinExponentRepresentation ↔ RiemannHypothesis := by
  rw [primeArchCompactThorinExponentRepresentation_iff_compactMarkovGerm,
    primeArchCompactMarkovGermRepresentation_iff_riemannHypothesis]

end

end RHTower
