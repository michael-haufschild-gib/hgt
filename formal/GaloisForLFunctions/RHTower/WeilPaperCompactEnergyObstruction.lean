import GaloisForLFunctions.RHTower.WeilPaperUnboundedSpectralEnergy
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compact representing laws do not admit a continuous full-energy extension

The origin moment constraints cut out a closed, hence compact, space of prime-torus
probabilities. Native full energy is unbounded even for normalized real-test,
symmetric spectral laws. Every continuous predictor on this compact space
therefore underestimates some such energies by arbitrarily large amounts.
-/

open Complex MeasureTheory Filter Set Topology
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Complex arithmetic moments vary continuously in the native weak topology. -/
theorem continuous_arithmeticPhase_integral (n : ℕ) :
    Continuous (fun μ : ProbabilityMeasure PrimePhaseSpace =>
      ∫ z, arithmeticPhase n z ∂(μ : Measure PrimePhaseSpace)) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  have ht : Tendsto (id : ProbabilityMeasure PrimePhaseSpace → ProbabilityMeasure PrimePhaseSpace)
      (𝓝 μ) (𝓝 μ) := tendsto_id
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp ht
    (BoundedContinuousFunction.mkOfCompact (arithmeticPhase n))

/-- All integer origin constraints define a closed subset of actual probabilities. -/
theorem isClosed_representingPhaseMeasures :
    IsClosed {μ : ProbabilityMeasure PrimePhaseSpace |
      ∀ n : ℕ, 2 ≤ n → ∫ z, arithmeticPhase n z ∂(μ : Measure PrimePhaseSpace) = 0} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_eq (continuous_arithmeticPhase_integral n) continuous_const

/-- The full space of origin-representing probabilities is compact. -/
instance instCompactSpaceRepresentingPhaseMeasure : CompactSpace RepresentingPhaseMeasure :=
  isCompact_iff_compactSpace.mp isClosed_representingPhaseMeasures.isCompact

/-- Continuous predictors on the full compact law space have unbounded underestimation
error on real-test, symmetric, normalized complex-null spectral laws. -/
theorem exists_symmetric_real_energy_above_continuous_predictor
    (F : C(RepresentingPhaseMeasure, ℝ)) (B : ℝ) :
    ∃ c : ComplexNullMixture, B < energy c.1.1 - F (spectralRepresentingMeasure c) ∧
      (∀ f, c.1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      Measure.map (fun ξ : ℝ => -ξ) (spectralProbability c.1 : Measure ℝ) =
        (spectralProbability c.1 : Measure ℝ) ∧
      Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace) := by
  obtain ⟨A, hA⟩ := (isCompact_range F.continuous).bddAbove
  obtain ⟨c, hc, hr, hs, ht⟩ := exists_symmetric_real_complexNullMixture_energy_gt (B+A)
  have hFc := hA (Set.mem_range_self (spectralRepresentingMeasure c))
  exact ⟨c, by linarith, hr, hs, ht⟩

/-- Native full energy has no continuous extension to all origin-representing laws. -/
theorem no_continuous_full_energy_extension :
    ¬ ∃ F : C(RepresentingPhaseMeasure, ℝ),
      ∀ c : ComplexNullMixture, F (spectralRepresentingMeasure c) = energy c.1.1 := by
  rintro ⟨F, hF⟩
  obtain ⟨c, hc, _, _, _⟩ := exists_symmetric_real_energy_above_continuous_predictor F 0
  rw [hF, sub_self] at hc
  exact (lt_irrefl 0) hc

end RHTower.WeilWorkPBAP
