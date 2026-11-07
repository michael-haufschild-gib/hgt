/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license; see LICENSE and NOTICE in the parent directory.
Adapted from rellich-kondrachov, Euclidean/L2Compactness/TranslationIntegral.lean.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.ConvolutionApproximation

/-!
# A local translation bound controls its kernel average

A probability kernel supported inside a ball averages only translations in
that ball. A uniform error bound therefore bounds the mean squared error.
-/

namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessTranslationIntegral : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessTranslationIntegral : MeasurableNeg E := by
  infer_instance

variable {ψ : E → ℝ}

private lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {δ : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) δ)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) δ)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) δ)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) δ)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) δ)ᶜ) hmeas hEq]

/-- A local translation modulus bounds its mean squared error under a supported probability kernel. -/
theorem translation_average_le_of_local_bound
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {δ η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) δ →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
    simpa [μ] using kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) δ) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    simpa [Real.norm_eq_abs, hμreal, mul_one] using this
  simpa [abs_of_nonneg hnonneg_int, μ] using habs

end Volume

end
#print axioms translation_average_le_of_local_bound

end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness
