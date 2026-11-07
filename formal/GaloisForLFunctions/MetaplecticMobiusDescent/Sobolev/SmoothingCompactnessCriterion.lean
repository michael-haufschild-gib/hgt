/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license; see LICENSE and NOTICE in the parent directory.
Adapted from rellich-kondrachov, Euclidean/L2Compactness/FrechetKolmogorov.lean.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.ConvolutionApproximation
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.CompactConvolution
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Compactness from uniform smoothing approximation

Compact smoothing images have finite nets. A common translation-error bound
transfers those nets to the original bounded family at every scale.
-/

namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessFrechetKolmogorov :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessFrechetKolmogorov : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessFrechetKolmogorov : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

lemma smoothing_error_le_of_translation_average_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by
  have hsq :
      ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤ η ^ 2 := by
    refine (le_trans ?_ htrans)
    simpa using
      smoothing_error_sq_le_translation_average
        (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs hψ0 hψint u
  exact (sq_le_sq₀ (norm_nonneg _) hη).1 hsq

/-- Uniform smoothing approximation transfers finite nets to the original bounded family. -/
theorem totallyBounded_of_small_translation_average
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ}
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by
  classical
  refine (Metric.totallyBounded_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases hApprox ε hε with ⟨ψ, hψc, hψcs, hψ0, hψint, htrans⟩
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
  have hB_compact : IsCompact (closure B) :=
    smoothL2_image_closedBall_isCompact K hK ψ hψc hψcs R
  have hB_tot : TotallyBounded B :=
    (totallyBounded_closure).1 hB_compact.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hB_tot (ε / 2) hε2 with ⟨t, htB, htfin, hBcover⟩
  refine ⟨t, htfin, ?_⟩
  intro x hx
  rcases hx with ⟨u, huA, rfl⟩
  have huR : u ∈ Metric.closedBall (0 : _) R := hA huA
  have hSu_mem : smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈ B := ⟨u, huR, rfl⟩
  have hSu_cover :
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈
        ⋃ y, ⋃ (_ : y ∈ t), Metric.ball y (ε / 2) :=
    hBcover hSu_mem
  rcases Set.mem_iUnion.1 hSu_cover with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyT, hyBall⟩
  have hyDist : dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y < ε / 2 := by
    simpa [Metric.ball, Set.mem_setOf_eq] using hyBall
  have hdist_smooth_ext :
      dist (extendByZeroL2 (E := E) (K := K) hKm u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) ≤ ε / 2 := by
    have hη : 0 ≤ ε / 2 := le_of_lt hε2
    have hnorm :
        ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ ε / 2 :=
      smoothing_error_le_of_translation_average_le
        (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs hψ0 hψint (η := ε / 2) hη u (htrans u huA)
    have hdist :
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (extendByZeroL2 (E := E) (K := K) hKm u) ≤ ε / 2 := by
      simpa [dist_eq_norm] using hnorm
    simpa [dist_comm] using hdist
  have hxDist : dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε := by
    have htri :=
      dist_triangle (extendByZeroL2 (E := E) (K := K) hKm u)
        (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
    have hlt :
        dist (extendByZeroL2 (E := E) (K := K) hKm u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            + dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
          < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hdist_smooth_ext hyDist
    have htmp :
        dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri hlt
    simpa [add_halves ε] using htmp
  have hxBall : extendByZeroL2 (E := E) (K := K) hKm u ∈ Metric.ball y ε := by
    simpa [Metric.ball, Set.mem_setOf_eq] using hxDist
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyT, hxBall⟩⟩

/-- Completeness turns the finite-net conclusion into compact closure. -/
theorem compact_closure_of_small_translation_average
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ}
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    IsCompact (closure (extendByZeroL2 (E := E) (K := K) hKm '' A)) := by
  have ht :
      TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) :=
    totallyBounded_of_small_translation_average
      (E := E) (K := K) hK hKm hA hApprox
  exact (ht.closure).isCompact_of_isClosed isClosed_closure

end Volume

end
#print axioms compact_closure_of_small_translation_average

end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness
