import GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
import GaloisForLFunctions.HTGeometry.CompactClusterLimit
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Compact signed spectral limits

Uniform mass bounds give a common cluster point for two positive measure
families. Every convergent continuous integral difference survives there;
Jordan reduction then makes the two limiting measures mutually singular.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Uniform mass bounds retain all convergent integral differences at one
pair of finite measures. -/
theorem exists_finite_measure_pair_of_integral_difference_limit
    {A T : Type*} {l : Filter A} [l.NeBot]
    (μs νs : A → FiniteMeasure X) (C : ℝ≥0)
    (hμ : ∀ a, (μs a).mass ≤ C) (hν : ∀ a, (νs a).mass ≤ C)
    (f : T → C(X, ℂ)) (k : T → ℂ)
    (h : ∀ t, Tendsto (fun a =>
      (∫ x, f t x ∂(μs a : Measure X)) - ∫ x, f t x ∂(νs a : Measure X))
      l (𝓝 (k t))) :
    ∃ μ ν : FiniteMeasure X, μ.mass ≤ C ∧ ν.mass ≤ C ∧
      ∀ t, (∫ x, f t x ∂(μ : Measure X)) -
        ∫ x, f t x ∂(ν : Measure X) = k t := by
  let S : Set (FiniteMeasure X) := {μ | μ.mass ≤ C}
  have hS : IsCompact S := isCompact_setOf_finiteMeasure_le_of_compactSpace X C
  obtain ⟨p, hp, hc⟩ := exists_clusterPt_of_isCompact (hS.prod hS) (l := l)
    (P := fun a => (μs a, νs a)) (Eventually.of_forall fun a => ⟨hμ a, hν a⟩)
  refine ⟨p.1, p.2, hp.1, hp.2, fun t => ?_⟩
  have hF : Continuous (fun p : FiniteMeasure X × FiniteMeasure X =>
      (∫ x, f t x ∂(p.1 : Measure X)) - ∫ x, f t x ∂(p.2 : Measure X)) :=
    ((MeasureAlgebra.continuous_ofMeasure_apply (f t)).comp continuous_fst).sub
      ((MeasureAlgebra.continuous_ofMeasure_apply (f t)).comp continuous_snd)
  exact eq_of_clusterPt_of_tendsto hc hF (h t)

omit [T2Space X] in
/-- Jordan reduction preserves every continuous integral difference. -/
theorem exists_mutuallySingular_finite_measure_pair (μ ν : FiniteMeasure X) :
    ∃ P N : FiniteMeasure X, (P : Measure X) ⟂ₘ (N : Measure X) ∧
      ∀ f : C(X, ℂ), (∫ x, f x ∂(P : Measure X)) - ∫ x, f x ∂(N : Measure X) =
        (∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂(ν : Measure X) := by
  let η := (μ : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure
  let J := η.toJordanDecomposition
  let P : FiniteMeasure X := ⟨J.posPart, inferInstance⟩
  let N : FiniteMeasure X := ⟨J.negPart, inferInstance⟩
  refine ⟨P, N, J.mutuallySingular, fun f => ?_⟩
  have hdiff : (P : Measure X).toSignedMeasure - (N : Measure X).toSignedMeasure =
      (μ : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition η
  have hadd : (P : Measure X) + (ν : Measure X) = (μ : Measure X) + (N : Measure X) := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    simp only [Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp hdiff
  have hint (σ : FiniteMeasure X) : Integrable (fun x => f x) (σ : Measure X) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := congrArg (fun σ : Measure X => ∫ x, f x ∂σ) hadd
  rw [integral_add_measure (hint P) (hint ν),
    integral_add_measure (hint μ) (hint N)] at hi
  exact sub_eq_sub_iff_add_eq_add.mpr hi

end

end GaloisForLFunctions.HTGeometry
