/-
# The null-preimage law on Euclidean space

The coordinate identification between `Fin m -> R` and `EuclideanSpace R (Fin m)` is a linear
homeomorphism which preserves Lebesgue measure, so the null-preimage law for real-analytic
functions transfers to the Euclidean norm, where spheres are round.

Main results:
* `euclCoord` — the coordinate identification, as a linear homeomorphism.
* `analytic_preimage_volume_eq_zero_isOpen_euclidean` — **the law on Euclidean space**.
-/
import GaloisForLFunctions.HTGeometry.LocalAnalyticNullPreimage
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Transport of a null set along a measure-preserving bijection. -/
theorem measure_eq_zero_of_preimage_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ β) (he : MeasurePreserving e.symm ν μ)
    {A : Set β} (h : μ (e ⁻¹' A) = 0) : ν A = 0 := by
  obtain ⟨N, hsub, hmeas, hnull⟩ := exists_measurable_superset_of_null h
  have hAsub : A ⊆ (e.symm) ⁻¹' N := by
    intro y hy
    refine hsub ?_
    simp only [Set.mem_preimage, Equiv.apply_symm_apply]
    exact hy
  have hnullpre : ν ((e.symm) ⁻¹' N) = 0 := by
    rw [he.measure_preimage hmeas.nullMeasurableSet]
    exact hnull
  exact measure_mono_null hAsub hnullpre

/-- The coordinate identification of a finite real product with Euclidean space. -/
def euclCoord (m : ℕ) : (Fin m → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm

theorem measurePreserving_euclCoord (m : ℕ) :
    MeasurePreserving (euclCoord m) volume volume :=
  PiLp.volume_preserving_toLp (Fin m)

theorem measurePreserving_euclCoord_symm (m : ℕ) :
    MeasurePreserving (euclCoord m).symm volume volume :=
  PiLp.volume_preserving_ofLp (Fin m)

/-- **The null-preimage law on Euclidean space.** -/
theorem analytic_preimage_volume_eq_zero_isOpen_euclidean {m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    {Φ : EuclideanSpace ℝ (Fin m) → ℝ} (hΦ : AnalyticOnNhd ℝ Φ U)
    (hnc : ∀ V : Set (EuclideanSpace ℝ (Fin m)), IsOpen V → V.Nonempty → V ⊆ U →
      ∃ p ∈ V, ∃ q ∈ V, Φ p ≠ Φ q)
    (E : Set ℝ) (hE : volume E = 0) :
    volume (U ∩ Φ ⁻¹' E) = 0 := by
  have hUpre : IsOpen ((euclCoord m) ⁻¹' U) := hU.preimage (euclCoord m).continuous
  have hΦT : AnalyticOnNhd ℝ (fun x : Fin m → ℝ => Φ (euclCoord m x)) ((euclCoord m) ⁻¹' U) := by
    intro x hx
    exact AnalyticAt.comp (g := Φ) (f := fun x : Fin m → ℝ => euclCoord m x) (x := x)
      (hΦ _ hx) ((euclCoord m).analyticAt x)
  have hncT : ∀ V : Set (Fin m → ℝ), IsOpen V → V.Nonempty → V ⊆ (euclCoord m) ⁻¹' U →
      ∃ p ∈ V, ∃ q ∈ V, Φ (euclCoord m p) ≠ Φ (euclCoord m q) := by
    intro V hV hVne hVsub
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      hnc ((euclCoord m) '' V) ((euclCoord m).toHomeomorph.isOpenMap V hV) (hVne.image _)
        (Set.image_subset_iff.mpr hVsub)
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨p', hp', q', hq', hpq⟩
  have hup := analytic_preimage_volume_eq_zero_isOpen hUpre hΦT hncT E hE
  refine measure_eq_zero_of_preimage_eq_zero (euclCoord m).toEquiv
    (measurePreserving_euclCoord_symm m) ?_
  rw [Set.preimage_inter]
  exact hup

end

end GaloisForLFunctions.HTGeometry
