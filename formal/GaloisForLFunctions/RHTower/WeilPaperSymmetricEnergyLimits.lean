import GaloisForLFunctions.RHTower.WeilPaperNativeRealificationRetract
import GaloisForLFunctions.RHTower.WeilPaperExactEnergyLimits

/-!
# Exact energy loss inside the symmetric real-test native image

The full energy loss and divergence constructions survive canonical realification.
They occur inside the closed real-test retract of native laws. In particular,
intrinsic energy remains nowhere continuous after imposing both spectral symmetries.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A canonical point of the closed real-test retract. -/
def paperSymmetricNativePoint (c : ComplexNullMixture) : Set.range paperNativeRealification :=
  ⟨⟨spectralRepresentingMeasure (paperSymmetricNativeMixture c), Set.mem_range_self _⟩,
    ⟨⟨spectralRepresentingMeasure c, Set.mem_range_self c⟩, paperNativeRealification_apply c⟩⟩

@[simp] theorem paperNativeSpectralEnergy_symmetricPoint (c : ComplexNullMixture) :
    paperNativeSpectralEnergy (paperSymmetricNativePoint c).1 = energy c.1.1 := by
  simp only [paperSymmetricNativePoint, paperNativeSpectralEnergy_apply,
    energy_paperSymmetricNativeMixture]

/-- The canonical point construction preserves weak convergence of native laws. -/
theorem tendsto_paperSymmetricNativePoint
    {α : Type*} {l : Filter α} {c : α → ComplexNullMixture} {a : ComplexNullMixture}
    (h : Tendsto (fun i => spectralRepresentingMeasure (c i)) l
      (𝓝 (spectralRepresentingMeasure a))) :
    Tendsto (fun i => paperSymmetricNativePoint (c i)) l (𝓝 (paperSymmetricNativePoint a)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_subtype_rng.mpr
  exact tendsto_spectralRepresentingMeasure_paperSymmetricNativeMixture h

/-- Every point of the real-test retract has a canonical native representative. -/
theorem exists_eq_paperSymmetricNativePoint (μ : Set.range paperNativeRealification) :
    ∃ c : ComplexNullMixture, μ = paperSymmetricNativePoint c := by
  rcases μ with ⟨μ, ν, rfl⟩
  rcases ν with ⟨ν, c, rfl⟩
  exact ⟨c, Subtype.ext (paperNativeRealification_apply c)⟩

/-- Exact energy loss can be realized using only real tests and both reflection symmetries. -/
theorem exists_real_test_spectralRepresentingMeasure_tendsto_exact_energy
    (a : ComplexNullMixture) (δ : ℝ≥0) :
    ∃ c : ℕ → ComplexNullMixture,
      Tendsto (fun n => spectralRepresentingMeasure (c n)) atTop
        (𝓝 (spectralRepresentingMeasure (paperSymmetricNativeMixture a))) ∧
      (∀ n, energy (c n).1.1 = energy a.1.1 + δ) ∧
      (∀ n f, (c n).1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      (∀ n, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c n).1 : Measure ℝ) =
        (spectralProbability (c n).1 : Measure ℝ)) ∧
      (∀ n, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c n)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c n)).1 : Measure PrimePhaseSpace)) := by
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_exact_energy a δ
  exact ⟨fun n => paperSymmetricNativeMixture (c n),
    tendsto_spectralRepresentingMeasure_paperSymmetricNativeMixture hc,
    fun n => (energy_paperSymmetricNativeMixture (c n)).trans (he n),
    fun n => paperSymmetricNativeMixture_real (c n),
    fun n => map_neg_spectralProbability_paperSymmetricNativeMixture (c n),
    fun n => map_neg_spectralRepresentingMeasure_paperSymmetricNativeMixture (c n)⟩

/-- Energy divergence also persists with real tests and both spectral symmetries. -/
theorem exists_real_test_spectralRepresentingMeasure_tendsto_energy_atTop
    (a : ComplexNullMixture) :
    ∃ c : ℕ → ComplexNullMixture,
      Tendsto (fun n => spectralRepresentingMeasure (c n)) atTop
        (𝓝 (spectralRepresentingMeasure (paperSymmetricNativeMixture a))) ∧
      Tendsto (fun n => energy (c n).1.1) atTop atTop ∧
      (∀ n f, (c n).1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      (∀ n, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c n).1 : Measure ℝ) =
        (spectralProbability (c n).1 : Measure ℝ)) ∧
      (∀ n, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c n)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c n)).1 : Measure PrimePhaseSpace)) := by
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_energy_atTop a
  refine ⟨fun n => paperSymmetricNativeMixture (c n),
    tendsto_spectralRepresentingMeasure_paperSymmetricNativeMixture hc, ?_,
    fun n => paperSymmetricNativeMixture_real (c n),
    fun n => map_neg_spectralProbability_paperSymmetricNativeMixture (c n),
    fun n => map_neg_spectralRepresentingMeasure_paperSymmetricNativeMixture (c n)⟩
  simpa only [energy_paperSymmetricNativeMixture] using he

/-- At every point of the closed real-test image, any prescribed nonnegative energy
increment disappears along a sequence staying entirely inside that image. -/
theorem exists_symmetricNativePoint_tendsto_exact_energy
    (μ : Set.range paperNativeRealification) (δ : ℝ≥0) :
    ∃ ν : ℕ → Set.range paperNativeRealification, Tendsto ν atTop (𝓝 μ) ∧
      ∀ n, paperNativeSpectralEnergy (ν n).1 = paperNativeSpectralEnergy μ.1 + δ := by
  obtain ⟨a, rfl⟩ := exists_eq_paperSymmetricNativePoint μ
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_exact_energy a δ
  refine ⟨fun n => paperSymmetricNativePoint (c n), tendsto_paperSymmetricNativePoint hc, ?_⟩
  intro n
  simpa only [paperNativeSpectralEnergy_symmetricPoint] using he n

/-- Energy is locally unbounded above even within the closed real-test image. -/
theorem exists_symmetricNativePoint_tendsto_energy_atTop
    (μ : Set.range paperNativeRealification) :
    ∃ ν : ℕ → Set.range paperNativeRealification, Tendsto ν atTop (𝓝 μ) ∧
      Tendsto (fun n => paperNativeSpectralEnergy (ν n).1) atTop atTop := by
  obtain ⟨a, rfl⟩ := exists_eq_paperSymmetricNativePoint μ
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_energy_atTop a
  refine ⟨fun n => paperSymmetricNativePoint (c n), tendsto_paperSymmetricNativePoint hc, ?_⟩
  simpa only [paperNativeSpectralEnergy_symmetricPoint] using he

/-- Restricting to real tests and spectral symmetry does not create a continuity point. -/
theorem not_continuousAt_native_full_energy_realification
    (μ : Set.range paperNativeRealification) :
    ¬ ContinuousAt (fun ν : Set.range paperNativeRealification =>
      paperNativeSpectralEnergy ν.1) μ := by
  intro h
  obtain ⟨ν, hν, he⟩ := exists_symmetricNativePoint_tendsto_energy_atTop μ
  exact not_tendsto_nhds_of_tendsto_atTop he _ (h.tendsto.comp hν)

/-- The symmetric real-test energy graph still has every upward vertical ray in its closure. -/
theorem symmetric_native_energy_vertical_ray_mem_closure
    (μ : Set.range paperNativeRealification) (δ : ℝ≥0) :
    (μ, paperNativeSpectralEnergy μ.1 + δ) ∈
      closure {p : Set.range paperNativeRealification × ℝ |
        paperNativeSpectralEnergy p.1.1 = p.2} := by
  obtain ⟨ν, hν, he⟩ := exists_symmetricNativePoint_tendsto_exact_energy μ δ
  apply mem_closure_of_tendsto (hν.prodMk_nhds
    (tendsto_const_nhds (x := paperNativeSpectralEnergy μ.1 + (δ : ℝ))))
  exact Filter.Eventually.of_forall he

/-- The intrinsic energy graph remains nonclosed on the real-test retract itself. -/
theorem not_isClosed_symmetric_native_energy_graph :
    ¬ IsClosed {p : Set.range paperNativeRealification × ℝ |
      paperNativeSpectralEnergy p.1.1 = p.2} := by
  intro h
  obtain ⟨a, _⟩ := exists_complexNullMixture_energy_gt 0
  have hm := symmetric_native_energy_vertical_ray_mem_closure (paperSymmetricNativePoint a) 1
  rw [h.closure_eq] at hm
  change paperNativeSpectralEnergy _ = paperNativeSpectralEnergy _ + (1 : ℝ) at hm
  linarith

end RHTower.WeilWorkPBAP
