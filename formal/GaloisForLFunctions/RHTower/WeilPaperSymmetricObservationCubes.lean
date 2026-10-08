import GaloisForLFunctions.RHTower.WeilPaperRepresentingObservationCubes

/-!
# Arbitrary-dimensional symmetric families invisible to finite observations

The faithful real kernel directions of the positive cube survive real/imaginary
splitting. Every finite observer therefore remains constant on affine cubes of
normalized complex-null mixtures of real tests, with distinct symmetric spectral
representing probabilities in every finite dimension.
-/

open Complex MeasureTheory
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Finite observations miss arbitrary-dimensional affine cubes even after restricting
all tests to real values and both spectral measures to reflection symmetry. -/
theorem exists_symmetric_spectralRepresentingMeasure_cube (k n : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, T (c s).1.1 = T (c t).1.1) ∧
      (∀ t f, (c t).1.1 f ≠ 0 → ∀ y, (f.1 y).im = 0) ∧
      (∀ t, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c t).1 : Measure ℝ) =
        (spectralProbability (c t).1 : Measure ℝ)) ∧
      (∀ t, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace)) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) := by
  obtain ⟨c, b, L, _, haff, hT, _, hkernel, hreal⟩ :=
    exists_spectralRepresentingMeasure_cube_real_directions k n (T.comp paperSplitRealMixture)
  let d (t : Fin n → Set.Icc (0 : ℝ) 1) :=
    paperSplitRealComplexNullMixture ⟨(c t).1, defect_complexNullMixture (c t)⟩
  let L' := paperSplitRealMixture.comp L
  have hkernel' : Function.Injective (fun v => mixtureSample (L' v)) := by
    intro v w h
    apply hkernel
    funext y
    have hh := congrFun h y
    change mixtureSample (paperSplitRealMixture (L v)) y =
      mixtureSample (paperSplitRealMixture (L w)) y at hh
    rw [mixtureSample_paperSplitRealMixture, mixtureSample_paperSplitRealMixture] at hh
    apply Complex.ext
    · exact Complex.ofReal_injective hh
    · rw [hreal, hreal]
  have haff' t : (d t).1.1 = paperSplitRealMixture b + L' (fun i => (t i).1) := by
    change paperSplitRealMixture (c t).1.1 =
      paperSplitRealMixture b + paperSplitRealMixture (L (fun i => (t i).1))
    rw [haff, map_add]
  have hr t : ∀ f, (d t).1.1 f ≠ 0 → ∀ y, (f.1 y).im = 0 :=
    paperSplitRealMixture_real (c t).1.1
  refine ⟨d, paperSplitRealMixture b, L', fun v w h => hkernel' (congrArg mixtureSample h),
    haff', hT, hr, ?_, ?_, ?_⟩
  · intro t
    exact map_neg_spectralProbability_of_real (d t).1 (hr t)
  · intro t
    exact map_neg_spectralTorusProbability_of_real (d t).1 (hr t)
  · intro s t hst
    have hs : mixtureSample (d s).1.1 = mixtureSample (d t).1.1 :=
      (spectralProbability_eq_iff_mixtureSample_eq _ _).mp
        ((spectralTorusProbability_eq_iff_spectralProbability_eq _ _).mp
          (congrArg Subtype.val hst))
    have hL : mixtureSample (L' (fun i => (s i).1)) =
        mixtureSample (L' (fun i => (t i).1)) := by
      funext y
      have hh := congrFun hs y
      rw [haff' s, haff' t] at hh
      simp only [mixtureSample, map_add] at hh
      exact add_left_cancel hh
    have hparam := hkernel' hL
    funext i
    exact Subtype.ext (congrFun hparam i)

/-- Full energy and arbitrary finitely many complex correlations remain fixed on
injective affine cubes of real-test, reflection-symmetric representing probabilities. -/
theorem exists_symmetric_spectralRepresentingMeasure_cube_same_energy_samples (n : ℕ) {k : ℕ}
    (y : Fin k → ℝ) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, energy (c s).1.1 = energy (c t).1.1) ∧
      (∀ i s t, mixtureSample (c s).1.1 (y i) = mixtureSample (c t).1.1 (y i)) ∧
      (∀ t f, (c t).1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      (∀ t, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c t).1 : Measure ℝ) =
        (spectralProbability (c t).1 : Measure ℝ)) ∧
      (∀ t, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace)) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) := by
  let E := ℝ × (Fin k → ℂ)
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨c, b, L, hL, haff, hT, hr, hs, ht, hinj⟩ :=
    exists_symmetric_spectralRepresentingMeasure_cube (Module.finrank ℝ E) n
      (e.toLinearMap.comp (paperEnergySampleObserver y))
  have hobs s t : paperEnergySampleObserver y (c s).1.1 =
      paperEnergySampleObserver y (c t).1.1 := e.injective (hT s t)
  exact ⟨c, b, L, hL, haff, fun s t => congrArg Prod.fst (hobs s t),
    fun i s t => congrFun (congrArg Prod.snd (hobs s t)) i, hr, hs, ht, hinj⟩

end RHTower.WeilWorkPBAP
