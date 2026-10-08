import GaloisForLFunctions.RHTower.WeilPaperSpectralObservationFibres

/-!
# A continuum of spectra with the same finite observations

Convex interpolation of the paper-derived normalized null pair retains every
integer constraint, full energy and any selected finite sample list. A separating
primitive rational moment makes the resulting spectral probabilities injective
in the interpolation parameter.
-/

noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Convex interpolation stays inside the actual mass-one positive mixture space. -/
def paperNormalizedSegment (a b : NormalizedMixture) (t : Set.Icc (0 : ℝ) 1) :
    NormalizedMixture :=
  ⟨(1 - t.1) • a.1 + t.1 • b.1,
    (fun f => add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (a.property.1 f))
      (mul_nonneg t.property.1 (b.property.1 f))), by
    change (Finsupp.linearCombination ℝ _) ((1 - t.1) • a.1 + t.1 • b.1) = 1
    rw [map_add, map_smul, map_smul]
    change (1 - t.1) • mixtureSample a.1 0 + t.1 • mixtureSample b.1 0 = 1
    rw [a.property.2, b.property.2, ← add_smul, sub_add_cancel, one_smul]⟩

/-- Every real linear observation is affine along the normalized segment. -/
theorem paperNormalizedSegment_observe {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] E) (a b : NormalizedMixture) (t : Set.Icc (0 : ℝ) 1) :
    T (paperNormalizedSegment a b t).1 = (1 - t.1) • T a.1 + t.1 • T b.1 := by
  exact (map_add T _ _).trans (congrArg₂ (· + ·) (map_smul T _ _) (map_smul T _ _))

/-- Complex autocorrelation is affine in the same native interpolation parameter. -/
theorem mixtureSample_paperNormalizedSegment (a b : NormalizedMixture)
    (t : Set.Icc (0 : ℝ) 1) (y : ℝ) :
    mixtureSample (paperNormalizedSegment a b t).1 y =
      (1 - t.1) • mixtureSample a.1 y + t.1 • mixtureSample b.1 y :=
  paperNormalizedSegment_observe (Finsupp.linearCombination ℝ _) a b t

private theorem complex_segment_injective (a b : ℂ) (hab : a ≠ b) :
    Function.Injective (fun t : ℝ => ((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b) := by
  intro t s h
  push_cast at h
  have hz : ((t : ℂ) - (s : ℂ)) * (b - a) = 0 := by linear_combination h
  have ht : (t : ℂ) - (s : ℂ) = 0 :=
    (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hab.symm)
  exact Complex.ofReal_injective (sub_eq_zero.mp ht)

/-- Every finite list of correlation locations has an entire injective interval of actual
spectral probabilities sharing full energy, all integer constraints, and those correlations. -/
theorem exists_injective_spectral_null_energy_samples_family {k : ℕ} (y : Fin k → ℝ) :
    ∃ c : Set.Icc (0 : ℝ) 1 → NormalizedMixture,
      (∀ t, defect (c t).1 = 0) ∧
      (∀ s t, energy (c s).1 = energy (c t).1) ∧
      (∀ i s t, mixtureSample (c s).1 (y i) = mixtureSample (c t).1 (y i)) ∧
      Function.Injective (fun t => spectralTorusProbability (c t)) := by
  obtain ⟨a, b, ha, hb, he, hs, r, hr⟩ := exists_normalized_null_same_energy_samples_pair y
  have hobs : paperEnergySampleObserver y a.1 = paperEnergySampleObserver y b.1 :=
    Prod.ext he (funext hs)
  have hconst (t : Set.Icc (0 : ℝ) 1) :
      paperEnergySampleObserver y (paperNormalizedSegment a b t).1 =
        paperEnergySampleObserver y a.1 := by
    rw [paperNormalizedSegment_observe, ← hobs, ← add_smul, sub_add_cancel, one_smul]
  refine ⟨paperNormalizedSegment a b, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [paperNormalizedSegment_observe, ha, hb, smul_zero, smul_zero, zero_add]
  · intro s t
    exact congrArg Prod.fst ((hconst s).trans (hconst t).symm)
  · intro i s t
    exact congrFun (congrArg Prod.snd ((hconst s).trans (hconst t).symm)) i
  · intro s t hst
    have hleft : (r.1.1 : ℕ) ≠ 0 := by
      have := (Finset.mem_Icc.mp r.1.1.property).1
      omega
    have hright : (r.1.2 : ℕ) ≠ 0 := by
      have := (Finset.mem_Icc.mp r.1.2.property).1
      omega
    have h := congrArg (fun μ => phaseMoment μ (r.1.1 : ℕ) (r.1.2 : ℕ)) hst
    rw [phaseMoment_spectralTorusProbability _ hleft hright,
      phaseMoment_spectralTorusProbability _ hleft hright,
      mixtureSample_paperNormalizedSegment, mixtureSample_paperNormalizedSegment,
      Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul] at h
    exact Subtype.ext (complex_segment_injective _ _ hr h)

/-- The same constant-observation interval also has injective real-line spectral probabilities. -/
theorem exists_injective_real_spectral_null_energy_samples_family {k : ℕ} (y : Fin k → ℝ) :
    ∃ c : Set.Icc (0 : ℝ) 1 → NormalizedMixture,
      (∀ t, defect (c t).1 = 0) ∧
      (∀ s t, energy (c s).1 = energy (c t).1) ∧
      (∀ i s t, mixtureSample (c s).1 (y i) = mixtureSample (c t).1 (y i)) ∧
      Function.Injective (fun t => spectralProbability (c t)) := by
  obtain ⟨c, hc, he, hs, hinj⟩ := exists_injective_spectral_null_energy_samples_family y
  refine ⟨c, hc, he, hs, fun s t h => hinj ?_⟩
  exact congrArg (fun μ : MeasureTheory.ProbabilityMeasure ℝ =>
    μ.map continuous_primeSpectralPoint.measurable.aemeasurable) h

end RHTower.WeilWorkPBAP
