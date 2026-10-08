import GaloisForLFunctions.RHTower.WeilPaperMixtureRealification
import GaloisForLFunctions.RHTower.WeilPaperSpectralObservationFibres

/-!
# Finite observations leave distinct representing spectral probabilities

Apply finite-dimensional kernel separation after positive conjugation averaging.
The real consecutive-ratio sampler retains a nonzero direction. Common positive
normalization realizes it inside the native full-complex-null probability class.
-/

open Complex
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Positive conjugation averaging retains a sampled kernel direction of any finite observer. -/
theorem exists_positive_complex_null_pair_same_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ a b : WeilTestFn →₀ ℝ,
      (∀ f, 0 ≤ a f) ∧ (∀ f, 0 ≤ b f) ∧
      (∀ n : ℕ, 2 ≤ n → mixtureSample a (Real.log n) = 0 ∧
        mixtureSample b (Real.log n) = 0) ∧
      mixtureSample a 0 = mixtureSample b 0 ∧ T a = T b ∧
      ∃ r : PaperPacketPrimitiveEdge (k + 3),
        mixtureSample a (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  obtain ⟨d, hd, hs⟩ := exists_paperNullMassSpace_finite_observation_kernel k
    (T.comp paperRealMixture)
  obtain ⟨i, hi⟩ : ∃ i, paperConsecutiveSampler (k + 1) d i ≠ 0 := by
    by_contra! h
    exact hs (funext h)
  refine ⟨paperRealMixture (paperNullPositivePart d),
    paperRealMixture (paperNullNegativePart d),
    paperRealMixture_nonneg _ (paperNullPositivePart_nonneg d),
    paperRealMixture_nonneg _ (paperNullNegativePart_nonneg d), ?_, ?_, ?_,
    paperConsecutiveEdge (k + 1) i, ?_⟩
  · intro n hn
    exact ⟨(defect_eq_zero_iff_paperRealMixture_complex_null _).mp
      (defect_paperNullPositivePart d) n hn,
      (defect_eq_zero_iff_paperRealMixture_complex_null _).mp
      (defect_paperNullNegativePart d) n hn⟩
  · simpa only [mixtureSample_paperRealMixture_zero] using paperNullPositivePart_mass_eq d
  · apply sub_eq_zero.mp
    rw [← map_sub, ← map_sub, paperNullPositivePart_sub_negativePart]
    exact hd
  · intro heq
    have hre := congrArg Complex.re heq
    simp only [mixtureSample_paperRealMixture, Complex.ofReal_re] at hre
    apply hi
    rw [paperConsecutiveSampler_apply, ← mixtureSample_paperNullParts_sub,
      Complex.sub_re, hre, sub_self]

/-- Arbitrary finite real linear observations leave distinct full-complex-null mass-one mixtures. -/
theorem exists_complexNullMixtures_same_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ a b : ComplexNullMixture, T a.1.1 = T b.1.1 ∧
      ∃ r : PaperPacketPrimitiveEdge (k + 3),
        mixtureSample a.1.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b.1.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  obtain ⟨a, b, ha, hb, hn, hm, hT, r, hr⟩ :=
    exists_positive_complex_null_pair_same_finite_observations k T
  let M : ℝ := (mixtureSample a 0).re
  let y : ℝ := Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)
  have hbM : (mixtureSample b 0).re = M := by rw [← hm]
  have hM : 0 < M := by
    have hpos : 0 < ‖mixtureSample a y - mixtureSample b y‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hr)
    have hbound : ‖mixtureSample a y - mixtureSample b y‖ ≤ M + M :=
      (norm_sub_le _ _).trans (add_le_add (mixtureSample_norm_le_mass a ha y) (by
        simpa only [hbM] using mixtureSample_norm_le_mass b hb y))
    linarith
  have hza : mixtureSample a 0 = (M : ℂ) := mixtureSample_zero_real a
  have hzb : mixtureSample b 0 = (M : ℂ) := hm.symm.trans hza
  let a₀ := paperNormalizeMass M hM a ha hza
  let b₀ := paperNormalizeMass M hM b hb hzb
  have han : ∀ n : ℕ, 2 ≤ n → mixtureSample a₀.1 (Real.log n) = 0 := by
    intro n hn'
    change mixtureSample (M⁻¹ • a) _ = 0
    rw [mixtureSample_smul, (hn n hn').1, smul_zero]
  have hbn : ∀ n : ℕ, 2 ≤ n → mixtureSample b₀.1 (Real.log n) = 0 := by
    intro n hn'
    change mixtureSample (M⁻¹ • b) _ = 0
    rw [mixtureSample_smul, (hn n hn').2, smul_zero]
  refine ⟨⟨a₀, han⟩, ⟨b₀, hbn⟩, ?_, r, ?_⟩
  · change T (M⁻¹ • a) = T (M⁻¹ • b)
    rw [map_smul, map_smul, hT]
  · intro heq
    apply hr
    change mixtureSample (M⁻¹ • a) y = mixtureSample (M⁻¹ • b) y at heq
    rw [mixtureSample_smul, mixtureSample_smul, Complex.real_smul, Complex.real_smul] at heq
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hM.ne')) heq

/-- Full energy and any finite list of complex correlations admit distinct origin-representing
spectral realizations, separated by a ratio with labels at most `2*k+4`. -/
theorem exists_complexNullMixtures_same_energy_samples {k : ℕ} (y : Fin k → ℝ) :
    ∃ a b : ComplexNullMixture, energy a.1.1 = energy b.1.1 ∧
      (∀ i, mixtureSample a.1.1 (y i) = mixtureSample b.1.1 (y i)) ∧
      ∃ r : PaperPacketPrimitiveEdge (2 * k + 4),
        mixtureSample a.1.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b.1.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  let E := ℝ × (Fin k → ℂ)
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨a, b, hT, r, hr⟩ := exists_complexNullMixtures_same_finite_observations
    (Module.finrank ℝ E) (e.toLinearMap.comp (paperEnergySampleObserver y))
  have hobs : paperEnergySampleObserver y a.1.1 = paperEnergySampleObserver y b.1.1 :=
    e.injective hT
  have hdim : Module.finrank ℝ E + 3 = 2 * k + 4 := by
    dsimp [E]
    rw [Module.finrank_prod, Module.finrank_self, finrank_real_of_complex, Module.finrank_fin_fun]
    omega
  refine ⟨a, b, congrArg Prod.fst hobs, fun i => congrFun (congrArg Prod.snd hobs) i, ?_⟩
  rw [← hdim]
  exact ⟨r, hr⟩

/-- Actual origin-representing probabilities need not be determined by full energy and
finitely many autocorrelation samples. -/
theorem exists_distinct_spectralRepresentingMeasures_same_energy_samples {k : ℕ}
    (y : Fin k → ℝ) :
    ∃ a b : ComplexNullMixture, energy a.1.1 = energy b.1.1 ∧
      (∀ i, mixtureSample a.1.1 (y i) = mixtureSample b.1.1 (y i)) ∧
      spectralRepresentingMeasure a ≠ spectralRepresentingMeasure b := by
  obtain ⟨a, b, he, hs, r, hr⟩ := exists_complexNullMixtures_same_energy_samples y
  refine ⟨a, b, he, hs, ?_⟩
  intro hab
  have hm := congrArg (fun μ : RepresentingPhaseMeasure =>
    phaseMoment μ.1 (r.1.1 : ℕ) (r.1.2 : ℕ)) hab
  have hl : (r.1.1 : ℕ) ≠ 0 := by have := (Finset.mem_Icc.mp r.1.1.property).1; omega
  have hr' : (r.1.2 : ℕ) ≠ 0 := by have := (Finset.mem_Icc.mp r.1.2.property).1; omega
  change phaseMoment (spectralTorusProbability a.1) _ _ =
    phaseMoment (spectralTorusProbability b.1) _ _ at hm
  rw [phaseMoment_spectralTorusProbability _ hl hr',
    phaseMoment_spectralTorusProbability _ hl hr'] at hm
  exact hr hm

end RHTower.WeilWorkPBAP
