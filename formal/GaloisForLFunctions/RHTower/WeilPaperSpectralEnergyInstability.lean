import GaloisForLFunctions.RHTower.WeilPaperUnboundedSpectralEnergy
import GaloisForLFunctions.RHTower.WeilPaperRepresentingObservationSegments

/-!
# Weakly convergent native laws with divergent full energy

An arbitrarily small convex admixture of a sufficiently energetic complex-null
law preserves normalization and every integer condition. Bounded spectral
expectations change by at most twice the admixture weight times the test norm.
Thus energy can diverge along native laws converging to any fixed native law.
-/

open Complex MeasureTheory Filter Set Topology
open scoped BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Expectations interpolate exactly along the native normalized segment. -/
theorem integral_spectralProbability_paperNormalizedSegment (F : ℝ →ᵇ ℝ)
    (a b : NormalizedMixture) (t : Set.Icc (0 : ℝ) 1) :
    (∫ ξ, F ξ ∂(spectralProbability (paperNormalizedSegment a b t) : Measure ℝ)) =
      (1-t.1) * (∫ ξ, F ξ ∂(spectralProbability a : Measure ℝ)) +
        t.1 * (∫ ξ, F ξ ∂(spectralProbability b : Measure ℝ)) := by
  simp only [integral_spectralProbability_eq_paperSpectralIntegralObserver,
    paperNormalizedSegment_observe, smul_eq_mul]

private theorem norm_spectralExpectation_le (F : ℝ →ᵇ ℝ) (a : NormalizedMixture) :
    ‖∫ ξ, F ξ ∂(spectralProbability a : Measure ℝ)‖ ≤ ‖F‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := (spectralProbability a : Measure ℝ))
    (Filter.Eventually.of_forall F.norm_coe_le_norm)

/-- A small admixture uniformly controls every bounded continuous spectral expectation. -/
theorem norm_spectralExpectation_segment_sub_le (F : ℝ →ᵇ ℝ)
    (a b : NormalizedMixture) (t : Set.Icc (0 : ℝ) 1) :
    ‖(∫ ξ, F ξ ∂(spectralProbability (paperNormalizedSegment a b t) : Measure ℝ)) -
      (∫ ξ, F ξ ∂(spectralProbability a : Measure ℝ))‖ ≤ 2*t.1*‖F‖ := by
  rw [integral_spectralProbability_paperNormalizedSegment]
  let A := ∫ ξ, F ξ ∂(spectralProbability a : Measure ℝ)
  let D := ∫ ξ, F ξ ∂(spectralProbability b : Measure ℝ)
  change ‖(1-t.1)*A+t.1*D-A‖ ≤ _
  rw [show (1-t.1)*A+t.1*D-A = t.1*(D-A) by ring,
    norm_mul, Real.norm_of_nonneg t.2.1]
  calc
    _ ≤ t.1*(‖D‖+‖A‖) := mul_le_mul_of_nonneg_left (norm_sub_le D A) t.2.1
    _ ≤ t.1*(‖F‖+‖F‖) := mul_le_mul_of_nonneg_left
      (add_le_add (norm_spectralExpectation_le F b) (norm_spectralExpectation_le F a)) t.2.1
    _ = _ := by ring

/-- Positive weights tending to zero, including the initial endpoint. -/
def paperVanishingSpectralWeight (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / ((n : ℝ)+1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      have hn : 0 ≤ (n : ℝ) := by positivity
      linarith⟩

/-- The second law may vary arbitrarily: vanishing admixture still gives weak convergence. -/
theorem tendsto_spectralProbability_vanishing_admixture
    (a : NormalizedMixture) (b : ℕ → NormalizedMixture) :
    Tendsto (fun n => spectralProbability
      (paperNormalizedSegment a (b n) (paperVanishingSpectralWeight n)))
      atTop (𝓝 (spectralProbability a)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    norm_spectralExpectation_segment_sub_le F a (b n) (paperVanishingSpectralWeight n)) ?_
  have hw : Tendsto (fun n => (paperVanishingSpectralWeight n).1) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using (tendsto_const_nhds.mul hw).mul_const ‖F‖

/-- Weak convergence survives the prime-torus map and exact origin constraints. -/
theorem tendsto_spectralRepresentingMeasure_vanishing_admixture
    (a : ComplexNullMixture) (b : ℕ → ComplexNullMixture) :
    Tendsto (fun n => spectralRepresentingMeasure
      (paperComplexNullSegment a (b n) (paperVanishingSpectralWeight n)))
      atTop (𝓝 (spectralRepresentingMeasure a)) := by
  apply tendsto_subtype_rng.mpr
  exact ((ProbabilityMeasure.continuous_map continuous_primeSpectralPoint).tendsto
    (spectralProbability a.1)).comp
      (tendsto_spectralProbability_vanishing_admixture a.1 (fun n => (b n).1))

/-- At every actual native law, native laws can converge weakly while full energy diverges. -/
theorem exists_spectralRepresentingMeasure_tendsto_energy_atTop (a : ComplexNullMixture) :
    ∃ c : ℕ → ComplexNullMixture,
      Tendsto (fun n => spectralRepresentingMeasure (c n)) atTop
        (𝓝 (spectralRepresentingMeasure a)) ∧
      Tendsto (fun n => energy (c n).1.1) atTop atTop := by
  classical
  let t := paperVanishingSpectralWeight
  have ht (n : ℕ) : 0 < (t n).1 := by
    change 0 < 1 / ((n : ℝ)+1)
    positivity
  choose b hb using fun n : ℕ => exists_complexNullMixture_energy_gt
    (((n : ℝ)+1-(1-(t n).1)*energy a.1.1)/(t n).1)
  let c (n : ℕ) := paperComplexNullSegment a (b n) (t n)
  have he (n : ℕ) : (n : ℝ)+1 < energy (c n).1.1 := by
    have hh := (div_lt_iff₀ (ht n)).mp (hb n)
    change (n : ℝ)+1 < energy (paperNormalizedSegment a.1 (b n).1 (t n)).1
    rw [paperNormalizedSegment_observe]
    simp only [smul_eq_mul]
    linarith only [hh]
  refine ⟨c, tendsto_spectralRepresentingMeasure_vanishing_admixture a b, ?_⟩
  exact tendsto_atTop_mono (fun n => by linarith [he n])
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Even on the actual native image, full energy admits no continuous realization. -/
theorem no_continuous_native_full_energy :
    ¬ ∃ F : C(Set.range spectralRepresentingMeasure, ℝ),
      ∀ c : ComplexNullMixture,
        F ⟨spectralRepresentingMeasure c, Set.mem_range_self c⟩ = energy c.1.1 := by
  rintro ⟨F, hF⟩
  obtain ⟨a, _⟩ := exists_complexNullMixture_energy_gt 0
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_energy_atTop a
  let a' : Set.range spectralRepresentingMeasure :=
    ⟨spectralRepresentingMeasure a, Set.mem_range_self a⟩
  let c' (n : ℕ) : Set.range spectralRepresentingMeasure :=
    ⟨spectralRepresentingMeasure (c n), Set.mem_range_self (c n)⟩
  have hc' : Tendsto c' atTop (𝓝 a') := tendsto_subtype_rng.mpr hc
  have hlim : Tendsto (fun n => energy (c n).1.1) atTop (𝓝 (energy a.1.1)) := by
    simpa only [Function.comp_def, c', a', hF] using (F.continuous.tendsto a').comp hc'
  exact not_tendsto_nhds_of_tendsto_atTop he _ hlim

end RHTower.WeilWorkPBAP
