import GaloisForLFunctions.RHTower.WeilWorkPBAPMomentPackets
import GaloisForLFunctions.RHTower.WeilRegularDeviationRigidity

/-!
# Actual spectral probabilities of normalized null mixtures

The Fourier-square density of a nonnegative, mass-one mixture of compact C² Weil
tests is a probability density. Its pushforward along the prime phase flow has
rational character moments equal to the actual autocorrelation samples. Thus the
normalized moment-packet construction produces representing probability measures
with its exact finite coefficient multiplier, without assuming Weil positivity.
-/

open Complex MeasureTheory Zeta23 GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate ContDiff

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- The spectral density in the frequency convention of mathlib Fourier inversion. -/
def testSpectralDensity (f : WeilTestFn) (ξ : ℝ) : ℝ :=
  ‖paperFT f.1 (-(2 * Real.pi * (ξ : ℂ)))‖ ^ 2

theorem testSpectralDensity_nonneg (f : WeilTestFn) (ξ : ℝ) :
    0 ≤ testSpectralDensity f ξ := sq_nonneg _

theorem continuous_testSpectralDensity (f : WeilTestFn) :
    Continuous (testSpectralDensity f) :=
  (((Zeta23.WeilEF.differentiable_paperFT f.2.1.continuous f.2.2).continuous.comp
    (by fun_prop)).norm).pow 2

private theorem test_support_bound (f : WeilTestFn) :
    ∃ A : ℝ, tsupport f.1 ⊆ Set.Icc (-A) A := by
  obtain ⟨A, hA⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨A, fun u hu => ?_⟩
  have h := hA hu
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  exact abs_le.mp h

theorem integrable_testSpectralDensity (f : WeilTestFn) :
    Integrable (testSpectralDensity f) := by
  obtain ⟨A, hA⟩ := test_support_bound f
  have h := (integrable_normSq_paperFT f.2.1 hA).comp_mul_left'
    (show -(2 * Real.pi) ≠ 0 by
      exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  convert h using 1
  funext ξ
  unfold testSpectralDensity
  congr 3
  push_cast
  ring

private theorem integrable_testSpectralDensity_phase (f : WeilTestFn) (y : ℝ) :
    Integrable (fun ξ : ℝ =>
      (testSpectralDensity f ξ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y)) := by
  refine (integrable_testSpectralDensity f).ofReal.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (continuous_testSpectralDensity f)).mul
      (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      simp [Complex.norm_exp, abs_of_nonneg (testSpectralDensity_nonneg f ξ)]

/-- Literal Fourier inversion of the C² autocorrelation, with the fixed `2π` convention. -/
theorem weilTest_eq_integral_testSpectralDensity (f : WeilTestFn) (y : ℝ) :
    EF.weilTest f.1 f.1 y = ∫ ξ : ℝ,
      (testSpectralDensity f ξ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y) := by
  obtain ⟨A, hA⟩ := test_support_bound f
  have hs : ∀ u, f.1 u ≠ 0 → |u| ≤ A := fun u hu =>
    abs_le.mpr (hA (subset_tsupport _ hu))
  rw [WeilRegular.weilTest_eq_integral f.2.1 f.2.2 hs]
  simp only [WeilRegular.pairTransform_ofReal f.2.1 f.2.2, testSpectralDensity]

/-- The actual finite sum of weighted Fourier squares. -/
def mixtureSpectralDensity (c : WeilTestFn →₀ ℝ) (ξ : ℝ) : ℝ :=
  c.sum (fun f t => t * testSpectralDensity f ξ)

theorem continuous_mixtureSpectralDensity (c : WeilTestFn →₀ ℝ) :
    Continuous (mixtureSpectralDensity c) :=
  continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_testSpectralDensity f)

theorem integrable_mixtureSpectralDensity (c : WeilTestFn →₀ ℝ) :
    Integrable (mixtureSpectralDensity c) :=
  integrable_finsetSum _ fun f _ => (integrable_testSpectralDensity f).const_mul _

theorem mixtureSpectralDensity_nonneg (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (ξ : ℝ) : 0 ≤ mixtureSpectralDensity c ξ :=
  Finset.sum_nonneg fun f _ => mul_nonneg (hc f) (testSpectralDensity_nonneg f ξ)

/-- Every sample is the Fourier integral of the mixture's actual spectral density. -/
theorem mixtureSample_eq_integral_density (c : WeilTestFn →₀ ℝ) (y : ℝ) :
    mixtureSample c y = ∫ ξ : ℝ,
      (mixtureSpectralDensity c ξ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y) := by
  simp only [mixtureSample, Finsupp.linearCombination_apply, Finsupp.sum, Complex.real_smul]
  calc
    (∑ f ∈ c.support, (c f : ℂ) * EF.weilTest f.1 f.1 y) =
        ∑ f ∈ c.support, ∫ ξ : ℝ, (c f : ℂ) *
          ((testSpectralDensity f ξ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y)) := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [weilTest_eq_integral_testSpectralDensity, integral_const_mul]
    _ = ∫ ξ : ℝ, ∑ f ∈ c.support, (c f : ℂ) *
          ((testSpectralDensity f ξ : ℂ) * Complex.exp (2 * Real.pi * I * ξ * y)) :=
      (integral_finsetSum _ fun f _ =>
        (integrable_testSpectralDensity_phase f y).const_mul (c f : ℂ)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp [mixtureSpectralDensity, Finsupp.sum, Finset.sum_mul, mul_assoc]

theorem mixtureSample_zero_eq_integral_density (c : WeilTestFn →₀ ℝ) :
    mixtureSample c 0 = ((∫ ξ, mixtureSpectralDensity c ξ : ℝ) : ℂ) := by
  rw [mixtureSample_eq_integral_density]
  simpa using Complex.ofRealCLM.integral_comp_comm (integrable_mixtureSpectralDensity c)

/-- Nonnegative finite test mixtures with autocorrelation mass one. -/
abbrev NormalizedMixture :=
  {c : WeilTestFn →₀ ℝ // (∀ f, 0 ≤ c f) ∧ mixtureSample c 0 = 1}

theorem integral_density_normalized (c : NormalizedMixture) :
    ∫ ξ, mixtureSpectralDensity c.1 ξ = 1 := by
  have h := congrArg Complex.re c.2.2
  rw [mixtureSample_zero_eq_integral_density] at h
  simpa using h

/-- The spectral probability has the literal Fourier-square density of the tests. -/
def spectralProbability (c : NormalizedMixture) : ProbabilityMeasure ℝ :=
  ⟨volume.withDensity (fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_mixtureSpectralDensity c.1)
        (Filter.Eventually.of_forall (mixtureSpectralDensity_nonneg c.1 c.2.1)),
      integral_density_normalized, ENNReal.ofReal_one]⟩⟩

theorem integral_spectralProbability (c : NormalizedMixture) (F : ℝ → ℂ) :
    ∫ ξ, F ξ ∂(spectralProbability c : Measure ℝ) =
      ∫ ξ, (mixtureSpectralDensity c.1 ξ : ℂ) * F ξ := by
  change ∫ ξ, F ξ ∂volume.withDensity
    (fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_mixtureSpectralDensity c.1).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [ENNReal.toReal_ofReal (mixtureSpectralDensity_nonneg c.1 c.2.1 ξ), Complex.real_smul]

/-- Prime phases in the same frequency convention as the spectral density. -/
def primeSpectralPoint (ξ : ℝ) : PrimePhaseSpace :=
  clockPhasePoint (fun p : Nat.Primes => Real.log (p : ℕ)) (2 * Real.pi * ξ)

theorem continuous_primeSpectralPoint : Continuous primeSpectralPoint := by
  unfold primeSpectralPoint clockPhasePoint
  fun_prop

theorem arithmeticExponent_detuning {n : ℕ} (hn : n ≠ 0) :
    characterDetuning (arithmeticExponent n) (fun p : Nat.Primes => Real.log (p : ℕ)) =
      Real.log n := by
  rw [log_nat_eq_sum_factorization hn]
  unfold characterDetuning arithmeticExponent
  change ((primeExponentVector n).mapRange (fun k : ℕ => (k : ℤ)) (by simp)).sum
    (fun p k => (k : ℝ) * Real.log (p : ℕ)) = _
  rw [Finsupp.sum_mapRange_index]
  · simp
  · intro p
    simp

theorem arithmeticPhase_primeSpectralPoint {n : ℕ} (hn : n ≠ 0) (ξ : ℝ) :
    arithmeticPhase n (primeSpectralPoint ξ) =
      Complex.exp (2 * Real.pi * I * ξ * Real.log n) := by
  rw [arithmeticPhase, primeSpectralPoint, torusCharacter_clockPhasePoint,
    arithmeticExponent_detuning hn]
  congr 1
  push_cast
  ring

theorem rationalPhase_primeSpectralPoint {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (ξ : ℝ) :
    arithmeticPhase a (primeSpectralPoint ξ) * conj (arithmeticPhase b (primeSpectralPoint ξ)) =
      Complex.exp (2 * Real.pi * I * ξ * (Real.log a - Real.log b)) := by
  rw [arithmeticPhase_primeSpectralPoint ha, arithmeticPhase_primeSpectralPoint hb,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, map_ofNat, Complex.conj_I]
  push_cast
  ring

/-- The actual spectral probability pushed to the compact prime torus. -/
def spectralTorusProbability (c : NormalizedMixture) : ProbabilityMeasure PrimePhaseSpace :=
  (spectralProbability c).map continuous_primeSpectralPoint.measurable.aemeasurable

/-- Rational character moments are the actual autocorrelation samples, with no limiting step. -/
theorem phaseMoment_spectralTorusProbability (c : NormalizedMixture)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    phaseMoment (spectralTorusProbability c) a b =
      mixtureSample c.1 (Real.log a - Real.log b) := by
  unfold phaseMoment spectralTorusProbability
  have hcont : Continuous (fun z : PrimePhaseSpace =>
      arithmeticPhase a z * conj (arithmeticPhase b z)) :=
    (arithmeticPhase a).continuous.mul (arithmeticPhase b).continuous.star
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map continuous_primeSpectralPoint.measurable.aemeasurable
      hcont.aestronglyMeasurable,
    integral_spectralProbability, mixtureSample_eq_integral_density]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [rationalPhase_primeSpectralPoint ha hb]
    simp only [Complex.ofReal_sub]

/-- The complex-null subclass used in the representing-measure density construction. -/
abbrev ComplexNullMixture :=
  {c : NormalizedMixture // ∀ n : ℕ, 2 ≤ n → mixtureSample c.1 (Real.log n) = 0}

/-- Every complex-null mixture produces an origin-representing probability measure. -/
def spectralRepresentingMeasure (c : ComplexNullMixture) : RepresentingPhaseMeasure :=
  ⟨spectralTorusProbability c.1, by
    intro n hn
    have h := phaseMoment_spectralTorusProbability c.1 (by omega : n ≠ 0) one_ne_zero
    simpa [phaseMoment, c.2 n hn] using h⟩

/-- The finite moment construction now yields an actual spectral representing measure,
retaining smooth tests, exact normalization, and every bounded-denominator moment. -/
theorem exists_spectral_representing_mixture (N L : ℕ)
    (μ : RepresentingPhaseMeasure) (d : UnitPacketCoeffs N) :
    ∃ (f : PacketIndex N → WeilTestFn) (c : ComplexNullMixture),
      (∀ i, ContDiff ℝ ∞ (f i).1) ∧
      c.1.1 = (packetMass N (L + 1))⁻¹ • packetMixture f ∧
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → b ≤ L + 1 →
        phaseMoment (spectralRepresentingMeasure c).1 a b =
          phaseMoment μ.1 a b * packetCoeffCorrelation d.1 a b := by
  obtain ⟨f, c, hf, hcf, hc, _, hm, hs⟩ := exists_normalized_representing_mixture N L μ d
  let c₀ : NormalizedMixture := ⟨c, hc, hm⟩
  have hn : ∀ n : ℕ, 2 ≤ n → mixtureSample c (Real.log n) = 0 := by
    intro n hn
    have h := hs n 1 (by omega) le_rfl (by omega)
    simpa [phaseMoment, μ.2 n hn] using h
  let c₁ : ComplexNullMixture := ⟨c₀, hn⟩
  refine ⟨f, c₁, hf, hcf, ?_⟩
  intro a b ha hb hbL
  change phaseMoment (spectralTorusProbability c₀) a b = _
  rw [phaseMoment_spectralTorusProbability c₀ (by omega) (by omega)]
  exact hs a b ha hb hbL

end RHTower.WeilWorkPBAP
