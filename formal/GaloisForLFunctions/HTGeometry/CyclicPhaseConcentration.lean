import GaloisForLFunctions.HTGeometry.CyclicPhaseMean
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Off-grid cyclic phase concentration

This module upgrades finite torsion-vertex counting to arbitrary real times.  A cyclic frequency
is drawn once in every coordinate.  After subtracting the exact Dirichlet mean, weighted complex
Hoeffding controls every target ray with its true squared coefficient mass.  The final theorem
puts the mean back and isolates its explicit bias contribution.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cyclic character carried by frequency `q` at real time `t`. -/
def cyclicPhaseValue (p : ℕ) (t : ℝ) (q : Fin p) : ℂ :=
  (cyclicPhaseRatio p t) ^ q.val

lemma integral_cyclicPhaseValue (p : ℕ) [NeZero p] (t : ℝ) :
    ∫ q, cyclicPhaseValue p t q ∂(PMF.uniformOfFintype (Fin p)).toMeasure =
      cyclicPhaseMean p t := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    cyclicPhaseValue, cyclicPhaseMean]
  rw [← Finset.smul_sum]
  simp [Fintype.card_fin]

lemma integral_cyclicCenteredCoordinate (p : ℕ) [NeZero p] (t : ℝ) (w : ℂ) :
    ∫ q, w * (cyclicPhaseValue p t q - cyclicPhaseMean p t)
        ∂(PMF.uniformOfFintype (Fin p)).toMeasure = 0 := by
  rw [integral_const_mul]
  rw [integral_sub]
  · rw [integral_cyclicPhaseValue]
    simp
  · exact Integrable.of_finite
  · exact Integrable.of_finite

/-- Uniform law on one cyclic frequency. -/
def cyclicFrequencyMeasure (p : ℕ) [NeZero p] : Measure (Fin p) :=
  (PMF.uniformOfFintype (Fin p)).toMeasure

/-- Independent uniform cyclic frequencies on every spectral coordinate. -/
def cyclicFrequencyProductMeasure (p : ℕ) [NeZero p] (I : Type*) [Fintype I] :
    Measure (I → Fin p) := Measure.pi fun _ => cyclicFrequencyMeasure p

variable {I : Type*} [Fintype I]

/-- Centred fixed-time cyclic overlap.  The exponent retains the exact squared coefficient mass. -/
theorem measureReal_cyclicCenteredOverlap_ge_le
    (p : ℕ) [NeZero p] (hp : 0 < p) (t : ℝ) (w : I → ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    (cyclicFrequencyProductMeasure p I).real
        {q | r ≤ ‖∑ i, w i *
          (cyclicPhaseValue p t (q i) - cyclicPhaseMean p t)‖} ≤
      4 * Real.exp (-r ^ 2 /
        (16 * (↑(∑ i, ‖w i‖₊ ^ 2) : ℝ))) := by
  classical
  let ν : Measure (Fin p) := cyclicFrequencyMeasure p
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, cyclicFrequencyMeasure]
    infer_instance
  let μ : Measure (I → Fin p) := Measure.pi fun _ => ν
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let X : I → (I → Fin p) → ℂ := fun i q =>
    w i * (cyclicPhaseValue p t (q i) - cyclicPhaseMean p t)
  let b : I → NNReal := fun i => 2 * ‖w i‖₊
  have hindepX : iIndepFun X μ := by
    simpa [X, μ] using
      (iIndepFun_pi (μ := fun _ : I => ν) (X := fun (i : I) (x : Fin p) =>
        w i * (cyclicPhaseValue p t x - cyclicPhaseMean p t))
        (fun _ => Measurable.aemeasurable (measurable_of_finite _)))
  have hindepRe : iIndepFun (fun i q => (X i q).re) μ :=
    hindepX.comp (fun _ => Complex.re) fun _ => Complex.measurable_re
  have hindepIm : iIndepFun (fun i q => (X i q).im) μ :=
    hindepX.comp (fun _ => Complex.im) fun _ => Complex.measurable_im
  have hmeas : ∀ i, AEMeasurable (X i) μ := fun _ =>
    Measurable.aemeasurable (measurable_of_finite _)
  have hbound : ∀ i, ∀ᵐ q ∂μ, ‖X i q‖ ≤ b i := by
    intro i
    filter_upwards [] with q
    have hphase : ‖cyclicPhaseValue p t (q i)‖ = 1 := by
      simp [cyclicPhaseValue, norm_pow, norm_cyclicPhaseRatio]
    have hmean := norm_cyclicPhaseMean_le_one hp t
    calc
      ‖X i q‖ = ‖w i‖ * ‖cyclicPhaseValue p t (q i) - cyclicPhaseMean p t‖ := by
        simp [X]
      _ ≤ ‖w i‖ * (‖cyclicPhaseValue p t (q i)‖ + ‖cyclicPhaseMean p t‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖w i‖ * 2 := by gcongr <;> linarith
      _ = b i := by simp [b]; ring
  have hcentre : ∀ i, ∫ q, X i q ∂μ = 0 := by
    intro i
    rw [MeasureTheory.integral_comp_eval
      (μ := fun _ : I => ν)
      (i := i)
      (f := fun x : Fin p =>
        w i * (cyclicPhaseValue p t x - cyclicPhaseMean p t))
      (Measurable.aestronglyMeasurable (measurable_of_finite _))]
    simpa only [ν, cyclicFrequencyMeasure] using
      integral_cyclicCenteredCoordinate p t (w i)
  have hcentreRe : ∀ i, ∫ q, (X i q).re ∂μ = 0 := by
    intro i
    have hint : Integrable (X i) μ := Integrable.of_finite
    calc
      ∫ q, (X i q).re ∂μ = (∫ q, X i q ∂μ).re := by
        simpa using integral_re hint
      _ = 0 := by rw [hcentre i]; rfl
  have hcentreIm : ∀ i, ∫ q, (X i q).im ∂μ = 0 := by
    intro i
    have hint : Integrable (X i) μ := Integrable.of_finite
    calc
      ∫ q, (X i q).im ∂μ = (∫ q, X i q ∂μ).im := by
        simpa using integral_im hint
      _ = 0 := by rw [hcentre i]; rfl
  have h := measureReal_norm_weighted_sum_ge_le
    X b hindepRe hindepIm hmeas hbound hcentreRe hcentreIm hr
  change μ.real {q | r ≤ ‖∑ i, X i q‖} ≤ _ at h
  have hsum : (↑(∑ i, b i ^ 2) : ℝ) =
      4 * (↑(∑ i, ‖w i‖₊ ^ 2) : ℝ) := by
    simp only [b, NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_mul,
      NNReal.coe_ofNat]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsum] at h
  have hden : 4 * (4 * (↑(∑ i, ‖w i‖₊ ^ 2) : ℝ)) =
      16 * (↑(∑ i, ‖w i‖₊ ^ 2) : ℝ) := by ring
  rw [hden] at h
  simpa [cyclicFrequencyProductMeasure, μ, ν, X] using h

/-- Fixed-time arbitrary-ray cap bound.  An off-grid time pays only its exact Dirichlet mean
contribution; no minimum spectral gap enters. -/
theorem measureReal_cyclicOverlap_ge_le
    (p : ℕ) [NeZero p] (hp : 0 < p) (t : ℝ) (w : I → ℂ)
    {threshold bias : ℝ} (_hbias : 0 ≤ bias) (hthreshold : bias ≤ threshold)
    (hmean : ‖cyclicPhaseMean p t * ∑ i, w i‖ ≤ bias) :
    (cyclicFrequencyProductMeasure p I).real
        {q | threshold ≤ ‖∑ i, w i * cyclicPhaseValue p t (q i)‖} ≤
      4 * Real.exp (-(threshold - bias) ^ 2 /
        (16 * (↑(∑ i, ‖w i‖₊ ^ 2) : ℝ))) := by
  classical
  let μ := cyclicFrequencyProductMeasure p I
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, cyclicFrequencyProductMeasure, cyclicFrequencyMeasure]
    infer_instance
  have hsub : {q : I → Fin p |
      threshold ≤ ‖∑ i, w i * cyclicPhaseValue p t (q i)‖} ⊆
      {q : I → Fin p | threshold - bias ≤ ‖∑ i, w i *
        (cyclicPhaseValue p t (q i) - cyclicPhaseMean p t)‖} := by
    intro q hq
    have hsplit : (∑ i, w i * cyclicPhaseValue p t (q i)) =
        (∑ i, w i * (cyclicPhaseValue p t (q i) - cyclicPhaseMean p t)) +
          cyclicPhaseMean p t * ∑ i, w i := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    simp only [Set.mem_setOf_eq] at hq ⊢
    rw [hsplit] at hq
    have htri := norm_add_le
      (∑ i, w i * (cyclicPhaseValue p t (q i) - cyclicPhaseMean p t))
      (cyclicPhaseMean p t * ∑ i, w i)
    linarith
  have hmono : μ.real
      {q : I → Fin p | threshold ≤ ‖∑ i, w i * cyclicPhaseValue p t (q i)‖} ≤
      μ.real {q : I → Fin p | threshold - bias ≤ ‖∑ i, w i *
        (cyclicPhaseValue p t (q i) - cyclicPhaseMean p t)‖} :=
    measureReal_mono hsub (measure_ne_top μ _)
  exact hmono.trans (measureReal_cyclicCenteredOverlap_ge_le
    p hp t w (sub_nonneg.mpr hthreshold))

end

end GaloisForLFunctions.HTGeometry
