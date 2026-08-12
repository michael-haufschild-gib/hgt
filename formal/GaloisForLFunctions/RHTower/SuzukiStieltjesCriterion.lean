import GaloisForLFunctions.RHTower.SuzukiStieltjesMoments

/-!
# Corrected Suzuki Stieltjes criterion

Suzuki (2022), Theorem 1.8 asserts a determinant-only converse.  The valid Stieltjes
existence theorem requires positive semidefiniteness of every ordinary and shifted Hankel
matrix.  This module proves the resulting exact criterion for Suzuki's literal density.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Full ordinary and shifted Hankel positivity kills the negative Jordan part of Suzuki's
literal signed density.  Hardy determinacy is the key step: a Stieltjes representative plus
the negative part has the same moments as the positive part. -/
theorem suzukiStieltjesNegativeMeasure_eq_zero_of_hankel_posSemidef
    (hPSD :
      (∀ n : ℕ,
        (HTGeometry.momentHankelMatrix suzukiStieltjesMoment n).PosSemidef) ∧
      ∀ n : ℕ,
        (HTGeometry.shiftedMomentHankelMatrix suzukiStieltjesMoment n).PosSemidef) :
    suzukiStieltjesNegativeMeasure = 0 := by
  obtain ⟨ν, hνFinite, hν⟩ :=
    (HTGeometry.stieltjesMomentSequence_iff_hankel_posSemidef).2 hPSD
  letI : IsFiniteMeasure ν := hνFinite
  let r : ℕ → ℝ := fun n =>
    ∫ t : ℝ, t ^ n ∂suzukiStieltjesPositiveMeasure
  have hpositive : HTGeometry.HasStieltjesMoments r
      suzukiStieltjesPositiveMeasure := by
    refine ⟨fun n => ⟨integrable_pow_suzukiStieltjesPositiveMeasure n, rfl⟩,
      suzukiStieltjesPositiveMeasure_support⟩
  have hsum : HTGeometry.HasStieltjesMoments r
      (ν + suzukiStieltjesNegativeMeasure) := by
    constructor
    · intro n
      have hνInt := (hν.1 n).1
      have hnegInt := integrable_pow_suzukiStieltjesNegativeMeasure n
      refine ⟨(integrable_add_measure.2 ⟨hνInt, hnegInt⟩), ?_⟩
      rw [integral_add_measure hνInt hnegInt, (hν.1 n).2]
      dsimp only [r]
      linarith [integral_pow_positive_sub_negative_eq_suzukiStieltjesMoment n]
    · rw [ae_add_measure_iff]
      exact ⟨hν.2, suzukiStieltjesNegativeMeasure_support⟩
  obtain ⟨d, hd, hHardy⟩ := exists_hardy_suzukiStieltjesPositiveMeasure
  have heq : suzukiStieltjesPositiveMeasure =
      ν + suzukiStieltjesNegativeMeasure :=
    HTGeometry.measure_eq_of_hasStieltjesMoments_of_hardy
      hpositive hsum hd hHardy
  have hle : suzukiStieltjesNegativeMeasure ≤
      suzukiStieltjesPositiveMeasure := by
    rw [heq]
    exact Measure.le_add_left (le_refl suzukiStieltjesNegativeMeasure)
  have hsing : suzukiStieltjesPositiveMeasure ⟂ₘ
      suzukiStieltjesNegativeMeasure := by
    unfold suzukiStieltjesPositiveMeasure suzukiStieltjesNegativeMeasure
    exact withDensity_ofReal_mutuallySingular
      continuous_suzukiStieltjesDensity.measurable
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
    hle.absolutelyContinuous hsing.symm

/-- Vanishing negative Jordan part upgrades to pointwise nonnegativity because Suzuki's density
is continuous and the base measure is Lebesgue measure on the open positive half-line. -/
theorem suzukiPsiPointwiseNonnegative_of_stieltjesNegativeMeasure_eq_zero
    (hzero : suzukiStieltjesNegativeMeasure = 0) :
    SuzukiPsiPointwiseNonnegative := by
  have hzeroAE : (fun t : ℝ =>
      ENNReal.ofReal (-suzukiStieltjesDensity t)) =ᵐ[suzukiStieltjesBaseMeasure] 0 := by
    apply (withDensity_eq_zero_iff
      continuous_suzukiStieltjesDensity.measurable.neg.ennreal_ofReal.aemeasurable).1
    exact hzero
  have hae : ∀ᵐ t ∂suzukiStieltjesBaseMeasure,
      0 ≤ suzukiStieltjesDensity t := by
    filter_upwards [hzeroAE] with t ht
    exact neg_nonpos.mp (ENNReal.ofReal_eq_zero.mp ht)
  have hpoint : ∀ t : ℝ, 0 < t → 0 ≤ suzukiStieltjesDensity t := by
    intro t ht
    by_contra hnot
    have htneg : suzukiStieltjesDensity t < 0 := lt_of_not_ge hnot
    let U : Set ℝ := {x | suzukiStieltjesDensity x < 0}
    have hUOpen : IsOpen U :=
      isOpen_lt continuous_suzukiStieltjesDensity continuous_const
    have hnull : suzukiStieltjesBaseMeasure U = 0 := by
      simpa only [U, not_le] using (ae_iff.mp hae)
    have hinterOpen : IsOpen (U ∩ Ioi 0) := hUOpen.inter isOpen_Ioi
    have hnonempty : (U ∩ Ioi 0).Nonempty := ⟨t, htneg, ht⟩
    have hne : volume (U ∩ Ioi 0) ≠ 0 :=
      hinterOpen.measure_ne_zero volume hnonempty
    unfold suzukiStieltjesBaseMeasure at hnull
    rw [Measure.restrict_apply hUOpen.measurableSet] at hnull
    exact hne hnull
  intro t ht
  rcases ht.eq_or_lt with rfl | htpos
  · rw [suzukiPsi_zero]
  · have hdensity := hpoint t htpos
    have hscale : 0 < (1 / 4 : ℝ) * Real.exp (-t / 2) := by positivity
    unfold suzukiStieltjesDensity at hdensity
    exact nonneg_of_mul_nonneg_right hdensity hscale

/-- RH annihilates the negative Jordan part of Suzuki's literal density. -/
theorem suzukiStieltjesNegativeMeasure_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) : suzukiStieltjesNegativeMeasure = 0 := by
  have hsource := suzukiPsiPointwiseNonnegative_of_riemannHypothesis hRH
  unfold suzukiStieltjesNegativeMeasure
  apply (withDensity_eq_zero_iff
    continuous_suzukiStieltjesDensity.measurable.neg.ennreal_ofReal.aemeasurable).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply ENNReal.ofReal_eq_zero.2
  change -suzukiStieltjesDensity t ≤ 0
  rw [neg_nonpos]
  unfold suzukiStieltjesDensity
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    (hsource t ht.le)

/-- Under RH, Suzuki's literal moments are represented by the positive Jordan measure. -/
theorem hasStieltjesMoments_suzukiStieltjesPositiveMeasure_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    HTGeometry.HasStieltjesMoments suzukiStieltjesMoment
      suzukiStieltjesPositiveMeasure := by
  have hzero := suzukiStieltjesNegativeMeasure_eq_zero_of_riemannHypothesis hRH
  refine ⟨fun n => ⟨integrable_pow_suzukiStieltjesPositiveMeasure n, ?_⟩,
    suzukiStieltjesPositiveMeasure_support⟩
  have hsplit := integral_pow_positive_sub_negative_eq_suzukiStieltjesMoment n
  simpa only [hzero, integral_zero_measure, sub_zero] using hsplit

/-- **Corrected Suzuki (2022), Theorem 1.8.**  RH is equivalent to full positive
semidefiniteness of every ordinary and shifted Hankel matrix of Suzuki's literal moments.
This includes singular Stieltjes sequences; determinant signs alone do not. -/
theorem riemannHypothesis_iff_suzukiStieltjes_hankel_posSemidef :
    RiemannHypothesis ↔
      (∀ n : ℕ,
        (HTGeometry.momentHankelMatrix suzukiStieltjesMoment n).PosSemidef) ∧
      ∀ n : ℕ,
        (HTGeometry.shiftedMomentHankelMatrix suzukiStieltjesMoment n).PosSemidef := by
  constructor
  · intro hRH
    apply (HTGeometry.stieltjesMomentSequence_iff_hankel_posSemidef).1
    exact ⟨suzukiStieltjesPositiveMeasure, inferInstance,
      hasStieltjesMoments_suzukiStieltjesPositiveMeasure_of_riemannHypothesis hRH⟩
  · intro hPSD
    exact riemannHypothesis_of_suzukiPsiPointwiseNonnegative
      (suzukiPsiPointwiseNonnegative_of_stieltjesNegativeMeasure_eq_zero
        (suzukiStieltjesNegativeMeasure_eq_zero_of_hankel_posSemidef hPSD))

/-- Valid half of Suzuki's published determinant statement: RH forces both determinant chains
nonnegative.  The converse needs full PSD, not only the leading determinants. -/
theorem riemannHypothesis_implies_suzukiStieltjes_determinant_chains_nonnegative
    (hRH : RiemannHypothesis) :
    (∀ n : ℕ,
      0 ≤ (HTGeometry.momentHankelMatrix suzukiStieltjesMoment n).det) ∧
    ∀ n : ℕ,
      0 ≤ (HTGeometry.shiftedMomentHankelMatrix suzukiStieltjesMoment n).det := by
  have hPSD := riemannHypothesis_iff_suzukiStieltjes_hankel_posSemidef.1 hRH
  exact ⟨fun n => (hPSD.1 n).det_nonneg, fun n => (hPSD.2 n).det_nonneg⟩

end RHTower
