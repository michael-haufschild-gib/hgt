import GaloisForLFunctions.BiScaleUncertainty.SieveRawMomentPerturbation
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm
import GaloisForLFunctions.BiScaleUncertainty.SieveThresholdRounding
import GaloisForLFunctions.BezoutValuationIncidence.SixModeStabilityAndSharpQuarterDecorrelation
import GaloisForLFunctions.BiScaleUncertainty.SieveCanonicalTranslation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform recovery modulo one physical translation across vanishing arithmetic support. -/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open BezoutValuationIncidence ValuationPhase
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Actual inverse weights for the significant part of the source. -/
def thresholdSourceWeights (N : ℕ) (c : ℕ → ℝ) (δ : ℝ) : ℕ → ℝ :=
  _root_.RHTower.pmRamanujanResidueCoeff (fun q => Threshold.source δ (selbergMultiplesCoord N c q)) N

/-- Actual inverse weights with source magnitudes and competitor signs. -/
def thresholdTargetWeights (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ) : ℕ → ℝ :=
  _root_.RHTower.pmRamanujanResidueCoeff
    (fun q => Threshold.target δ (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q)) N

theorem coordinate_thresholdSource (N : ℕ) (c : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (q : ℕ) :
    selbergMultiplesCoord N (thresholdSourceWeights N c δ) q =
      Threshold.source δ (selbergMultiplesCoord N c q) := by
  rw [thresholdSourceWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Finset.Icc 1 N
  · simp [hq]
  · rw [if_neg hq, selbergMultiplesCoord_eq_zero_of_notMem c hq]
    simp [Threshold.source, not_lt.mpr hδ]

theorem coordinate_thresholdTarget (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (q : ℕ) :
    selbergMultiplesCoord N (thresholdTargetWeights N c e δ) q =
      Threshold.target δ (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q) := by
  rw [thresholdTargetWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Finset.Icc 1 N
  · simp [hq]
  · rw [if_neg hq, selbergMultiplesCoord_eq_zero_of_notMem c hq]
    simp [Threshold.target, not_lt.mpr hδ]

private theorem magnitude_error_all (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h6 : ∀ h : Fin 6 → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ δ^6) (q : ℕ) :
    abs (|selbergMultiplesCoord N c q| - |selbergMultiplesCoord N e q|) ≤ δ := by
  by_cases hq : q ∈ Finset.Icc 1 N
  · exact coordinate_magnitude_error N c e δ hδ h6 q hq
  · rw [selbergMultiplesCoord_eq_zero_of_notMem c hq,
      selbergMultiplesCoord_eq_zero_of_notMem e hq]
    simpa using hδ

/-- The rounded actual profiles have exactly equal fifth and sixth arrays. -/
theorem threshold_moments_eq (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h6 : ∀ h : Fin 6 → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ δ^6)
    (m : ℕ) (hm : m = 5 ∨ m = 6)
    (hnoise : ∀ h : Fin m → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ δ^6) :
    ∀ h : Fin m → ℕ,
      translatedMoment N (thresholdSourceWeights N c δ) h =
        translatedMoment N (thresholdTargetWeights N c e δ) h := by
  apply (moments_eq_iff_resonant_products _ _ _ _).mpr
  intro r hr
  simp_rw [coordinate_thresholdSource N c δ hδ, coordinate_thresholdTarget N c e δ hδ]
  exact Threshold.products_eq hm δ hδ hδ1
    (fun i => selbergMultiplesCoord N c (addOrderOf (r i)))
    (fun i => selbergMultiplesCoord N e (addOrderOf (r i)))
    (fun i => magnitude_error_all N c e δ hδ h6 (addOrderOf (r i)))
    (resonant_product_error N c e m (δ^6) hnoise r hr)

private theorem sieveSeq_eq_of_weights (N : ℕ) (c e : ℕ → ℝ)
    (he : ∀ d ∈ Finset.Icc 1 N, e d = c d) (n : ℕ) :
    sieveSeq N e n = sieveSeq N c n := by
  unfold sieveSeq
  exact Finset.sum_congr rfl fun d hd => he d (Finset.mem_filter.mp hd).1

/-- Only one natural shift is used, even when the small discarded modes change support. -/
theorem exists_physical_translate_error (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h5 : ∀ h : Fin 5 → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ δ^6)
    (h6 : ∀ h : Fin 6 → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ δ^6) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n+t)| ≤
      3 * (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ := by
  let c' := thresholdSourceWeights N c δ
  let e' := thresholdTargetWeights N c e δ
  have h5' := threshold_moments_eq N c e δ hδ hδ1 h6 5 (Or.inl rfl) h5
  have h6' := threshold_moments_eq N c e δ hδ hδ1 h6 6 (Or.inr rfl) h6
  have hshift : ∃ t : ℕ, ∀ n, sieveSeq N e' n = sieveSeq N c' (n+t) := by
    rcases coefficients_eq_or_companion_of_moments N c' e' h5' h6' with he | he
    · exact ⟨0, fun n => by simpa using sieveSeq_eq_of_weights N c' e' he n⟩
    · exact ⟨canonicalShift N c', fun n =>
        (sieveSeq_eq_of_weights N (companion N c') e' he n).trans (sieveSeq_companion N c' n)⟩
  obtain ⟨t, ht⟩ := hshift
  have hsource (n : ℕ) : |sieveSeq N c n - sieveSeq N c' n| ≤
      (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ := by
    apply sieveSeq_error_le_totient_sum
    intro q _
    change |selbergMultiplesCoord N c q -
      selbergMultiplesCoord N (thresholdSourceWeights N c δ) q| ≤ δ
    rw [coordinate_thresholdSource N c δ hδ]
    exact Threshold.source_error δ _ hδ
  have htarget (n : ℕ) : |sieveSeq N e n - sieveSeq N e' n| ≤
      (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * (2*δ) := by
    apply sieveSeq_error_le_totient_sum
    intro q hq
    change |selbergMultiplesCoord N e q -
      selbergMultiplesCoord N (thresholdTargetWeights N c e δ) q| ≤ 2*δ
    rw [coordinate_thresholdTarget N c e δ hδ]
    exact Threshold.target_error δ _ _ hδ (coordinate_magnitude_error N c e δ hδ h6 q hq)
  refine ⟨t, fun n => ?_⟩
  calc
    _ ≤ |sieveSeq N e n - sieveSeq N e' n| +
        |sieveSeq N e' n - sieveSeq N c (n+t)| := abs_sub_le _ _ _
    _ ≤ (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * (2*δ) +
        (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * δ := by
      apply add_le_add (htarget n)
      rw [ht, abs_sub_comm]
      exact hsource (n+t)
    _ = _ := by ring

/-- Raw error ε has a uniform sixth-root modulus, with no amplitude or support-gap assumption. -/
theorem exists_physical_translate_holder (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h5 : ∀ h : Fin 5 → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ ε)
    (h6 : ∀ h : Fin 6 → ℕ,
      |translatedMoment N c h - translatedMoment N e h| ≤ ε) :
    ∃ t : ℕ, ∀ n : ℕ, |sieveSeq N e n - sieveSeq N c (n+t)| ≤
      3 * (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) * ε^(1/6 : ℝ) := by
  have hp : (ε^(1/6 : ℝ))^6 = ε := by
    simpa only [Nat.cast_ofNat, one_div] using
      (Real.rpow_inv_natCast_pow (n := 6) hε (by norm_num))
  apply exists_physical_translate_error N c e (ε^(1/6 : ℝ))
    (Real.rpow_nonneg hε _) (Real.rpow_le_one hε hε1 (by norm_num))
  · simpa only [hp] using h5
  · simpa only [hp] using h6

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
