import GaloisForLFunctions.RHTower.WeilLogShiftRawOrder
import GaloisForLFunctions.RHTower.WeilLogShiftLawCovariance
import GaloisForLFunctions.RHTower.WeilLogShiftConvexRightSupport

/-! The centered raw correction law lies below the centered index law in finite convex order. -/

open MeasureTheory GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalRaw_convex_sum_le (r k : ℕ)
    (φ : {f : ℝ → ℝ // ConvexOn ℝ Set.univ f}) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i * φ.val (finiteWeilCanonicalRawCorrectionValue r k i)) ≤
      ∑ i, finiteWeilCanonicalEdgeMass r k i * φ.val (finiteWeilCanonicalRawIndexValue r k i) := by
  let d : Fin (r + 1) →o ℝ :=
    ⟨fun i => derivWithin φ.val (Set.Ioi (finiteWeilCanonicalRawCorrectionValue r k i))
      (finiteWeilCanonicalRawCorrectionValue r k i),
      fun i j hij => finiteWeilConvex_rightDeriv_monotone φ
        (finiteWeilCanonicalRawCorrectionValue_monotone r k hij)⟩
  let e : Fin (r + 1) →o ℝ :=
    ⟨fun i => finiteWeilCanonicalRawIndexValue r k i - finiteWeilCanonicalRawCorrectionValue r k i,
      finiteWeilCanonicalRawDefect_monotone r k⟩
  have he : (finiteWeilCanonicalEdgeLaw r k).Ex e = 0 :=
    finiteWeilCanonicalRawDefect_mean_zero r k
  have hc := finiteWeilLaw_monotone_covariance_nonneg (finiteWeilCanonicalEdgeLaw r k) d e
  rw [he, mul_zero] at hc
  change 0 ≤ ∑ i, finiteWeilCanonicalEdgeMass r k i *
    (derivWithin φ.val (Set.Ioi (finiteWeilCanonicalRawCorrectionValue r k i))
      (finiteWeilCanonicalRawCorrectionValue r k i) *
      (finiteWeilCanonicalRawIndexValue r k i - finiteWeilCanonicalRawCorrectionValue r k i)) at hc
  have hs : (∑ i, finiteWeilCanonicalEdgeMass r k i *
      (derivWithin φ.val (Set.Ioi (finiteWeilCanonicalRawCorrectionValue r k i))
        (finiteWeilCanonicalRawCorrectionValue r k i) *
        (finiteWeilCanonicalRawIndexValue r k i - finiteWeilCanonicalRawCorrectionValue r k i))) ≤
      ∑ i, finiteWeilCanonicalEdgeMass r k i *
        (φ.val (finiteWeilCanonicalRawIndexValue r k i) - φ.val (finiteWeilCanonicalRawCorrectionValue r k i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (finiteWeilConvex_right_support φ _ _)
      (finiteWeilCanonicalEdgeMass_pos r k i).le
  have h := hc.trans hs
  simpa only [mul_sub, Finset.sum_sub_distrib, sub_nonneg] using h

theorem finiteWeilCanonicalRaw_convex_integral_le (r k : ℕ)
    (φ : {f : ℝ → ℝ // ConvexOn ℝ Set.univ f}) :
    (∫ x, φ.val x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)) ≤
      ∫ x, φ.val x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ) := by
  rw [finiteWeilCanonicalRawCorrectionLaw, finiteWeilCanonicalRawIndexLaw,
    finiteWeilCanonicalObservableLaw_integral_real, finiteWeilCanonicalObservableLaw_integral_real]
  exact finiteWeilCanonicalRaw_convex_sum_le r k φ

end RHTower
