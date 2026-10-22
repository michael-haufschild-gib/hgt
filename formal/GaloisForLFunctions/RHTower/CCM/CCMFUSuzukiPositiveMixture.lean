import GaloisForLFunctions.RHTower.CCM.CCMFUCentralRectangularAffineWeld

/-!
# CCM-FU as a positive marked Suzuki-profile average

This module removes the final affine wall memory from the central Xi-screw codiagonal formulation
of CCM-FU. The marked rectangular measure has an exact first moment, so its affine memory is
uniformly bounded. The RH-bearing datum is therefore uniform boundedness of one positive marked
average of Suzuki's literal signed profile `suzukiPsi`, with all positive/negative cancellation
preserved inside the readout.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- First marked moment of the FU rectangular aperture measure. -/
theorem integral_rectangularMixDensity_mul_sub_add_endpoint_eq
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ t in b..H,
        ccmThirdGradeCesaroRectangularMixDensity H t * (t - b)) +
      (32 / H ^ (4 : ℕ)) * (H - b) =
        32 / b ^ (3 : ℕ) - 32 / (H * b ^ (2 : ℕ)) := by
  have hH : 0 < H := hb.trans_le hbH
  let P : ℝ → ℝ := fun t =>
    (-128 * (1 / t ^ (3 : ℕ)) + 96 * b * (1 / t ^ (4 : ℕ))) +
      ((96 / H) * (1 / t ^ (2 : ℕ)) - (64 * b / H) * (1 / t ^ (3 : ℕ)))
  have hP : ∀ t ∈ Set.uIcc b H,
      HasDerivAt P
        (ccmThirdGradeCesaroRectangularMixDensity H t * (t - b)) t := by
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    have h2raw := (hasDerivAt_const (x := t) (c := (1 : ℝ))).div
      ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
    simp only [Pi.pow_apply, id_eq] at h2raw
    have h2 : HasDerivAt (fun x : ℝ => 1 / x ^ (2 : ℕ)) (-2 / t ^ (3 : ℕ)) t := by
      apply h2raw.congr_deriv
      field_simp [ht0]
      ring
    have h3raw := (hasDerivAt_const (x := t) (c := (1 : ℝ))).div
      ((hasDerivAt_id t).pow 3) (pow_ne_zero 3 ht0)
    simp only [Pi.pow_apply, id_eq] at h3raw
    have h3 : HasDerivAt (fun x : ℝ => 1 / x ^ (3 : ℕ)) (-3 / t ^ (4 : ℕ)) t := by
      apply h3raw.congr_deriv
      field_simp [ht0]
      ring
    have h4raw := (hasDerivAt_const (x := t) (c := (1 : ℝ))).div
      ((hasDerivAt_id t).pow 4) (pow_ne_zero 4 ht0)
    simp only [Pi.pow_apply, id_eq] at h4raw
    have h4 : HasDerivAt (fun x : ℝ => 1 / x ^ (4 : ℕ)) (-4 / t ^ (5 : ℕ)) t := by
      apply h4raw.congr_deriv
      field_simp [ht0]
      ring
    have hraw := ((h3.const_mul (-128)).add (h4.const_mul (96 * b))).add
      ((h2.const_mul (96 / H)).sub (h3.const_mul (64 * b / H)))
    dsimp only [P]
    apply hraw.congr_deriv
    unfold ccmThirdGradeCesaroRectangularMixDensity
    field_simp [ht0, hH.ne']
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => ccmThirdGradeCesaroRectangularMixDensity H t * (t - b))
      volume b H := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hbH] at ht
      exact (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact (((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).mul
        (continuousAt_id.sub continuousAt_const)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP hint]
  dsimp only [P]
  field_simp [hb.ne', hH.ne']
  ring

/-- Positive marked aperture average of Suzuki's literal signed source profile. Positive and
negative values of `suzukiPsi` remain coupled inside one readout. -/
def ccmFUCentralXiScrewPositiveMixture (b H : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t) +
  (32 / H ^ (4 : ℕ)) * suzukiPsi H

/-- Explicit affine wall memory removed from the Xi-screw codiagonal mixture. -/
def ccmFUCentralXiScrewAffineMemory (b H : ℝ) : ℝ :=
  suzukiPsi b * ccmGuinandWeilThirdGradeCesaroErrorKernel H b +
    ccmGuinandWeilXiScrewRightSlope b *
      (32 / b ^ (3 : ℕ) - 32 / (H * b ^ (2 : ℕ)))

/-- The codiagonal reporter differs from the positive marked Suzuki-profile average by one fully
explicit affine wall memory. -/
theorem ccmFUCentralXiScrewCodiagonalMixture_eq_positiveMixture_sub_affineMemory
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmFUCentralXiScrewCodiagonalMixture b H =
      ccmFUCentralXiScrewPositiveMixture b H -
        ccmFUCentralXiScrewAffineMemory b H := by
  have hH : 0 < H := hb.trans_le hbH
  have hdensityCont : ContinuousOn
      (ccmThirdGradeCesaroRectangularMixDensity H) (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hρ : IntervalIntegrable
      (ccmThirdGradeCesaroRectangularMixDensity H) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont
  have hρψ : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t)
      volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont.mul continuous_suzukiPsi.continuousOn
  have hρlin : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * (t - b))
      volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont.mul (continuousOn_id.sub continuousOn_const)
  have hbulk :
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmGuinandWeilXiScrewCodiagonal b t) =
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t) -
        suzukiPsi b * (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t) -
        ccmGuinandWeilXiScrewRightSlope b *
          (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * (t - b)) := by
    calc
      _ = ∫ t in b..H,
          (ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t -
            suzukiPsi b * ccmThirdGradeCesaroRectangularMixDensity H t) -
          ccmGuinandWeilXiScrewRightSlope b *
            (ccmThirdGradeCesaroRectangularMixDensity H t * (t - b)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmGuinandWeilXiScrewCodiagonal b t = _
        unfold ccmGuinandWeilXiScrewCodiagonal
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
              (hρψ.sub (hρ.const_mul (suzukiPsi b)))
              (hρlin.const_mul (ccmGuinandWeilXiScrewRightSlope b)),
          intervalIntegral.integral_sub hρψ (hρ.const_mul (suzukiPsi b)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hmass := integral_rectangularMixDensity_add_endpoint_eq_errorKernel hb hbH
  have hfirst := integral_rectangularMixDensity_mul_sub_add_endpoint_eq hb hbH
  unfold ccmFUCentralXiScrewCodiagonalMixture
    ccmFUCentralXiScrewPositiveMixture ccmFUCentralXiScrewAffineMemory
  rw [hbulk]
  rw [ccmGuinandWeilXiScrewCodiagonal]
  linear_combination -(suzukiPsi b) * hmass -
    ccmGuinandWeilXiScrewRightSlope b * hfirst

/-- The affine Suzuki wall memory is uniformly bounded in the moving upper wall. -/
theorem exists_nonnegative_uniform_bound_ccmFUCentralXiScrewAffineMemory
    {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
      |ccmFUCentralXiScrewAffineMemory b H| ≤ C := by
  let C : ℝ :=
    |suzukiPsi b| * (96 / b ^ (4 : ℕ)) +
      |ccmGuinandWeilXiScrewRightSlope b| * (32 / b ^ (3 : ℕ))
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    positivity
  · intro H hbH
    have hbHle : b ≤ H := hbH.le
    have hH : 0 < H := hb.trans hbH
    have hk :=
      ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds hb hbHle
        (show b ∈ Set.Icc b H from ⟨le_rfl, hbHle⟩)
    have hk0 : 0 ≤ ccmGuinandWeilThirdGradeCesaroErrorKernel H b := by
      exact (by positivity : 0 ≤ 32 / b ^ (4 : ℕ)) |>.trans hk.1
    let m : ℝ := 32 / b ^ (3 : ℕ) - 32 / (H * b ^ (2 : ℕ))
    have hm0 : 0 ≤ m := by
      dsimp only [m]
      field_simp [hb.ne', hH.ne']
      nlinarith
    have hmle : m ≤ 32 / b ^ (3 : ℕ) := by
      dsimp only [m]
      have hsub : 0 ≤ 32 / (H * b ^ (2 : ℕ)) := by positivity
      linarith
    unfold ccmFUCentralXiScrewAffineMemory
    change |suzukiPsi b * ccmGuinandWeilThirdGradeCesaroErrorKernel H b +
      ccmGuinandWeilXiScrewRightSlope b * m| ≤ C
    calc
      _ ≤ |suzukiPsi b * ccmGuinandWeilThirdGradeCesaroErrorKernel H b| +
          |ccmGuinandWeilXiScrewRightSlope b * m| := abs_add_le _ _
      _ = |suzukiPsi b| * ccmGuinandWeilThirdGradeCesaroErrorKernel H b +
          |ccmGuinandWeilXiScrewRightSlope b| * m := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hm0]
      _ ≤ |suzukiPsi b| * (96 / b ^ (4 : ℕ)) +
          |ccmGuinandWeilXiScrewRightSlope b| * (32 / b ^ (3 : ℕ)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hk.2 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hmle (abs_nonneg _))
      _ = C := by rfl

/-- Uniform boundedness of the positive marked Suzuki-profile average. -/
def CCMFUCentralXiScrewPositiveMixtureBound (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
    |ccmFUCentralXiScrewPositiveMixture b H| ≤ C

/-- **Ultimate positive-kernel Suzuki form of CCM-FU.** The RH-bearing codiagonal-mixture bound is
equivalent to boundedness of a positive marked average of the literal signed Suzuki profile. All
Gamma and affine wall terms are unconditionally bounded; positive/negative profile regions remain
coupled. -/
theorem ccmFUCentralXiScrewCodiagonalMixtureBound_iff_positiveMixtureBound
    {b : ℝ} (hb : 0 < b) :
    CCMFUCentralXiScrewCodiagonalMixtureBound b ↔
      CCMFUCentralXiScrewPositiveMixtureBound b := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_nonnegative_uniform_bound_ccmFUCentralXiScrewAffineMemory hb
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + A, add_nonneg hC0 hA0, ?_⟩
    intro H hbH
    have heq :=
      ccmFUCentralXiScrewCodiagonalMixture_eq_positiveMixture_sub_affineMemory
        hb hbH.le
    have hrecover :
        ccmFUCentralXiScrewPositiveMixture b H =
          ccmFUCentralXiScrewCodiagonalMixture b H +
            ccmFUCentralXiScrewAffineMemory b H := by
      linarith
    rw [hrecover]
    exact (abs_add_le _ _).trans (add_le_add (hC H hbH) (hA H hbH))
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + A, add_nonneg hC0 hA0, ?_⟩
    intro H hbH
    rw [ccmFUCentralXiScrewCodiagonalMixture_eq_positiveMixture_sub_affineMemory
      hb hbH.le]
    exact (abs_sub _ _).trans (add_le_add (hC H hbH) (hA H hbH))

/-- **Direct CCM-FU compression.**  The anchored triangular prime--polar moment and the positive
Suzuki-profile mixture have the same uniform-boundedness burden at every positive lower wall. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_positiveMixtureBound
    {b : ℝ} (hb : 0 < b) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b ↔
      CCMFUCentralXiScrewPositiveMixtureBound b :=
  ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_xiScrewCodiagonalMixtureBound hb |>.trans
    (ccmFUCentralXiScrewCodiagonalMixtureBound_iff_positiveMixtureBound hb)

/-- **Exact positive-mixture/RH absorption law.**  Uniform boundedness of the marked Suzuki-profile
average is unchanged by adjoining RH. -/
theorem ccmFUCentralXiScrewPositiveMixtureBound_iff_and_riemannHypothesis
    {b : ℝ} (hb : 0 < b) :
    CCMFUCentralXiScrewPositiveMixtureBound b ↔
      CCMFUCentralXiScrewPositiveMixtureBound b ∧ RiemannHypothesis := by
  constructor
  · intro hbound
    refine ⟨hbound, ?_⟩
    have hcodiagonal :=
      (ccmFUCentralXiScrewCodiagonalMixtureBound_iff_positiveMixtureBound hb).2 hbound
    exact
      (ccmFUCentralXiScrewCodiagonalMixtureBound_iff_and_riemannHypothesis hb).mp
        hcodiagonal |>.2
  · exact And.left

end GaloisForLFunctions.RHTower
