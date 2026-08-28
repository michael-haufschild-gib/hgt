import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketNatOrder
import GaloisForLFunctions.RHTower.Sieve.MaynardUpperPhaseHandoff

open Complex MeasureTheory Set
open Filter ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- Buffered transition exponent between the physical-slice receiver and paired-kernel decay. -/
def routeTPairedKernelBufferedMu : ℝ :=
  4 / (1 + 3 * maynardLongGlobalAmplitudeDeficit / 2)

/-- Fixed reserve retained by the physical-slice receiver at the buffered transition. -/
def routeTPhysicalSliceBufferedReserve : ℝ :=
  2 - routeTPairedKernelBufferedMu * (1 - routeTGapMomentNu)

/-- Fixed decay exponent acquired by the paired normalized Mellin kernel at the buffer. -/
def routeTPairedKernelDecayReserve : ℝ :=
  routeTPairedKernelBufferedMu * (1 - routeTPhysicalSliceHandoffTheta) - 1

/-- Canonical relative reference width used by the cancellation-preserving paired receiver. -/
def routeTPairedKernelReferenceRelativeWidth (x : ℝ) : ℝ :=
  4 * (2 * x) ^ routeTPhysicalSliceHandoffTheta / x

theorem routeTPhysicalSliceBufferedReserve_pos :
    0 < routeTPhysicalSliceBufferedReserve := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 0 < 1 + 3 * maynardLongGlobalAmplitudeDeficit / 2 := by positivity
  rw [routeTPhysicalSliceBufferedReserve, routeTPairedKernelBufferedMu,
    routeTGapMomentNu]
  field_simp
  nlinarith

theorem routeTPairedKernelDecayReserve_pos :
    0 < routeTPairedKernelDecayReserve := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 0 < 1 + 3 * maynardLongGlobalAmplitudeDeficit / 2 := by positivity
  rw [routeTPairedKernelDecayReserve, routeTPairedKernelBufferedMu,
    routeTPhysicalSliceHandoffTheta]
  field_simp
  nlinarith

/-- Every exponent lies in a receiver range with a fixed power reserve: physical-slice reserve
below the buffer, or paired-kernel decay above it. -/
theorem routeT_buffered_physicalSlice_or_pairedKernel_decay (mu : ℝ) :
    mu * (1 - routeTGapMomentNu) + routeTPhysicalSliceBufferedReserve ≤ 2 ∨
      routeTPairedKernelDecayReserve ≤
        mu * (1 - routeTPhysicalSliceHandoffTheta) - 1 := by
  by_cases hmu : mu ≤ routeTPairedKernelBufferedMu
  · left
    have hfactor : 0 ≤ 1 - routeTGapMomentNu := by
      linarith [routeTGapMomentNu_lt_half]
    have hmul := mul_le_mul_of_nonneg_right hmu hfactor
    rw [routeTPhysicalSliceBufferedReserve]
    linarith
  · right
    have hfactor : 0 ≤ 1 - routeTPhysicalSliceHandoffTheta := by
      linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_ge hmu) hfactor
    rw [routeTPairedKernelDecayReserve]
    linarith

/-- The canonical common reference has exactly the height-matched shape consumed by the buffered
paired-kernel estimate. -/
theorem routeT_commonReferenceRelativeWidth_heightMatched
    {T mu : ℝ} (hT : 0 < T) :
    4 * (2 * T ^ mu) ^ routeTPhysicalSliceHandoffTheta / T ^ mu =
      (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)) := by
  have hTpow : 0 ≤ T ^ mu := Real.rpow_nonneg hT.le _
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTpow,
    ← Real.rpow_mul hT.le]
  calc
    4 * (2 ^ routeTPhysicalSliceHandoffTheta *
          T ^ (mu * routeTPhysicalSliceHandoffTheta)) / T ^ mu =
        (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          (T ^ (mu * routeTPhysicalSliceHandoffTheta) / T ^ mu) := by ring
    _ = (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        T ^ (mu * routeTPhysicalSliceHandoffTheta - mu) := by
      rw [Real.rpow_sub hT]
    _ = (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)) := by
      congr 2
      ring

/-- The fixed buffered paired-kernel scale condition is automatic at large height. -/
theorem eventually_routeTPairedKernelBufferedScaleReady :
    ∀ᶠ T : ℝ in Filter.atTop,
      16 * 2 ^ routeTPhysicalSliceHandoffTheta *
        T ^ (-routeTPairedKernelDecayReserve) ≤ 1 := by
  have hdecay :=
    (tendsto_rpow_neg_atTop routeTPairedKernelDecayReserve_pos).const_mul
      (16 * 2 ^ routeTPhysicalSliceHandoffTheta)
  have hzero :
      (16 * 2 ^ routeTPhysicalSliceHandoffTheta) * 0 = (0 : ℝ) := by ring
  rw [hzero] at hdecay
  have hlt := Filter.Tendsto.eventually_lt hdecay
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)) zero_lt_one
  filter_upwards [hlt] with T hT
  exact hT.le

/-- On the line `Re s = 1`, physical scaling cancels out of the paired-kernel low-band bound. -/
theorem norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_relative
    {lambda H R y : ℝ} (hlambda : 0 < lambda) (hH : 0 < H) (hR : 0 < R)
    (hHR : H ≤ R) (hsmall : |y| * (2 * R) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin lambda (lambda * R)
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin lambda (lambda * H)
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      8 * |y| * R := by
  let s : ℂ := (1 : ℂ) + (y : ℝ) * Complex.I
  have hsre : 0 < s.re := by simp [s]
  have hsnorm : ‖s - 1‖ = |y| := by simp [s]
  have hphysicalH : 0 < lambda * H := mul_pos hlambda hH
  have hphysicalR : 0 < lambda * R := mul_pos hlambda hR
  have hphysicalOrder : lambda * H ≤ lambda * R :=
    mul_le_mul_of_nonneg_left hHR hlambda.le
  have hsmall' : ‖s - 1‖ * (2 * (lambda * R) / lambda) ≤ 1 := by
    rw [hsnorm]
    convert hsmall using 1 <;> field_simp [hlambda.ne']
  have hk := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
    hlambda hphysicalH hphysicalR hphysicalOrder hsre hsmall'
  rw [show s.re = 1 by simp [s], sub_self, Real.rpow_zero, mul_one, hsnorm] at hk
  convert hk using 1 <;> field_simp [hlambda.ne']

/-- Above the buffered handoff, the common-reference paired kernel has a fixed negative-power
gain on a complete dyadic ordinate shell. -/
theorem norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_bufferedPower
    {T mu lambda H R y : ℝ}
    (hT : 1 < T) (hmu : routeTPairedKernelBufferedMu ≤ mu)
    (hlambda : 0 < lambda) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hRshape : R =
      (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)))
    (hy : |y| ≤ 2 * T)
    (hready : 16 * 2 ^ routeTPhysicalSliceHandoffTheta *
        T ^ (-routeTPairedKernelDecayReserve) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin lambda (lambda * R)
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin lambda (lambda * H)
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      64 * 2 ^ routeTPhysicalSliceHandoffTheta *
        T ^ (-routeTPairedKernelDecayReserve) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hfactor : 0 ≤ 1 - routeTPhysicalSliceHandoffTheta := by
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hmul := mul_le_mul_of_nonneg_right hmu hfactor
  have hexp :
      1 + mu * (routeTPhysicalSliceHandoffTheta - 1) ≤
        -routeTPairedKernelDecayReserve := by
    rw [routeTPairedKernelDecayReserve]
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
  have hcollapse :
      T * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)) =
        T ^ (1 + mu * (routeTPhysicalSliceHandoffTheta - 1)) := by
    calc
      T * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)) =
          T ^ (1 : ℝ) * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)) := by
            rw [Real.rpow_one]
      _ = T ^ (1 + mu * (routeTPhysicalSliceHandoffTheta - 1)) :=
        (Real.rpow_add hT0 _ _).symm
  have hscale :
      T * R ≤
        (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          T ^ (-routeTPairedKernelDecayReserve) := by
    rw [hRshape]
    calc
      T * ((4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1))) =
          (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
            (T * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1))) := by ring
      _ = (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          T ^ (1 + mu * (routeTPhysicalSliceHandoffTheta - 1)) := by rw [hcollapse]
      _ ≤ (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          T ^ (-routeTPairedKernelDecayReserve) := by gcongr
  have hsmall : |y| * (2 * R) ≤ 1 := by
    calc
      |y| * (2 * R) ≤ (2 * T) * (2 * R) := by
        gcongr
      _ = 4 * (T * R) := by ring
      _ ≤ 16 * 2 ^ routeTPhysicalSliceHandoffTheta *
          T ^ (-routeTPairedKernelDecayReserve) := by
        nlinarith
      _ ≤ 1 := hready
  have hk := norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_relative
    hlambda hH hR hHR hsmall
  calc
    _ ≤ 8 * |y| * R := hk
    _ ≤ 8 * (2 * T) * R := by gcongr
    _ = 16 * (T * R) := by ring
    _ ≤ 64 * 2 ^ routeTPhysicalSliceHandoffTheta *
        T ^ (-routeTPairedKernelDecayReserve) := by nlinarith

/-- **Canonical buffered paired-kernel decay.**  Eventually, every dyadic ordinate shell above
the buffered handoff retains one fixed negative power in the actual common-reference kernel
difference, uniformly over the target width and physical base. -/
theorem eventually_norm_routeTPairedKernelReference_sub_target_le_bufferedPower :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ mu lambda H y : ℝ,
        routeTPairedKernelBufferedMu ≤ mu →
        0 < lambda → 0 < H →
        H ≤ routeTPairedKernelReferenceRelativeWidth (T ^ mu) →
        T ≤ y → y ≤ 2 * T →
        ‖routeTNormalizedSmoothWindowMellin lambda
              (lambda * routeTPairedKernelReferenceRelativeWidth (T ^ mu))
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin lambda (lambda * H)
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
          64 * 2 ^ routeTPhysicalSliceHandoffTheta *
            T ^ (-routeTPairedKernelDecayReserve) := by
  filter_upwards [eventually_routeTPairedKernelBufferedScaleReady,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hready hT
  intro mu lambda H y hmu hlambda hH hHR hylo hyhi
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hR : 0 < routeTPairedKernelReferenceRelativeWidth (T ^ mu) := by
    unfold routeTPairedKernelReferenceRelativeWidth
    positivity
  have hy0 : 0 ≤ y := by linarith
  have hyabs : |y| ≤ 2 * T := by
    rw [abs_of_nonneg hy0]
    exact hyhi
  apply norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_bufferedPower
    hT hmu hlambda hH hR hHR
  · unfold routeTPairedKernelReferenceRelativeWidth
    exact routeT_commonReferenceRelativeWidth_heightMatched hT0
  · exact hyabs
  · exact hready

end

end RHTower.Sieve
