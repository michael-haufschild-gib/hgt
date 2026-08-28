import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketNatOrder
import GaloisForLFunctions.RHTower.Sieve.MaynardUpperPhaseHandoff
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSpatialL4

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

/-- Exact fixed coefficient of the physical block-base reference after shell height matching. -/
def routeTPairedKernelCommonReferenceCoefficient : ℝ :=
  16 * 2 ^ (-routeTPhysicalSliceHandoffTheta)

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

/-- The actual common reference is calibrated at one quarter of the height-matched support. -/
theorem routeT_commonBlockReferenceRelativeWidth_heightMatched
    {T mu : ℝ} (hT : 0 < T) :
    routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4) =
      routeTPairedKernelCommonReferenceCoefficient *
        T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)) := by
  have hY : 0 < T ^ mu := Real.rpow_pos_of_pos hT _
  have hY4 : 0 < T ^ mu / 4 := div_pos hY (by norm_num)
  rw [routeTPairedKernelReferenceRelativeWidth,
    show 2 * (T ^ mu / 4) = T ^ mu / 2 by ring,
    Real.div_rpow hY.le (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul hT.le]
  rw [routeTPairedKernelCommonReferenceCoefficient]
  have htwo : 0 < (2 : ℝ) := by norm_num
  calc
    4 * (T ^ (mu * routeTPhysicalSliceHandoffTheta) /
          2 ^ routeTPhysicalSliceHandoffTheta) / (T ^ mu / 4) =
        (16 * (2 ^ routeTPhysicalSliceHandoffTheta)⁻¹) *
          (T ^ (mu * routeTPhysicalSliceHandoffTheta) / T ^ mu) := by
      field_simp [hY.ne', (Real.rpow_pos_of_pos htwo _).ne']
      ring
    _ = (16 * 2 ^ (-routeTPhysicalSliceHandoffTheta)) *
        T ^ (mu * routeTPhysicalSliceHandoffTheta - mu) := by
      rw [Real.rpow_neg htwo.le, Real.rpow_sub hT]
    _ = (16 * 2 ^ (-routeTPhysicalSliceHandoffTheta)) *
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

/-- The scale condition for the actual block-base common reference is eventually automatic. -/
theorem eventually_routeTCommonBlockReferenceBufferedScaleReady :
    ∀ᶠ T : ℝ in Filter.atTop,
      4 * routeTPairedKernelCommonReferenceCoefficient *
        T ^ (-routeTPairedKernelDecayReserve) ≤ 1 := by
  have hdecay :=
    (tendsto_rpow_neg_atTop routeTPairedKernelDecayReserve_pos).const_mul
      (4 * routeTPairedKernelCommonReferenceCoefficient)
  have hzero :
      (4 * routeTPairedKernelCommonReferenceCoefficient) * 0 = (0 : ℝ) := by ring
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
    convert hsmall using 1
    all_goals field_simp [hlambda.ne']
  have hk := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
    hlambda hphysicalH hphysicalR hphysicalOrder hsre hsmall'
  rw [show s.re = 1 by simp [s], sub_self, Real.rpow_zero, mul_one, hsnorm] at hk
  convert hk using 1
  all_goals field_simp [hlambda.ne']

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

/-- Coefficient-parametric form of the buffered paired-kernel estimate. -/
theorem norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_bufferedPower_of_shape
    {T mu lambda H R C y : ℝ}
    (hT : 1 < T) (hmu : routeTPairedKernelBufferedMu ≤ mu)
    (hlambda : 0 < lambda) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hC : 0 ≤ C)
    (hRshape : R = C * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1)))
    (hy : |y| ≤ 2 * T)
    (hready : 4 * C * T ^ (-routeTPairedKernelDecayReserve) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin lambda (lambda * R)
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin lambda (lambda * H)
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      16 * C * T ^ (-routeTPairedKernelDecayReserve) := by
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
  have hscale : T * R ≤ C * T ^ (-routeTPairedKernelDecayReserve) := by
    rw [hRshape]
    calc
      T * (C * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1))) =
          C * (T * T ^ (mu * (routeTPhysicalSliceHandoffTheta - 1))) := by ring
      _ = C * T ^ (1 + mu * (routeTPhysicalSliceHandoffTheta - 1)) := by
        rw [hcollapse]
      _ ≤ C * T ^ (-routeTPairedKernelDecayReserve) := by gcongr
  have hsmall : |y| * (2 * R) ≤ 1 := by
    calc
      |y| * (2 * R) ≤ (2 * T) * (2 * R) := by gcongr
      _ = 4 * (T * R) := by ring
      _ ≤ 4 * C * T ^ (-routeTPairedKernelDecayReserve) := by nlinarith
      _ ≤ 1 := hready
  have hk := norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_relative
    hlambda hH hR hHR hsmall
  calc
    _ ≤ 8 * |y| * R := hk
    _ ≤ 8 * (2 * T) * R := by gcongr
    _ = 16 * (T * R) := by ring
    _ ≤ 16 * C * T ^ (-routeTPairedKernelDecayReserve) := by nlinarith

/-- The actual common block-base reference has a fixed paired-kernel power gain. -/
theorem norm_routeTCommonBlockReference_sub_target_le_bufferedPower
    {T mu lambda H y : ℝ}
    (hT : 1 < T) (hmu : routeTPairedKernelBufferedMu ≤ mu)
    (hlambda : 0 < lambda) (hH : 0 < H)
    (hHR : H ≤ routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4))
    (hy : |y| ≤ 2 * T)
    (hready : 4 * routeTPairedKernelCommonReferenceCoefficient *
      T ^ (-routeTPairedKernelDecayReserve) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin lambda
          (lambda * routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4))
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin lambda (lambda * H)
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      16 * routeTPairedKernelCommonReferenceCoefficient *
        T ^ (-routeTPairedKernelDecayReserve) := by
  have hR : 0 < routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4) := by
    unfold routeTPairedKernelReferenceRelativeWidth
    positivity
  have hC : 0 ≤ routeTPairedKernelCommonReferenceCoefficient := by
    unfold routeTPairedKernelCommonReferenceCoefficient
    positivity
  exact norm_routeTNormalizedSmoothWindowMellin_physical_sub_le_bufferedPower_of_shape
    hT hmu hlambda hH hR hHR hC
      (routeT_commonBlockReferenceRelativeWidth_heightMatched
        (zero_lt_one.trans hT)) hy hready

/-- **Actual common-block buffered decay.**  Eventually, every dyadic ordinate shell above the
buffered handoff retains one fixed negative power for the common reference calibrated at one
quarter of the height-matched support. -/
theorem eventually_norm_routeTCommonBlockReference_sub_target_le_bufferedPower :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ mu lambda H y : ℝ,
        routeTPairedKernelBufferedMu ≤ mu →
        0 < lambda → 0 < H →
        H ≤ routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4) →
        T ≤ y → y ≤ 2 * T →
        ‖routeTNormalizedSmoothWindowMellin lambda
              (lambda * routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4))
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin lambda (lambda * H)
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
          16 * routeTPairedKernelCommonReferenceCoefficient *
            T ^ (-routeTPairedKernelDecayReserve) := by
  filter_upwards [eventually_routeTCommonBlockReferenceBufferedScaleReady,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hready hT
  intro mu lambda H y hmu hlambda hH hHR hylo hyhi
  have hy0 : 0 ≤ y := by linarith
  have hyabs : |y| ≤ 2 * T := by
    rw [abs_of_nonneg hy0]
    exact hyhi
  exact norm_routeTCommonBlockReference_sub_target_le_bufferedPower
    hT hmu hlambda hH hHR hyabs hready

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

/-- Arbitrary-order far-tail decay for a non-comparable paired kernel.  Unlike the historical
adjacent-width estimate, this needs only `H ≤ R`: bounding both endpoints by the narrower target
costs a fixed factor two and preserves the paired object for the finite annulus. -/
theorem exists_integral_norm_fixedSource_mul_noncomparablePairedKernel_natOrder_tail_le
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {M N H R U : ℝ},
        1 ≤ X → 0 < M → 1 ≤ N → 0 < H → 0 < R →
        H ≤ R → R ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
          ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
          heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
            (2 * Cj * (N / H) ^ (j + 1) * U ^ (-(j : ℝ))) := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_routeTNormalizedSmoothWindowMellin_one_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro L X k T0 t M N H R U hX hM hN hH hR hHR hRN hU
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let KR : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let KH : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N H
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  have hA : ∀ y : ℝ, ‖A y‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hA 0)
  have hKRint := integrable_routeTNormalizedSmoothWindowMellin_one
    (zero_lt_one.trans_le hN) hR
  have hHint : H ≤ N := hHR.trans hRN
  have hKHint := integrable_routeTNormalizedSmoothWindowMellin_one
    (zero_lt_one.trans_le hN) hH
  have hKint : Integrable (fun y => KR y - KH y) := by
    change Integrable (KR - KH)
    exact hKRint.sub hKHint
  have hAcont : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hprod : Integrable (fun y => ‖A y * (KR y - KH y)‖) := by
    exact (hKint.bdd_mul hAcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hA)).norm
  have hmajor : Integrable (fun y => P * (‖KR y‖ + ‖KH y‖)) := by
    exact (hKRint.norm.add hKHint.norm).const_mul P
  have hmono : (∫ y in tail, ‖A y * (KR y - KH y)‖) ≤
      ∫ y in tail, P * (‖KR y‖ + ‖KH y‖) := by
    apply setIntegral_mono_on hprod.integrableOn hmajor.integrableOn
      (measurableSet_le measurable_const continuous_abs.measurable)
    intro y _hy
    rw [norm_mul]
    exact mul_le_mul (hA y) (norm_sub_le _ _) (norm_nonneg _) hP
  have hscale : (∫ y in tail, P * (‖KR y‖ + ‖KH y‖)) =
      P * ((∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hKRint.norm.integrableOn hKHint.norm.integrableOn]
  have htailR := htail N R U hN hR hRN hU
  have htailH := htail N H U hN hH hHint hU
  have hratio : (N / R) ^ (j + 1) ≤ (N / H) ^ (j + 1) := by
    gcongr
  have hUneg : 0 ≤ U ^ (-(j : ℝ)) := Real.rpow_nonneg hU.le _
  have hCR :
      Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ)) ≤
        Cj * (N / H) ^ (j + 1) * U ^ (-(j : ℝ)) := by
    gcongr
  calc
    (∫ y in {y : ℝ | U ≤ |y|}, ‖A y * (KR y - KH y)‖) ≤
        ∫ y in tail, P * (‖KR y‖ + ‖KH y‖) := hmono
    _ = P * ((∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖) := hscale
    _ ≤ P * (Cj * (N / R) ^ (j + 1) * U ^ (-(j : ℝ)) +
        Cj * (N / H) ^ (j + 1) * U ^ (-(j : ℝ))) := by
      gcongr
    _ ≤ P * (2 * Cj * (N / H) ^ (j + 1) * U ^ (-(j : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hP
      linarith
    _ = _ := by rfl

/-- The paired-kernel power gain passes pointwise into the fixed-ambient cell coefficient. -/
theorem norm_maynardFixedAmbientDefectCellCoefficient_le_bufferedPower
    {a : ℝ → ℂ} {T mu H V : ℝ} {m : ℕ} {u : ℝ}
    (hT : 1 < T) (hmu : routeTPairedKernelBufferedMu ≤ mu)
    (hH : 0 < H)
    (hHR : H ≤ routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4))
    (hV0 : 0 ≤ V) (hsource : ‖a ((m : ℝ) + u)‖ ≤ V)
    (hylo : T ≤ (m : ℝ) + u) (hyhi : (m : ℝ) + u ≤ 2 * T)
    (hready : 4 * routeTPairedKernelCommonReferenceCoefficient *
      T ^ (-routeTPairedKernelDecayReserve) ≤ 1) :
    ‖maynardFixedAmbientDefectCellCoefficient a 1
        (routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4)) H 1 m u‖ ≤
      V * (16 * routeTPairedKernelCommonReferenceCoefficient *
        T ^ (-routeTPairedKernelDecayReserve)) := by
  let R := routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4)
  have hR : 0 < R := by
    dsimp only [R, routeTPairedKernelReferenceRelativeWidth]
    positivity
  have hy0 : 0 ≤ (m : ℝ) + u := by linarith
  have hyabs : |(m : ℝ) + u| ≤ 2 * T := by
    rw [abs_of_nonneg hy0]
    exact hyhi
  have hk := norm_routeTCommonBlockReference_sub_target_le_bufferedPower
    hT hmu (by norm_num : (0 : ℝ) < 1) hH
      (by simpa only [R] using hHR) hyabs hready
  change ‖a ((m : ℝ) + u) *
      (routeTNormalizedSmoothWindowMellin 1 R
          ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin 1 H
          ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * Complex.I))‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul hsource (by simpa only [one_mul] using hk)
    (norm_nonneg _) hV0

/-- Equation-(111) with the buffered paired-kernel power retained in its coefficient envelope. -/
theorem integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_bufferedPower
    {x T mu H V : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hT : 1 < T) (hmu : routeTPairedKernelBufferedMu ≤ mu)
    (hH : 0 < H)
    (hHR : H ≤ routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4))
    (hV0 : 0 ≤ V) (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖a ((m : ℝ) + u)‖ ≤ V)
    (hy : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      T ≤ (m : ℝ) + u ∧ (m : ℝ) + u ≤ 2 * T)
    (hready : 4 * routeTPairedKernelCommonReferenceCoefficient *
      T ^ (-routeTPairedKernelDecayReserve) ≤ 1) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S a lambda 1
          (routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4)) H 1‖ ^ 2) ≤
      4 * (2 * x) *
        (V * (16 * routeTPairedKernelCommonReferenceCoefficient *
          T ^ (-routeTPairedKernelDecayReserve))) ^ 2 *
        (S.card : ℝ) * (1 + 2 * (1 + Real.log cellCount)) := by
  let R := routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4)
  let A := V * (16 * routeTPairedKernelCommonReferenceCoefficient *
    T ^ (-routeTPairedKernelDecayReserve))
  have hR : 0 < R := by
    dsimp only [R, routeTPairedKernelReferenceRelativeWidth]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A, routeTPairedKernelCommonReferenceCoefficient]
    positivity
  have hbnd : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a 1 R H 1 m u‖ ≤ A := by
    intro m hm u hu
    exact norm_maynardFixedAmbientDefectCellCoefficient_le_bufferedPower
      hT hmu hH (by simpa only [R] using hHR) hV0 (hV m hm u hu)
        (hy m hm u hu).1 (hy m hm u hu).2 hready
  have hL2 := integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card
    (sigma := (1 : ℝ)) (A := A) (N := (1 : ℝ)) (R := R) (H := H)
    hx (by norm_num) hA (by norm_num) hR hH S hS a ha hbnd
  simpa only [sub_self, mul_zero, zero_add, Real.rpow_one, R, A] using hL2

/-- Equation-(112) with the same paired-kernel power retained through the fourth moment. -/
theorem integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_bufferedPower
    {x T mu H V : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hT : 1 < T) (hmu : routeTPairedKernelBufferedMu ≤ mu)
    (hH : 0 < H)
    (hHR : H ≤ routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4))
    (hV0 : 0 ≤ V) (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖a ((m : ℝ) + u)‖ ≤ V)
    (hy : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      T ≤ (m : ℝ) + u ∧ (m : ℝ) + u ≤ 2 * T)
    (hready : 4 * routeTPairedKernelCommonReferenceCoefficient *
      T ^ (-routeTPairedKernelDecayReserve) ≤ 1) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S a lambda 1
          (routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4)) H 1‖ ^ 4) ≤
      4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        (V * (16 * routeTPairedKernelCommonReferenceCoefficient *
          T ^ (-routeTPairedKernelDecayReserve))) ^ 4 *
        (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
  let R := routeTPairedKernelReferenceRelativeWidth (T ^ mu / 4)
  let A := V * (16 * routeTPairedKernelCommonReferenceCoefficient *
    T ^ (-routeTPairedKernelDecayReserve))
  have hR : 0 < R := by
    dsimp only [R, routeTPairedKernelReferenceRelativeWidth]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A, routeTPairedKernelCommonReferenceCoefficient]
    positivity
  have hbnd : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a 1 R H 1 m u‖ ≤ A := by
    intro m hm u hu
    exact norm_maynardFixedAmbientDefectCellCoefficient_le_bufferedPower
      hT hmu hH (by simpa only [R] using hHR) hV0 (hV m hm u hu)
        (hy m hm u hu).1 (hy m hm u hu).2 hready
  have hL4 := integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar
    (sigma := (1 : ℝ)) (A := A) (N := (1 : ℝ)) (R := R) (H := H)
    hx (by norm_num) hA (by norm_num) hR hH S hS a ha hbnd
  simpa only [sub_self, mul_zero, zero_add, Real.rpow_one, R, A] using hL4

end

end RHTower.Sieve
