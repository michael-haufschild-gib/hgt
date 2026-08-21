import GaloisForLFunctions.RHTower.Sieve.MaynardAdaptiveAmplitudeEnvelope
import GaloisForLFunctions.RHTower.Sieve.MaynardParityForcedSecond

/-!
# Canonical adaptive parity bad-measure capstone

At the canonical Route-T packet scale, parity forcing converts equation-(111) to a second-count
energy.  The three-scale adaptive envelope then cancels amplitude exactly and absorbs selector
entropy into an arbitrary positive height power.  The resulting physical bad-measure estimate is
uniform in amplitude, adaptive exponent, box cutoff, and parity choice.
-/

noncomputable section
namespace RHTower.Sieve

open MeasureTheory Filter

/-- Canonical amplitude-free equation-(111): after parity forcing and selector absorption, the
only unsummed losses are the cell logarithm and the explicit physical threshold denominator. -/
theorem eventually_volume_routeTPrimeGapPacket_adaptive_parity_forced_second
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {q K L cellCount : ℕ} {B : Finset ℕ} {a : ℝ → ℂ}
        {R H D V : ℝ},
      0 < R → 0 < H → 0 < D → 0 < V →
      0 ≤ 1 + 2 * (1 + Real.log cellCount) →
      L ≤ routeTPrimeGapPacketSupport T →
      B ⊆ Finset.range (2 * K) → B ⊆ Finset.range cellCount →
      Continuous a →
      (∀ m ∈ B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * V) →
      3 / 4 ≤ routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
        (routeTPrimeGapPacketBase T) V →
      4 * V * (T ^ (8 / 5 : ℝ)) ^
          (1 - routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) ≤
        (D / 2) * (Real.log T) ^ q →
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre B K).card : ℝ) T (T ^ (8 / 5 : ℝ))
          (routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) →
      IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre B K).card : ℝ) T (T ^ (8 / 5 : ℝ))
          (routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) →
      (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T))).real
          {lambda | D ≤
            ‖maynardFixedAmbientPhysicalDefectPacket B a lambda 1 R H 1‖} ≤
        2 * ((128 *
          (T ^ eta * T * (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
  have henergy :=
    eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_absorbed_sixty
      heta
  have hbaseTop : Filter.Tendsto routeTPrimeGapPacketBase
      Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ routeTPrimeGapPacketBase T := hbaseTop.eventually_ge_atTop 1
  filter_upwards [henergy, hbaseLarge, Filter.eventually_ge_atTop (1 : ℝ)] with
    T henergyT hbase hT
  intro q K L cellCount B a R H D V hR hH hD hV hcellLog hLX hB hBcell
    ha hsource halpha hthreshold heven hodd
  let Y : ℝ := T ^ (8 / 5 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
    (routeTPrimeGapPacketBase T) V
  let countScale : ℝ := T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hcountScale : 0 ≤ countScale := by
    dsimp only [countScale]
    positivity
  have henergyBound :
      routeTPrimeGapPacketBase T * V ^ 2 * countScale ≤
        T ^ eta * T * Y ^ routeTGapMomentNu := by
    apply henergyT hLX hT0 hV hcountScale
    · simpa only [alpha] using halpha
    · dsimp only [countScale]
      exact le_rfl
  have hmeasure :=
    volume_maynardFixedAmbientPhysicalDefectPacket_large_le_parity_forced_second
      (q := q) (K := K) (B := B) (a := a)
      (x := routeTPrimeGapPacketBase T) (N := 1) (R := R) (H := H)
      (D := D) (V := V) (T := T) (Y := Y) (alpha := alpha)
      (cellCount := cellCount) hbase (by norm_num) hR hH hD hV hT0 hY
      (Real.log_nonneg hT) hcellLog hB hBcell ha hsource
      (by simpa only [Y, alpha] using hthreshold)
      (by simpa only [Y, alpha] using heven)
      (by simpa only [Y, alpha] using hodd)
  have hnumer :
      4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
          (1 + 2 * (1 + Real.log cellCount)) ≤
        128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount)) := by
    calc
      4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
          (1 + 2 * (1 + Real.log cellCount)) =
        128 * (routeTPrimeGapPacketBase T * V ^ 2 * countScale) *
          (1 + 2 * (1 + Real.log cellCount)) := by ring
      _ ≤ 128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left henergyBound (by norm_num)) hcellLog
  have hquot :
      (4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
          (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2 ≤
        (128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2 :=
    div_le_div_of_nonneg_right hnumer (sq_nonneg (D / 2))
  calc
    (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
        (2 * routeTPrimeGapPacketBase T))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket B a lambda 1 R H 1‖} ≤
      2 * ((4 * (2 * routeTPrimeGapPacketBase T) * (4 * V) ^ 2 * countScale *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
      simpa only [Y, alpha, countScale] using hmeasure
    _ ≤ 2 * ((128 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 2 * ((128 *
        (T ^ eta * T * (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu) *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
      dsimp only [Y]

end RHTower.Sieve
