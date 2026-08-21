import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryAdaptiveEnvelope

noncomputable section
namespace RHTower.Sieve

open MeasureTheory Filter

/-- The canonical base-amplitude layer has the same critical bad-measure scale as every selected
positive band: trivial cardinality is exactly the second count at exponent `(1+nu)/2`. -/
theorem eventually_volume_routeTPrimeGapPacket_trivialBoundary_base
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {L cellCount : ℕ} {U : Finset ℕ} {a : ℝ → ℂ} {R H D : ℝ},
      0 < R → 0 < H → 0 < D →
      L ≤ routeTPrimeGapPacketSupport T →
      (cellCount : ℝ) ≤ T →
      U ⊆ Finset.range cellCount →
      Continuous a →
      ∀ (c : ℕ → ℝ),
      (∀ m ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ ‖a (c m)‖) →
      let V := routeTTrivialBoundaryAmplitudeThreshold
        L (routeTPrimeGapPacketSupport T) 60 (routeTPrimeGapPacketBase T)
      let B := maynardUnitCellBaseAmplitudeSet U a c V
      (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T))).real
          {lambda | D ≤
            ‖maynardFixedAmbientPhysicalDefectPacket B a lambda 1 R H 1‖} ≤
        (32 * (T ^ eta * T *
          (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount))) / D ^ 2 := by
  have henergy :=
    eventually_routeTPrimeGapPacket_adaptive_second_count_cancellation_absorbed_sixty_trivialBoundary
      heta
  have hbaseTop : Filter.Tendsto routeTPrimeGapPacketBase
      Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in Filter.atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [henergy, hbaseLarge, Filter.eventually_ge_atTop (1 : ℝ)] with
    T henergyT hbase hT
  intro L cellCount U a R H D hR hH hD hLX hcell hU ha c hmax
  let N : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let Y : ℝ := T ^ (8 / 5 : ℝ)
  let V : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 N
  let B : Finset ℕ := maynardUnitCellBaseAmplitudeSet U a c V
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  have hN : 1 ≤ N := by dsimp only [N]; linarith
  have hDbase : 1 < N / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [N]
    linarith
  have hV : 0 < V := by
    dsimp only [V]
    exact routeTTrivialBoundaryAmplitudeThreshold_pos L X 60 (by norm_num)
      (by simpa only [Nat.reduceMul] using hDbase)
  have hBRange : B ⊆ Finset.range cellCount := by
    exact (Finset.filter_subset _ _).trans hU
  have hcardNat : B.card ≤ cellCount := by
    simpa using Finset.card_le_card hBRange
  have hcard : (B.card : ℝ) ≤ T := by
    have hcardCast : (B.card : ℝ) ≤ (cellCount : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardCast.trans hcell
  have halphaEq : alpha = (1 + routeTGapMomentNu) / 2 := by
    dsimp only [alpha, V, X, N]
    exact routeTAdaptiveCellAmplitude_trivialBoundaryThreshold
      L (routeTPrimeGapPacketSupport T) 60 (by norm_num)
        (by simpa only [Nat.reduceMul, N] using hDbase)
  have hsecond : (B.card : ℝ) ≤
      T * Y ^ (1 + routeTGapMomentNu - 2 * alpha) := by
    have hexp : 1 + routeTGapMomentNu - 2 * alpha = 0 := by
      rw [halphaEq]
      ring
    simpa only [hexp, Real.rpow_zero, mul_one] using hcard
  have henergyBound : N * V ^ 2 * (B.card : ℝ) ≤
      T ^ eta * T * Y ^ routeTGapMomentNu := by
    simpa only [N, X, Y, V, alpha] using
      (henergyT hLX (zero_le_one.trans hT) hV (Nat.cast_nonneg B.card)
        (by simpa only [X, N, V, alpha] using halphaEq.ge) hsecond)
  have hsource : ∀ m ∈ B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ V := by
    intro m hm u hu
    have hmU : m ∈ U := Finset.filter_subset _ _ hm
    have hrep : ‖a (c m)‖ < V := (Finset.mem_filter.mp hm).2
    exact (hmax m hmU u hu).trans hrep.le
  have hmeasure :=
    volume_maynardFixedAmbientPhysicalDefectPacket_large_le_card_of_source_bound
      hN (by norm_num : (0 : ℝ) < 1) hR hH hV.le hD B hBRange a ha hsource
  have hlog : 0 ≤ 1 + 2 * (1 + Real.log cellCount) :=
    routeTCellLogFactor_nonneg cellCount
  have hnumer :
      4 * (2 * N) * (2 * V) ^ 2 * (B.card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount)) ≤
        32 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount)) := by
    calc
      4 * (2 * N) * (2 * V) ^ 2 * (B.card : ℝ) *
          (1 + 2 * (1 + Real.log cellCount)) =
        32 * (N * V ^ 2 * (B.card : ℝ)) *
          (1 + 2 * (1 + Real.log cellCount)) := by ring
      _ ≤ 32 * (T ^ eta * T * Y ^ routeTGapMomentNu) *
          (1 + 2 * (1 + Real.log cellCount)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left henergyBound (by norm_num)) hlog
  have hquot := div_le_div_of_nonneg_right hnumer (sq_nonneg D)
  simpa only [N, X, Y, V, B] using hmeasure.trans hquot

end RHTower.Sieve
