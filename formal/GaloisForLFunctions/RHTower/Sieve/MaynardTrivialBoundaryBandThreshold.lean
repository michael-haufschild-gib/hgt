import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryFirstExclusion

noncomputable section
namespace RHTower.Sieve

open Filter

/-- Every positive amplitude band above the exact trivial boundary automatically satisfies the
large-packet threshold that rules out Maynard's first receiver. The band depth and selector cost
are both paid by one fixed logarithmic power. -/
theorem eventually_routeT_amplitudeBand_firstExclusionThreshold
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L : ℕ} {V : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T → 0 < V →
      routeTTrivialBoundaryAmplitudeThreshold
          L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) ≤ V →
      4 * V * (T ^ (8 / 5 : ℝ)) ^
          (1 - routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) ≤
        ((D / (2 * (routeTTrivialBoundaryBandCount T : ℝ))) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  have hcost := eventually_sixteen_bandCount_selectorCost_le_receiverLog hD
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hcost, hbaseLarge, Filter.eventually_ge_atTop (1 : ℝ)] with
    T hcostT hbase hT
  intro L V hL hLX hV hthreshold
  let N : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let Y : ℝ := T ^ (8 / 5 : ℝ)
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hN : 1 ≤ N := by
    dsimp only [N]
    linarith
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hX : 1 < X := by
    have hceil : 3 * N ≤ (X : ℝ) := by
      dsimp only [X, N, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hXone : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hceilUpper : (X : ℝ) < 3 * N + 1 := by
    dsimp only [X, N, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXN : (X : ℝ) ≤ 4 * N := by linarith
  have hNY : 4 * N = Y := by
    dsimp only [N, Y, routeTPrimeGapPacketBase]
    field_simp
  have hSupport : (X : ℝ) ≤ Y := by rw [← hNY]; exact hXN
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hDbase : 1 < N / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [N]
    linarith
  have hkappa : 1 ≤ kappa := by dsimp only [kappa]; norm_num
  have hLowerComparable : Y ≤ kappa * (N / (2 ^ 120 : ℝ)) := by
    dsimp only [kappa]
    rw [← hNY]
    ring_nf
    exact le_rfl
  have halpha : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hDbase (by simpa only [X, N] using hthreshold)
  have hA : V * Y ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hDbase hV hY hkappa hSupport
          hLowerComparable halpha)
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    simpa only [Y] using hSupport
  have hcostBound :
      16 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [Q, kappa] using hcostT L X hXone (by simpa only [X] using hLX) hXscale
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  have hfactor : 0 ≤ 16 * Q := by positivity
  have hfull : 16 * Q * (V * Y ^ (1 - alpha)) ≤
      D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      16 * Q * (V * Y ^ (1 - alpha)) ≤
          16 * Q * (heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA hfactor
      _ = 16 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hcostBound
  have hden : 0 < 4 * Q := mul_pos (by norm_num) hQ
  have hdiv : 4 * (V * Y ^ (1 - alpha)) ≤
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      4 * (V * Y ^ (1 - alpha)) * (4 * Q) =
          16 * Q * (V * Y ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hfull
  have htarget :
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) =
        ((D / (2 * Q)) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    field_simp
    ring
  rw [htarget] at hdiv
  simpa only [N, X, Y, alpha, Q, mul_assoc] using hdiv

end RHTower.Sieve
