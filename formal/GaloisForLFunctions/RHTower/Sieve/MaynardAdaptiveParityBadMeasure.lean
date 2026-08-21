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

/-- The spatial Gram logarithm is nonnegative for every natural cell count, including zero. -/
theorem routeTCellLogFactor_nonneg (cellCount : ℕ) :
    0 ≤ 1 + 2 * (1 + Real.log cellCount) := by
  by_cases hzero : cellCount = 0
  · subst cellCount
    norm_num
  · have hone : (1 : ℕ) ≤ cellCount := Nat.one_le_iff_ne_zero.mpr hzero
    have honeReal : (1 : ℝ) ≤ cellCount := by exact_mod_cast hone
    linarith [Real.log_nonneg honeReal]

/-- Uniformly for every cell family of cardinal ambient range at most `T`, the single spatial Gram
logarithm is absorbed by an arbitrary positive Route-T power. -/
theorem eventually_routeTCellLogFactor_absorbed
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ cellCount : ℕ, (cellCount : ℝ) ≤ T →
        1 + 2 * (1 + Real.log cellCount) ≤ T ^ eta := by
  let eps : ℝ := eta / 2
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have hlog := RHTower.burnolEventually_log_pow_le_rpow heps 1
  have hconst : ∀ᶠ T : ℝ in Filter.atTop, (5 : ℝ) ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop 5
  filter_upwards [hlog, hconst, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hlogT hconstT hlogOne hT
  intro cellCount hcell
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlogT0 : 0 ≤ Real.log T := zero_le_one.trans hlogOne
  have hlogCell : Real.log cellCount ≤ Real.log T := by
    by_cases hzero : cellCount = 0
    · subst cellCount
      simpa using hlogT0
    · have hcellPos : (0 : ℝ) < cellCount := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      exact Real.log_le_log hcellPos hcell
  have hfactor :
      1 + 2 * (1 + Real.log cellCount) ≤ 5 * Real.log T := by linarith
  have hlogPower : Real.log T ≤ T ^ eps := by simpa using hlogT
  have hTpow0 : 0 ≤ T ^ eps := Real.rpow_nonneg hTpos.le _
  calc
    1 + 2 * (1 + Real.log cellCount) ≤ 5 * Real.log T := hfactor
    _ ≤ T ^ eps * T ^ eps :=
      mul_le_mul hconstT hlogPower hlogT0 hTpow0
    _ = T ^ (eps + eps) := (Real.rpow_add hTpos eps eps).symm
    _ = T ^ eta := by
      congr 1
      dsimp only [eps]
      linarith

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

/-- Fully absorbed canonical equation-(111): when the ambient cell range is at most the Route-T
height, the spatial logarithm joins selector entropy inside the arbitrary `T^eta` budget.  The
right side is independent of amplitude, adaptive exponent, cutoff, cell family, and parity. -/
theorem eventually_volume_routeTPrimeGapPacket_adaptive_parity_forced_second_fully_absorbed
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {q K L cellCount : ℕ} {B : Finset ℕ} {a : ℝ → ℂ}
        {R H D V : ℝ},
      0 < R → 0 < H → 0 < D → 0 < V →
      (cellCount : ℝ) ≤ T →
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
          (T ^ eta * T * (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu)) /
            (D / 2) ^ 2) := by
  let eps : ℝ := eta / 2
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have hmeasure :=
    eventually_volume_routeTPrimeGapPacket_adaptive_parity_forced_second heps
  have hlog := eventually_routeTCellLogFactor_absorbed heps
  filter_upwards [hmeasure, hlog, Filter.eventually_ge_atTop (1 : ℝ)] with
    T hmeasureT hlogT hT
  intro q K L cellCount B a R H D V hR hH hD hV hcell hLX hB hBcell
    ha hsource halpha hthreshold heven hodd
  have hmeasureBound := hmeasureT hR hH hD hV
    (routeTCellLogFactor_nonneg cellCount) hLX hB hBcell ha hsource
    halpha hthreshold heven hodd
  have hlogBound := hlogT cellCount hcell
  let Y : ℝ := T ^ (8 / 5 : ℝ)
  let G : ℝ := 1 + 2 * (1 + Real.log cellCount)
  let P : ℝ := T * Y ^ routeTGapMomentNu
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTeps0 : 0 ≤ T ^ eps := Real.rpow_nonneg hTpos.le _
  have hP0 : 0 ≤ P := by dsimp only [P, Y]; positivity
  have hcombine : (T ^ eps * P) * G ≤ T ^ eta * P := by
    calc
      (T ^ eps * P) * G = (T ^ eps * G) * P := by ac_rfl
      _ ≤ (T ^ eps * T ^ eps) * P :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by simpa only [G] using hlogBound) hTeps0) hP0
      _ = T ^ (eps + eps) * P := by rw [Real.rpow_add hTpos]
      _ = T ^ eta * P := by
        congr 2
        dsimp only [eps]
        linarith
  have hnumer :
      128 * ((T ^ eps * T * Y ^ routeTGapMomentNu) * G) ≤
        128 * (T ^ eta * T * Y ^ routeTGapMomentNu) := by
    have hcombine' :
        (T ^ eps * T * Y ^ routeTGapMomentNu) * G ≤
          T ^ eta * T * Y ^ routeTGapMomentNu := by
      simpa only [P, mul_assoc] using hcombine
    exact mul_le_mul_of_nonneg_left hcombine' (by norm_num)
  have hquot :
      (128 * ((T ^ eps * T * Y ^ routeTGapMomentNu) * G)) / (D / 2) ^ 2 ≤
        (128 * (T ^ eta * T * Y ^ routeTGapMomentNu)) / (D / 2) ^ 2 :=
    div_le_div_of_nonneg_right hnumer (sq_nonneg (D / 2))
  calc
    (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
        (2 * routeTPrimeGapPacketBase T))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket B a lambda 1 R H 1‖} ≤
      2 * ((128 * ((T ^ eps * T * Y ^ routeTGapMomentNu) * G)) /
        (D / 2) ^ 2) := by
      simpa only [Y, G, mul_assoc] using hmeasureBound
    _ ≤ 2 * ((128 * (T ^ eta * T * Y ^ routeTGapMomentNu)) /
        (D / 2) ^ 2) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 2 * ((128 *
        (T ^ eta * T * (T ^ (8 / 5 : ℝ)) ^ routeTGapMomentNu)) /
          (D / 2) ^ 2) := by dsimp only [Y]

end RHTower.Sieve
