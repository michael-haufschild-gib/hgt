import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryBaseMeasure
import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCanonicalCutoff

noncomputable section
namespace RHTower.Sieve

open Filter

/-- Canonical logarithmic depth for the amplitude decomposition. -/
def routeTTrivialBoundaryBandCount (T : ℝ) : ℕ :=
  ⌈1 + 2 * Real.log T / Real.log 2⌉₊

theorem routeTTrivialBoundaryBandCount_pos
    {T : ℝ} (hT : 1 ≤ T) :
    0 < routeTTrivialBoundaryBandCount T := by
  apply Nat.ceil_pos.mpr
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem two_mul_sq_le_two_pow_routeTTrivialBoundaryBandCount
    {T : ℝ} (hT : 0 < T) :
    2 * T ^ 2 ≤ ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil :
      1 + 2 * Real.log T / Real.log 2 ≤
        (routeTTrivialBoundaryBandCount T : ℝ) := by
    exact Nat.le_ceil _
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) hceil
  have hlogb : (2 : ℝ) ^ (Real.log T / Real.log 2) = T := by
    simpa only [Real.logb] using
      (Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1) hT)
  have hmiddle :
      (2 : ℝ) ^ (2 * Real.log T / Real.log 2) = T ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * Real.log T / Real.log 2) =
          (2 : ℝ) ^ ((Real.log T / Real.log 2) * 2) := by
            congr 1
            ring
      _ = ((2 : ℝ) ^ (Real.log T / Real.log 2)) ^ (2 : ℝ) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = T ^ (2 : ℝ) := by rw [hlogb]
      _ = T ^ 2 := Real.rpow_two T
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one, hmiddle] at hpow
  simpa only [Real.rpow_two, Real.rpow_natCast,
    Nat.cast_pow, Nat.cast_ofNat] using hpow

/-- The exact trivial-count amplitude is never smaller than one inverse height on the canonical
Route-T packet scale. -/
theorem eventually_one_div_le_routeTTrivialBoundaryAmplitudeThreshold :
    ∀ᶠ T : ℝ in atTop,
      ∀ L : ℕ,
        1 / T ≤ routeTTrivialBoundaryAmplitudeThreshold
          L (routeTPrimeGapPacketSupport T) 60 (routeTPrimeGapPacketBase T) := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hbaseLarge, Filter.eventually_ge_atTop (1 : ℝ)] with T hbase hT
  intro L
  let N : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let D : ℝ := N / (2 ^ 120 : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X 60
  let a : ℝ := (1 + routeTGapMomentNu) / 2 - 1
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hD : 1 < D := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [D, N]
    linarith
  have hDpos : 0 < D := zero_lt_one.trans hD
  have hCpos : 0 < C := by
    dsimp only [C]
    exact heathBrownEligibleBoxCost_pos L X 60 (by norm_num)
  have hC : 1 ≤ C := by
    have hcard : 0 < Fintype.card (HeathBrownBoxChoice L X 60) :=
      Fintype.card_pos_iff.mpr (nonempty_heathBrownBoxChoice L X 60 (by norm_num))
    have hcardOne : (1 : ℝ) ≤ Fintype.card (HeathBrownBoxChoice L X 60) := by
      exact_mod_cast hcard
    dsimp only [C, heathBrownEligibleBoxCost]
    exact one_le_mul_of_one_le_of_one_le hcardOne (by norm_num)
  have haLower : -(1 : ℝ) / 2 ≤ a := by
    dsimp only [a]
    linarith [routeTGapMomentNu_pos]
  have haUpper : a ≤ 0 := by
    dsimp only [a]
    linarith [routeTGapMomentNu_lt_half]
  have hDupper : D ≤ T ^ (8 / 5 : ℝ) := by
    have hpow0 : 0 ≤ T ^ (8 / 5 : ℝ) := Real.rpow_nonneg hTpos.le _
    calc
      D = T ^ (8 / 5 : ℝ) / (4 * 2 ^ 120) := by
        dsimp only [D, N, routeTPrimeGapPacketBase]
        ring
      _ ≤ T ^ (8 / 5 : ℝ) := div_le_self hpow0 (by norm_num)
  have hscale :
      (T ^ (8 / 5 : ℝ)) ^ (-(1 : ℝ) / 2) ≤ D ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDupper (by norm_num)
  have hscaleEq :
      (T ^ (8 / 5 : ℝ)) ^ (-(1 : ℝ) / 2) = T ^ (-(4 : ℝ) / 5) := by
    rw [← Real.rpow_mul hTpos.le]
    congr 1
    ring
  have hDexp : D ^ (-(1 : ℝ) / 2) ≤ D ^ a :=
    Real.rpow_le_rpow_of_exponent_le hD.le haLower
  have hTexp : T ^ (-(1 : ℝ)) ≤ T ^ (-(4 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  calc
    1 / T = T ^ (-(1 : ℝ)) := by simp only [Real.rpow_neg_one, one_div]
    _ ≤ T ^ (-(4 : ℝ) / 5) := hTexp
    _ = (T ^ (8 / 5 : ℝ)) ^ (-(1 : ℝ) / 2) := hscaleEq.symm
    _ ≤ D ^ (-(1 : ℝ) / 2) := hscale
    _ ≤ D ^ a := hDexp
    _ ≤ C * D ^ a := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hDpos.le a))
    _ = routeTTrivialBoundaryAmplitudeThreshold L X 60 N := by
      rfl

/-- The canonical logarithmic band depth strictly covers every unit-cell maximum of the literal
Route-T aggregate. -/
theorem eventually_norm_routeTAggregate_lt_trivialBoundary_bandCap :
    ∀ᶠ T : ℝ in atTop,
      ∀ L : ℕ, 1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ y : ℝ,
        ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
            (routeTPrimeGapPacketBase T)
            ((1 : ℂ) + (y : ℝ) * Complex.I)‖ <
          ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
            routeTTrivialBoundaryAmplitudeThreshold
              L (routeTPrimeGapPacketSupport T) 60
                (routeTPrimeGapPacketBase T) := by
  have hPevent :=
    eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_routeT_absorbed_leftCutoff
      (by norm_num : (0 : ℝ) < 1)
  have hVevent :=
    eventually_one_div_le_routeTTrivialBoundaryAmplitudeThreshold
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 1
  filter_upwards [hPevent, hVevent, hbaseLarge,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hPT hVT hbase hT
  intro L hL hLX y
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let V : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 x
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hx : 1 ≤ x := by simpa only [x] using hbase
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * x + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXx : (X : ℝ) ≤ 4 * x := by linarith
  have hxscale : 4 * x = T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    field_simp
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    rw [← hxscale]
    exact hXx
  have hP : P ≤ T := by
    have := hPT x L X hx hL hX (by simpa only [X] using hLX) hXx hXscale
    simpa only [P, Real.rpow_one] using this
  have hnorm :
      ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (1 / 75) x ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤ P := by
    dsimp only [P]
    convert
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X 60 hX T (1 / 75) x 1 y hxpos (by norm_num)) using 1
    norm_num
  have hV : 1 / T ≤ V := by
    simpa only [V, X, x] using hVT L
  have htwo :=
    two_mul_sq_le_two_pow_routeTTrivialBoundaryBandCount hTpos
  have hproduct :
      (2 * T ^ 2) * (1 / T) ≤
        ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) * V :=
    mul_le_mul htwo hV (by positivity) (by positivity)
  have hcap : T <
      ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) * V := by
    have hleft : (2 * T ^ 2) * (1 / T) = 2 * T := by
      field_simp
    rw [hleft] at hproduct
    linarith
  have hout := (hnorm.trans hP).trans_lt hcap
  simpa only [X, x, V] using hout

end RHTower.Sieve
