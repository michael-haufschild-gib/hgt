import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryBandSchedule

noncomputable section
namespace RHTower.Sieve

open Filter

/-- Fixed receiver logarithmic power paying one amplitude-band count and degree-60 selector cost. -/
def routeTTrivialBoundaryReceiverLogPower : ℕ := 122

/-- Exact first-branch cost cancellation dual to the squared second-count cancellation. -/
theorem routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
    (L X k : ℕ) (hk : 0 < k) (hX : 1 < X) {N V Y kappa : ℝ}
    (hD : 1 < N / (2 ^ (2 * k) : ℝ))
    (hV : 0 < V) (hY : 0 < Y) (hkappa : 1 ≤ kappa)
    (hSupport : (X : ℝ) ≤ Y)
    (hLowerComparable : Y ≤ kappa * (N / (2 ^ (2 * k) : ℝ)))
    (halphaLower : (1 + routeTGapMomentNu) / 2 ≤
      routeTAdaptiveCellAmplitude L X k N V) :
    V * Y ^ (1 - routeTAdaptiveCellAmplitude L X k N V) ≤
      heathBrownEligibleBoxCost L X k *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X k N V
  let C : ℝ := heathBrownEligibleBoxCost L X k *
    kappa ^ routeTTrivialBoundaryDistortionExponent
  have henvelope :=
    routeTAdaptiveCellAmplitude_threshold_le_receiverScale_envelope_trivialBoundary
      L X k hk hX hD hV hY hkappa hSupport hLowerComparable halphaLower
  have hpower0 : 0 ≤ Y ^ (1 - alpha) := Real.rpow_nonneg hY.le _
  have hmul : V * Y ^ (1 - alpha) ≤
      (C * Y ^ (alpha - 1)) * Y ^ (1 - alpha) := by
    exact mul_le_mul_of_nonneg_right (by simpa only [C, alpha] using henvelope) hpower0
  calc
    V * Y ^ (1 - routeTAdaptiveCellAmplitude L X k N V) ≤
        (C * Y ^ (alpha - 1)) * Y ^ (1 - alpha) := by
      simpa only [alpha] using hmul
    _ = C * (Y ^ (alpha - 1) * Y ^ (1 - alpha)) := by ring
    _ = C * Y ^ ((alpha - 1) + (1 - alpha)) := by
      rw [Real.rpow_add hY]
    _ = C := by simp
    _ = heathBrownEligibleBoxCost L X k *
        kappa ^ routeTTrivialBoundaryDistortionExponent := rfl

/-- Linear-log upper constant for the canonical amplitude-band count. -/
def routeTTrivialBoundaryBandLogConstant : ℝ :=
  2 + 2 / Real.log 2

theorem routeTTrivialBoundaryBandCount_cast_le_log
    {T : ℝ} (hT : 1 ≤ T) :
    (routeTTrivialBoundaryBandCount T : ℝ) ≤
      routeTTrivialBoundaryBandLogConstant * (1 + Real.log T) := by
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 0 < 1 + 2 * Real.log T / Real.log 2 := by positivity
  have hceil :
      (routeTTrivialBoundaryBandCount T : ℝ) <
        2 + 2 * Real.log T / Real.log 2 := by
    calc
      (routeTTrivialBoundaryBandCount T : ℝ) <
          1 + 2 * Real.log T / Real.log 2 + 1 := by
        simpa only [routeTTrivialBoundaryBandCount] using Nat.ceil_lt_add_one harg.le
      _ = 2 + 2 * Real.log T / Real.log 2 := by ring
  dsimp only [routeTTrivialBoundaryBandLogConstant]
  have hinv' : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlogTwo.le
  have hcross :
      2 + 2 * Real.log T / Real.log 2 ≤
        (2 + 2 / Real.log 2) * (1 + Real.log T) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have heq :
        (2 + 2 * (Real.log 2)⁻¹) * (1 + Real.log T) =
          (2 + 2 * Real.log T * (Real.log 2)⁻¹) +
            (2 * (Real.log 2)⁻¹ + 2 * Real.log T) := by ring
    rw [heq]
    exact le_add_of_nonneg_right
      (add_nonneg (mul_nonneg (by norm_num) hinv')
        (mul_nonneg (by norm_num) hlogT))
  exact hceil.le.trans hcross

/-- Linear-log upper constant for the exact Route-T selector logarithm base. -/
def routeTTrivialBoundaryLogBaseConstant : ℝ :=
  4 + 240 * Real.log 2

theorem routeTPrimeGapPacketLogBase_le_one_add_log
    {T : ℝ} {X : ℕ} (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ)) :
    1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ)) ≤
      routeTTrivialBoundaryLogBaseConstant * (1 + Real.log T) := by
  let C : ℝ := (2 : ℝ) ^ 120
  let M : ℝ := (((2 ^ 120 * X : ℕ) : ℝ))
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hM : M = C * (X : ℝ) := by
    simp only [M, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hlogX : Real.log (X : ℝ) ≤ (8 / 5 : ℝ) * Real.log T := by
    have hlog := Real.log_le_log hXpos hXscale
    rwa [Real.log_rpow hTpos] at hlog
  have hlogC : Real.log C = 120 * Real.log 2 := by
    dsimp only [C]
    rw [Real.log_pow]
    norm_num
  have hlogM : Real.log M ≤
      120 * Real.log 2 + (8 / 5 : ℝ) * Real.log T := by
    rw [hM, Real.log_mul hCpos.ne' hXpos.ne', hlogC]
    linarith
  dsimp only [routeTTrivialBoundaryLogBaseConstant]
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnonneg : 0 ≤ (4 + 240 * Real.log 2) * Real.log T := by positivity
  nlinarith

/-- One fixed logarithmic power pays the canonical amplitude-band depth, the exact degree-60
selector cost, and the trivial-boundary scale distortion. -/
theorem eventually_sixteen_bandCount_selectorCost_le_receiverLog
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ L X : ℕ, 1 ≤ X → L ≤ X → (X : ℝ) ≤ T ^ (8 / 5 : ℝ) →
        16 * (routeTTrivialBoundaryBandCount T : ℝ) *
            heathBrownEligibleBoxCost L X 60 *
              (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
          D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  let CQ : ℝ := routeTTrivialBoundaryBandLogConstant
  let CB : ℝ := routeTTrivialBoundaryLogBaseConstant
  let CC : ℝ := (60 : ℝ) * (2 : ℝ) ^ 60
  let KD : ℝ := (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent
  let Cbase : ℝ := 16 * CQ * CC * CB ^ 120 * KD
  let C0 : ℝ := Cbase * 2 ^ 121
  let M : ℝ := max 1 (C0 / D)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop M
  filter_upwards [hlog, Filter.eventually_ge_atTop (1 : ℝ)] with T hlogT hT
  intro L X hX hLX hXscale
  let ell : ℝ := Real.log T
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hlogOne : 1 ≤ ell := by
    exact (le_max_left _ _).trans (by simpa only [ell, M] using hlogT)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hCQ : 0 ≤ CQ := by
    dsimp only [CQ, routeTTrivialBoundaryBandLogConstant]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hCB : 0 ≤ CB := by
    dsimp only [CB, routeTTrivialBoundaryLogBaseConstant]
    positivity
  have hCC : 0 ≤ CC := by dsimp only [CC]; positivity
  have hKD : 0 ≤ KD := by dsimp only [KD]; positivity
  have hCbase : 0 ≤ Cbase := by
    dsimp only [Cbase]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hCQ) hCC)
        (pow_nonneg hCB 120)) hKD
  have hB : 0 ≤ B := by
    have hMone : (1 : ℝ) ≤ (((2 ^ 120 * X : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
    dsimp only [B]
    linarith [Real.log_nonneg hMone]
  have hQ : (routeTTrivialBoundaryBandCount T : ℝ) ≤ CQ * (1 + ell) := by
    simpa only [CQ, ell] using routeTTrivialBoundaryBandCount_cast_le_log hT
  have hBupper : B ≤ CB * (1 + ell) := by
    simpa only [B, CB, ell] using
      routeTPrimeGapPacketLogBase_le_one_add_log hT hX hXscale
  have hcost0 : 0 ≤ heathBrownEligibleBoxCost L X 60 := by
    dsimp only [heathBrownEligibleBoxCost]
    positivity
  have hcostRaw := heathBrownEligibleBoxCost_sixty_le_routeTLogBase L X hX hLX
  have hBpow : B ^ 120 ≤ (CB * (1 + ell)) ^ 120 :=
    pow_le_pow_left₀ hB hBupper 120
  have hcost : heathBrownEligibleBoxCost L X 60 ≤
      CC * CB ^ 120 * (1 + ell) ^ 120 := by
    calc
      heathBrownEligibleBoxCost L X 60 ≤ CC * B ^ 120 := by
        simpa only [CC, B] using hcostRaw
      _ ≤ CC * (CB * (1 + ell)) ^ 120 :=
        mul_le_mul_of_nonneg_left hBpow hCC
      _ = CC * CB ^ 120 * (1 + ell) ^ 120 := by
        rw [mul_pow]
        ring
  have hOneLog : 0 ≤ 1 + ell := by linarith
  have hcore :
      16 * (routeTTrivialBoundaryBandCount T : ℝ) *
          heathBrownEligibleBoxCost L X 60 * KD ≤
        Cbase * (1 + ell) ^ 121 := by
    have hqUpper0 : 0 ≤ 16 * (CQ * (1 + ell)) :=
      mul_nonneg (by norm_num) (mul_nonneg hCQ hOneLog)
    have hqStep :
        16 * (routeTTrivialBoundaryBandCount T : ℝ) ≤
          16 * (CQ * (1 + ell)) :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    have hfirst :
        16 * (routeTTrivialBoundaryBandCount T : ℝ) *
            heathBrownEligibleBoxCost L X 60 ≤
          16 * (CQ * (1 + ell)) *
            (CC * CB ^ 120 * (1 + ell) ^ 120) :=
      mul_le_mul hqStep hcost hcost0
        hqUpper0
    calc
      16 * (routeTTrivialBoundaryBandCount T : ℝ) *
          heathBrownEligibleBoxCost L X 60 * KD ≤
        (16 * (CQ * (1 + ell)) *
          (CC * CB ^ 120 * (1 + ell) ^ 120)) * KD :=
            mul_le_mul_of_nonneg_right hfirst hKD
      _ = Cbase * (1 + ell) ^ 121 := by
        dsimp only [Cbase]
        rw [show (121 : ℕ) = 1 + 120 by norm_num, pow_add, pow_one]
        ring
  have hshapeBase : 1 + ell ≤ 2 * ell := by linarith
  have hshapePow : (1 + ell) ^ 121 ≤ (2 * ell) ^ 121 :=
    pow_le_pow_left₀ hOneLog hshapeBase 121
  have hshape :
      Cbase * (1 + ell) ^ 121 ≤
        C0 * ell ^ 121 := by
    calc
      Cbase * (1 + ell) ^ 121 ≤ Cbase * (2 * ell) ^ 121 :=
        mul_le_mul_of_nonneg_left hshapePow hCbase
      _ = C0 * ell ^ 121 := by
        dsimp only [C0]
        rw [mul_pow]
        ring
  have hCD : C0 / D ≤ ell := by
    exact (le_max_right _ _).trans (by simpa only [ell, M] using hlogT)
  have hconst : C0 ≤ D * ell := by
    have hout : C0 ≤ ell * D := (div_le_iff₀ hD).mp hCD
    simpa only [mul_comm] using hout
  have hlast : C0 * ell ^ 121 ≤ D * ell ^ 122 := by
    have hp : 0 ≤ ell ^ 121 := pow_nonneg (zero_le_one.trans hlogOne) _
    calc
      C0 * ell ^ 121 ≤ (D * ell) * ell ^ 121 :=
        mul_le_mul_of_nonneg_right hconst hp
      _ = D * ell ^ 122 := by
        rw [show (122 : ℕ) = 1 + 121 by norm_num, pow_add, pow_one]
        ring
  simpa only [KD, ell, routeTTrivialBoundaryReceiverLogPower] using
    hcore.trans (hshape.trans hlast)

end RHTower.Sieve
