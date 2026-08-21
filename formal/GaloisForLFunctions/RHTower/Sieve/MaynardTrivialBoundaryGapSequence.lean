import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryBandCoverage
import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryBandThreshold
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTFixedCutoffCount

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Transition-strip receiver for one already-spaced selected ordinate sequence. -/
theorem eventually_routeT_selectedCell_fixedCutoff_gapSequence_twoAlternative_transition
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      (1 + routeTGapMomentNu) / 2 ≤ alpha → alpha ≤ 19 / 25 →
      0 < V → 1 ≤ delta → delta ≤ 2 * T → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - 1) ≤ V) →
      IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu) alpha := by
  filter_upwards [
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_to_trivialBoundary,
    eventually_card_le_maynard_second_of_selected_cell_coloring_transition,
    eventually_maynardHarmonicFixedLogCost_absorbed
      (r := 1 / 400) (by norm_num) 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcolorT hcountT hcost hT
  intro L X K mu N0 alpha V delta hX hL hXscale hLscale hmuLo hmuHi
    halphaLo halphaHi hV hdelta hdeltaHi hK S hS lam hband hgap haggregate hreserve
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hT hL hLscale i hi
  obtain ⟨color, hcolor⟩ := hcolorT X hX mu hmuLo hmuHi hXscale L hL
    1 alpha V N0 (by norm_num) halphaLo hV S lam hband hmobius
      haggregate hreserve
  have hraw := hcountT hX hL hXscale hLscale hmuLo hmuHi (by norm_num)
    halphaLo halphaHi (by positivity : 0 < delta) hdeltaHi S hS lam hgap hband
      color hcolor
  have hcost' : maynardHarmonicFactor K delta * (Real.log T) ^ 0 ≤
      T ^ ((1 / 200 : ℝ) / 2) := by
    simpa only [show (1 / 200 : ℝ) / 2 = 1 / 400 by norm_num] using
      hcost K delta hK hdelta
  apply routeT_two_alternative_of_reserved_height_count
    hT rfl (by norm_num : (0 : ℝ) < 1 / 200)
  right
  simpa using
    (maynard_count_receiver_margin_general (q := 0) hT.le hraw hcost')

/-- Full trivial-boundary receiver for one spaced selected ordinate sequence. -/
theorem eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_above_trivialBoundary
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 V delta : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < V →
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ V →
      1 ≤ delta → delta ≤ 2 * T → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu)
        (routeTAdaptiveCellAmplitude L X 60 N0 V) := by
  obtain ⟨A, hupper⟩ :=
    exists_eventually_routeT_selectedCell_fixedCutoff_all_amplitude
  filter_upwards [
    eventually_routeT_selectedCell_fixedCutoff_gapSequence_twoAlternative_transition q,
    hupper,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A q,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with
      T htransition hupperT hcostQ hcost0 hT
  intro L X K mu N0 V delta hX hL hXL hXscale hLscale hmuLo hmuHi hD
    hV hthreshold hdelta hdeltaHi hK S hS lam hband hgap hdiam haggregate
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N0 V
  have halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hD hthreshold
  have hreserve : ∀ box : HeathBrownBoxChoice L X 60,
      IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
      IsHeathBrownBoxWindowRelevant N0 X 60 box →
      heathBrownEligibleBoxCost L X 60 *
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (alpha - 1) ≤ V := by
    intro box _helig hwin
    exact routeTAdaptiveCellAmplitude_windowRelevant_reserve
      L X 60 (by norm_num) hX hD hV box hwin
  by_cases halphaHi : alpha ≤ 19 / 25
  · simpa only [alpha] using
      (htransition hX.le hL hXscale hLscale hmuLo hmuHi halphaLo halphaHi
        hV hdelta hdeltaHi hK S hS lam hband hgap haggregate hreserve)
  · have halphaThreeQuarter : 3 / 4 ≤ alpha := by
      have : 19 / 25 < alpha := lt_of_not_ge halphaHi
      norm_num at this ⊢
      linarith
    have hraw := hupperT hX.le hL hXL hXscale hLscale hmuLo hmuHi
      (by norm_num : (1 : ℝ) / 2 ≤ 1) halphaThreeQuarter hV
      (by positivity : 0 < delta) hdeltaHi S hS lam hband hgap hdiam
        haggregate hreserve
    have normalize :
        ((S.card : ℝ) ≤ maynardHarmonicFactor K delta *
              T ^ (mu * (1 - alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha) ∨
          (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
              T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha)) →
        IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu) alpha := by
      intro hcount
      apply routeT_two_alternative_of_reserved_height_count
        hT rfl (routeTSelectedCellAmplitudeReserve_pos (A := A) hT)
      rcases hcount with hfirst | hsecond
      · left
        exact maynard_count_receiver_margin_general hT.le hfirst
          (hcostQ alpha K delta hK hdelta)
      · right
        have hsecond' := maynard_count_receiver_margin_general
          (q := 0) hT.le hsecond (hcost0 alpha K delta hK hdelta)
        simpa using hsecond'
    simpa only [alpha] using normalize hraw

private theorem cast_two_mul_add_one_le_two_mul
    {j n : ℕ} (h : j < n) :
    (((2 * j : ℕ) : ℝ) + 1) ≤ (2 * n : ℕ) := by
  norm_cast
  omega

private theorem cast_two_mul_add_one_add_one_le_two_mul
    {j n : ℕ} (h : j < n) :
    (((2 * j + 1 : ℕ) : ℝ) + 1) ≤ (2 * n : ℕ) := by
  norm_cast
  omega

/-- Logarithmic selector base valid on every reparameterized Route-T shell through `mu ≤ 19/9`. -/
def routeTTrivialBoundaryShellLogBaseConstant : ℝ :=
  5 + 240 * Real.log 2

theorem routeTShellLogBase_le_one_add_log
    {T : ℝ} {X : ℕ} (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXscale : (X : ℝ) ≤ T ^ (19 / 9 : ℝ)) :
    1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ)) ≤
      routeTTrivialBoundaryShellLogBaseConstant * (1 + Real.log T) := by
  let C : ℝ := (2 : ℝ) ^ 120
  let M : ℝ := (((2 ^ 120 * X : ℕ) : ℝ))
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hM : M = C * (X : ℝ) := by
    simp only [M, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hlogX : Real.log (X : ℝ) ≤ (19 / 9 : ℝ) * Real.log T := by
    have hlog := Real.log_le_log hXpos hXscale
    rwa [Real.log_rpow hTpos] at hlog
  have hlogC : Real.log C = 120 * Real.log 2 := by
    dsimp only [C]
    rw [Real.log_pow]
    norm_num
  have hlogM : Real.log M ≤
      120 * Real.log 2 + (19 / 9 : ℝ) * Real.log T := by
    rw [hM, Real.log_mul hCpos.ne' hXpos.ne', hlogC]
    linarith
  dsimp only [routeTTrivialBoundaryShellLogBaseConstant]
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- One fixed logarithmic power absorbs variable-width shell depth and selector cost uniformly
through the full reparameterized exponent range `mu ≤ 19/9`. -/
theorem eventually_thirtytwo_shellBandCount_selectorCost_le_receiverLog
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ L X : ℕ, 1 ≤ X → L ≤ X → (X : ℝ) ≤ T ^ (19 / 9 : ℝ) →
        32 * (routeTTrivialBoundaryBandCount T : ℝ) *
            heathBrownEligibleBoxCost L X 60 *
              (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
          D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  let CQ : ℝ := routeTTrivialBoundaryBandLogConstant
  let CB : ℝ := routeTTrivialBoundaryShellLogBaseConstant
  let CC : ℝ := (60 : ℝ) * (2 : ℝ) ^ 60
  let KD : ℝ := (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent
  let Cbase : ℝ := 32 * CQ * CC * CB ^ 120 * KD
  let C0 : ℝ := Cbase * 2 ^ 121
  let M : ℝ := max 1 (C0 / D)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop M
  filter_upwards [hlog, Filter.eventually_ge_atTop (1 : ℝ)] with T hlogT hT
  intro L X hX hLX hXscale
  let ell : ℝ := Real.log T
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hlogOne : 1 ≤ ell := by
    exact (le_max_left _ _).trans (by simpa only [ell, M] using hlogT)
  have hCQ : 0 ≤ CQ := by
    dsimp only [CQ, routeTTrivialBoundaryBandLogConstant]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hCB : 0 ≤ CB := by
    dsimp only [CB, routeTTrivialBoundaryShellLogBaseConstant]
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
    simpa only [B, CB, ell] using routeTShellLogBase_le_one_add_log hT hX hXscale
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
      32 * (routeTTrivialBoundaryBandCount T : ℝ) *
          heathBrownEligibleBoxCost L X 60 * KD ≤
        Cbase * (1 + ell) ^ 121 := by
    have hqUpper0 : 0 ≤ 32 * (CQ * (1 + ell)) :=
      mul_nonneg (by norm_num) (mul_nonneg hCQ hOneLog)
    have hqStep :
        32 * (routeTTrivialBoundaryBandCount T : ℝ) ≤
          32 * (CQ * (1 + ell)) :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    have hfirst :
        32 * (routeTTrivialBoundaryBandCount T : ℝ) *
            heathBrownEligibleBoxCost L X 60 ≤
          32 * (CQ * (1 + ell)) *
            (CC * CB ^ 120 * (1 + ell) ^ 120) :=
      mul_le_mul hqStep hcost hcost0 hqUpper0
    calc
      32 * (routeTTrivialBoundaryBandCount T : ℝ) *
          heathBrownEligibleBoxCost L X 60 * KD ≤
        (32 * (CQ * (1 + ell)) *
          (CC * CB ^ 120 * (1 + ell) ^ 120)) * KD :=
            mul_le_mul_of_nonneg_right hfirst hKD
      _ = Cbase * (1 + ell) ^ 121 := by
        dsimp only [Cbase]
        rw [show (121 : ℕ) = 1 + 120 by norm_num, pow_add, pow_one]
        ring
  have hshapeBase : 1 + ell ≤ 2 * ell := by linarith
  have hshapePow : (1 + ell) ^ 121 ≤ (2 * ell) ^ 121 :=
    pow_le_pow_left₀ hOneLog hshapeBase 121
  have hshape : Cbase * (1 + ell) ^ 121 ≤ C0 * ell ^ 121 := by
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

/-- First-exclusion threshold on a shell after exact height reparameterization.  Only the full
Route-T exponent bound and the physical-support comparison survive. -/
theorem eventually_routeT_amplitudeBand_reparameterizedShell_firstExclusionThreshold
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} {N V : ℝ},
      1 < X → 1 ≤ L → L ≤ X → (X : ℝ) ≤ T ^ (19 / 9 : ℝ) →
      1 < N / (2 ^ 120 : ℝ) → 0 < V →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ 120 : ℝ)) →
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N ≤ V →
      8 * V * (X : ℝ) ^
          (1 - routeTAdaptiveCellAmplitude L X 60 N V) ≤
        ((D / (2 * (routeTTrivialBoundaryBandCount T : ℝ))) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  filter_upwards [
    eventually_thirtytwo_shellBandCount_selectorCost_le_receiverLog hD,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hcost hT
  intro L X N V hX hL hLX hXscale hN hV hcomparable hthreshold
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hkappa : 1 ≤ kappa := by dsimp only [kappa]; norm_num
  have halpha : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hN hthreshold
  have hA : V * (X : ℝ) ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hN hV (by positivity : (0 : ℝ) < X)
          hkappa (le_refl _) (by simpa only [kappa] using hcomparable) halpha)
  have hcostFull :
      32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [Q, kappa] using hcost L X hX.le hLX hXscale
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  have hfull : 32 * Q * (V * (X : ℝ) ^ (1 - alpha)) ≤
      D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      32 * Q * (V * (X : ℝ) ^ (1 - alpha)) ≤
          32 * Q * (heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hcostFull
  have hden : 0 < 4 * Q := by positivity
  have hdiv : 8 * (V * (X : ℝ) ^ (1 - alpha)) ≤
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      8 * (V * (X : ℝ) ^ (1 - alpha)) * (4 * Q) =
          32 * Q * (V * (X : ℝ) ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hfull
  have htarget :
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) =
        ((D / (2 * Q)) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    field_simp
    ring
  rw [htarget] at hdiv
  simpa only [alpha, Q, mul_assoc] using hdiv

/-- Exact forcing law for an extracted shell band.  The factor eight is precisely the worst-case
cost of cell width `delta ≤ 2`; no first-alternative residue remains. -/
theorem routeT_second_alternative_of_shell_mass
    {q : ℕ} {D V x T alpha delta Q R : ℝ}
    (hD : 0 < D) (hV : 0 < V) (hQ : 0 < Q)
    (hdelta : 1 ≤ delta) (hdeltaTwo : delta ≤ 2)
    (hlog : 0 ≤ Real.log T)
    (hthreshold : 8 * V * x ^ (1 - alpha) ≤
      ((D / (2 * Q)) / 2) * (Real.log T) ^ q)
    (hmass : D / (16 * delta * Q) ≤ V * R)
    (halt : IsRouteTMaynardTwoAlternative q R T x alpha) :
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  let P : ℝ := (Real.log T) ^ q
  let E : ℝ := D / (32 * Q)
  let A : ℝ := D / (16 * delta * Q)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hdelta0 : 0 < delta := zero_lt_one.trans_le hdelta
  have hdenSmall : 0 < 16 * delta * Q := by positivity
  have hdenLarge : 16 * delta * Q ≤ 32 * Q := by
    have hdeltaBound : 16 * delta ≤ (32 : ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right hdeltaBound hQ.le
  have hEA : E ≤ A := by
    dsimp only [E, A]
    exact div_le_div_of_nonneg_left hD.le hdenSmall hdenLarge
  have hthreshold' : V * x ^ (1 - alpha) ≤ E * P := by
    have hscaled : 8 * (V * x ^ (1 - alpha)) ≤ 8 * (E * P) := by
      calc
        8 * (V * x ^ (1 - alpha)) = 8 * V * x ^ (1 - alpha) := by ring
        _ ≤ ((D / (2 * Q)) / 2) * (Real.log T) ^ q := hthreshold
        _ = 8 * (E * P) := by
          dsimp only [E, P]
          field_simp
          ring
    exact (mul_le_mul_iff_left₀ (by norm_num : (0 : ℝ) < 8)).mp
      (by simpa only [mul_comm] using hscaled)
  have hmul : V * x ^ (1 - alpha) ≤ V * (R * P) := by
    calc
      V * x ^ (1 - alpha) ≤ E * P := hthreshold'
      _ ≤ A * P := mul_le_mul_of_nonneg_right hEA hP
      _ ≤ (V * R) * P :=
        mul_le_mul_of_nonneg_right (by simpa only [A] using hmass) hP
      _ = V * (R * P) := by ring
  have hlarge : x ^ (1 - alpha) ≤ R * (Real.log T) ^ q := by
    have hmul' : x ^ (1 - alpha) * V ≤ (R * P) * V := by
      simpa only [mul_comm] using hmul
    simpa only [P] using (mul_le_mul_iff_left₀ hV).mp hmul'
  exact routeT_second_alternative_of_large_error hlarge halt

private theorem shellBandMass_uniform_of_width_le_two
    {D delta Q : ℝ} (hD : 0 ≤ D) (hdelta : 0 < delta)
    (hdeltaTwo : delta ≤ 2) (hQ : 0 < Q) :
    D / (32 * Q) ≤ D / (16 * delta * Q) := by
  have hdenSmall : 0 < 16 * delta * Q :=
    mul_pos (mul_pos (by norm_num) hdelta) hQ
  have hdeltaBound : 16 * delta ≤ (32 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hdeltaTwo (by norm_num)).trans_eq (by ring)
  have hdenLarge : 16 * delta * Q ≤ 32 * Q :=
    mul_le_mul_of_nonneg_right hdeltaBound hQ.le
  exact div_le_div_of_nonneg_left hD hdenSmall hdenLarge

/-- Variable-width shell extraction pays at most twice the unit-cell first-exclusion cost.
The exact support, rather than the larger ambient comparison scale, is the receiver base. -/
theorem eventually_routeT_amplitudeBand_shell_firstExclusionThreshold
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L : ℕ} {V : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T → 0 < V →
      routeTTrivialBoundaryAmplitudeThreshold
          L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) ≤ V →
      8 * V * (routeTPrimeGapPacketSupport T : ℝ) ^
          (1 - routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) V) ≤
        ((D / (2 * (routeTTrivialBoundaryBandCount T : ℝ))) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  have hcost := eventually_sixteen_bandCount_selectorCost_le_receiverLog
    (show 0 < D / 2 by positivity)
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
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hN : 1 ≤ N := by dsimp only [N]; linarith
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hX : 1 < X := by
    have hceil : 3 * N ≤ (X : ℝ) := by
      dsimp only [X, N, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hXone : 1 ≤ X := hX.le
  have hceilUpper : (X : ℝ) < 3 * N + 1 := by
    dsimp only [X, N, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXN : (X : ℝ) ≤ 4 * N := by linarith
  have hDbase : 1 < N / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [N]
    linarith
  have hkappa : 1 ≤ kappa := by dsimp only [kappa]; norm_num
  have hLowerComparable : (X : ℝ) ≤ kappa * (N / (2 ^ 120 : ℝ)) := by
    dsimp only [kappa]
    have heq : 4 * (2 ^ 120 : ℝ) * (N / (2 ^ 120 : ℝ)) = 4 * N := by
      field_simp
    rw [heq]
    exact hXN
  have halpha : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hDbase (by simpa only [X, N] using hthreshold)
  have hA : V * (X : ℝ) ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hDbase hV (by positivity : (0 : ℝ) < X)
          hkappa (le_refl _) hLowerComparable halpha)
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    have hYeq : T ^ (8 / 5 : ℝ) = 4 * N := by
      dsimp only [N, routeTPrimeGapPacketBase]
      field_simp
    rw [hYeq]
    exact hXN
  have hcostHalf :
      16 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        (D / 2) * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [Q, kappa] using
      hcostT L X hXone (by simpa only [X] using hLX) hXscale
  have hcostFull :
      32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent =
          2 * (16 * Q * heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) := by ring
      _ ≤ 2 * ((D / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) :=
        mul_le_mul_of_nonneg_left hcostHalf (by norm_num)
      _ = D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by ring
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  have hfull : 32 * Q * (V * (X : ℝ) ^ (1 - alpha)) ≤
      D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      32 * Q * (V * (X : ℝ) ^ (1 - alpha)) ≤
          32 * Q * (heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hcostFull
  have hden : 0 < 4 * Q := by positivity
  have hdiv : 8 * (V * (X : ℝ) ^ (1 - alpha)) ≤
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      8 * (V * (X : ℝ) ^ (1 - alpha)) * (4 * Q) =
          32 * Q * (V * (X : ℝ) ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hfull
  have htarget :
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) =
        ((D / (2 * Q)) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    field_simp
    ring
  rw [htarget] at hdiv
  simpa only [N, X, alpha, Q, mul_assoc] using hdiv

/-- Exact even-cell discretization of a central ordinate shell feeds the trivial-boundary
receiver without integer endpoint trimming or a unit-cell reindexing hypothesis. -/
theorem eventually_exists_routeT_adjacentDefect_central_gapSequence_receiver_above_trivialBoundary
    (receiverQ : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X n Q : ℕ} {mu N0 H R delta B : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < H → 0 < R → H ≤ R →
      1 ≤ delta → delta ≤ 2 → 0 < B → 0 < Q →
      T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T →
      (∀ y ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta),
        |y| ≤ N0 / (2 * R)) →
      B ≤ ‖∫ y in T..(T + ((2 * n : ℕ) : ℝ) * delta),
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) N0
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N0 R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N0 H
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
      heathBrownWindowRelevantFixedPolylogBound L X 60 N0 1 ≤
        (((2 ^ Q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) →
      (n : ℝ) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤
        B / (16 * delta) →
      ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < Q ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) N0
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        B / (16 * delta * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) *
              (S.card : ℝ) ∧
        IsRouteTMaynardTwoAlternative receiverQ (S.card : ℝ) T (T ^ mu)
          (routeTAdaptiveCellAmplitude L X 60 N0
            (((2 ^ q : ℕ) : ℝ) *
              routeTTrivialBoundaryAmplitudeThreshold L X 60 N0)) := by
  filter_upwards [
    eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_above_trivialBoundary
      receiverQ,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hT
  intro L X n Q mu N0 H R delta B hX hL hXL hXscale hLscale hmuLo hmuHi
    hD hH hR hHR hdelta hdeltaTwo hB hQ hshellTop hcentral hdefect hcap hsmall
  let v : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 N0
  have hv : 0 < v := by
    dsimp only [v]
    exact routeTTrivialBoundaryAmplitudeThreshold_pos L X 60 (by norm_num) hD
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_adjacent_defect_central
      L X 60 T (mu / 120) hX.le (by
        have hden : 0 < (2 ^ (2 * 60) : ℝ) := by positivity
        exact hden.trans ((one_lt_div hden).mp hD))
      hH hR hHR (by positivity : 0 < delta) hB hv hQ hcentral hdefect
      (by simpa only [v] using hcap) (by simpa only [v] using hsmall)
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hmemShell : ∀ j < n,
      lam j ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta) := by
    intro j hj
    rcases hmem j hj with heven | hodd
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans heven.1
      · have hcast := cast_two_mul_add_one_le_two_mul hj
        exact heven.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans hodd.1
      · have hcast := cast_two_mul_add_one_add_one_le_two_mul hj
        exact hodd.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
  have hband : ∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    have hrn := Finset.mem_range.mp (hS hr)
    have hm := hmemShell r hrn
    exact ⟨hm.1, hm.2.trans hshellTop⟩
  have hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T := by
    intro r hr s hs
    have hrb := hband r hr
    have hsb := hband s hs
    rw [abs_le]
    constructor <;> linarith
  have hnT : (n : ℝ) ≤ T := by
    have hnleTwoN : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * n by omega)
    have htwoN0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hscale : ((2 * n : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) * delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta htwoN0
    have hmul : ((2 * n : ℕ) : ℝ) * delta ≤ T := by linarith
    exact hnleTwoN.trans (hscale.trans hmul)
  have hdeltaTop : delta ≤ 2 * T := by
    calc
      delta ≤ 2 := hdeltaTwo
      _ = 2 * 1 := by ring
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hT.le (by norm_num)
  let V : ℝ := (((2 ^ q : ℕ) : ℝ) * v)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hthreshold : routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ V := by
    have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    dsimp only [V, v]
    calc
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 =
          1 * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 := by ring
      _ ≤ ((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 :=
        mul_le_mul_of_nonneg_right hp hv.le
  have halt := hreceiver hX hL hXL hXscale hLscale hmuLo hmuHi hD hV
    hthreshold hdelta hdeltaTop hnT S hS lam hband hgap hdiam
      (by simpa only [V, v] using hlarge)
  refine ⟨lam, S, q, hgap, hS, hq, hband, ?_, ?_, ?_⟩
  · simpa only [v] using hlarge
  · simpa only [v] using hmass
  · simpa only [V, v] using halt

/-- Central reparameterized shell, positive amplitude branch: exact extraction and the full
`mu ≤ 19/9` logarithmic budget force Maynard's second count with no unit-cell alignment. -/
theorem eventually_exists_routeT_adjacentDefect_central_gapSequence_forcedSecond
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X n : ℕ} {mu N0 H R delta : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      T ^ mu = (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (N0 / (2 ^ 120 : ℝ)) →
      0 < H → 0 < R → H ≤ R →
      1 ≤ delta → delta ≤ 2 →
      T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T →
      (∀ y ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta),
        |y| ≤ N0 / (2 * R)) →
      D ≤ ‖∫ y in T..(T + ((2 * n : ℕ) : ℝ) * delta),
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) N0
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N0 R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N0 H
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
      heathBrownWindowRelevantFixedPolylogBound L X 60 N0 1 ≤
        (((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) →
      (n : ℝ) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤
        D / (16 * delta) →
      ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) N0
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        D / (16 * delta * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) *
              (S.card : ℝ) ∧
        (S.card : ℝ) ≤ T * (T ^ mu) ^
          (1 + routeTGapMomentNu -
            2 * routeTAdaptiveCellAmplitude L X 60 N0
              (((2 ^ q : ℕ) : ℝ) *
                routeTTrivialBoundaryAmplitudeThreshold L X 60 N0)) := by
  filter_upwards [
    eventually_exists_routeT_adjacentDefect_central_gapSequence_receiver_above_trivialBoundary
      routeTTrivialBoundaryReceiverLogPower,
    eventually_routeT_amplitudeBand_reparameterizedShell_firstExclusionThreshold hD,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hbridge hthresholdT hT
  intro L X n mu N0 H R delta hX hL hLX hXL hXexact hLscale hmuLo hmuHi
    hN hcomparable hH hR hHR hdelta hdeltaTwo hshellTop hcentral hdefect hcap hsmall
  have hXscale : (X : ℝ) ≤ T ^ mu := by rw [hXexact]
  have hQ : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT.le
  obtain ⟨lam, S, q, hgap, hS, hq, hband, hlarge, hmass, halt⟩ :=
    hbridge hX hL hXL hXscale hLscale hmuLo hmuHi hN hH hR hHR hdelta
      hdeltaTwo hD hQ hshellTop hcentral hdefect hcap hsmall
  let v : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 N0
  let V : ℝ := (((2 ^ q : ℕ) : ℝ) * v)
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N0 V
  have hv : 0 < v := by
    dsimp only [v]
    exact routeTTrivialBoundaryAmplitudeThreshold_pos L X 60 (by norm_num) hN
  have hV : 0 < V := by dsimp only [V]; positivity
  have hbaseThreshold : routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ V := by
    have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    dsimp only [V, v]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hv.le
  have hXscaleTop : (X : ℝ) ≤ T ^ (19 / 9 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hmuHi
    simpa only [hXexact] using hpow
  have hthreshold := hthresholdT hX hL hLX hXscaleTop hN hV hcomparable
    hbaseThreshold
  have hthreshold' : 8 * V * (T ^ mu) ^ (1 - alpha) ≤
      ((D / (2 * Q)) / 2) *
        (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    rw [hXexact]
    simpa only [V, v, alpha, Q] using hthreshold
  have hQreal : 0 < Q := by dsimp only [Q]; exact_mod_cast hQ
  have hsecond : (S.card : ℝ) ≤ T * (T ^ mu) ^
      (1 + routeTGapMomentNu - 2 * alpha) := by
    apply routeT_second_alternative_of_shell_mass hD hV hQreal hdelta hdeltaTwo
      (Real.log_nonneg hT.le) hthreshold'
    · simpa only [V, v, Q] using hmass
    · simpa only [V, v, alpha] using halt
  refine ⟨lam, S, q, hgap, hS, hq, hband, ?_, ?_, ?_⟩
  · simpa only [v] using hlarge
  · simpa only [v] using hmass
  · simpa only [V, v, alpha] using hsecond

/-- Arbitrary central shell form.  Exact adaptive width removes endpoint trimming, while
`delta ≤ 2` converts the selected-band mass to the uniform lower bound `D/(32 Q)`. -/
theorem eventually_exists_routeT_adjacentDefect_centralInterval_forcedSecond
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} {mu N0 H R b : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      T ^ mu = (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (N0 / (2 ^ 120 : ℝ)) →
      0 < H → 0 < R → H ≤ R →
      T + 2 ≤ b → b ≤ 2 * T →
      (∀ y ∈ Set.Icc T b, |y| ≤ N0 / (2 * R)) →
      D ≤ ‖∫ y in T..b,
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) N0
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N0 R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N0 H
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
      heathBrownWindowRelevantFixedPolylogBound L X 60 N0 1 ≤
        (((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) →
      (b - T) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ D / 8 →
      ∃ n : ℕ, ∃ delta : ℝ, ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        0 < n ∧ 1 ≤ delta ∧ delta ≤ 2 ∧
        b = T + ((2 * n : ℕ) : ℝ) * delta ∧
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) N0
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        D / (32 * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) *
              (S.card : ℝ) ∧
        (S.card : ℝ) ≤ T * (T ^ mu) ^
          (1 + routeTGapMomentNu -
            2 * routeTAdaptiveCellAmplitude L X 60 N0
              (((2 ^ q : ℕ) : ℝ) *
                routeTTrivialBoundaryAmplitudeThreshold L X 60 N0)) := by
  filter_upwards [
    eventually_exists_routeT_adjacentDefect_central_gapSequence_forcedSecond hD]
      with T hforced
  intro L X mu N0 H R b hX hL hLX hXL hXexact hLscale hmuLo hmuHi hN
    hcomparable hH hR hHR hlength htop hcentral hdefect hcap hbase
  obtain ⟨n, delta, hn, hdelta, hdeltaTwo, hb⟩ :=
    exists_even_cells_unit_two_of_two_le_length hlength
  have hshellTop : T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T := by
    rw [← hb]
    exact htop
  have hcentral' : ∀ y ∈ Set.Icc T
      (T + ((2 * n : ℕ) : ℝ) * delta), |y| ≤ N0 / (2 * R) := by
    simpa only [← hb] using hcentral
  have hdefect' : D ≤ ‖∫ y in T..(T + ((2 * n : ℕ) : ℝ) * delta),
      heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) N0
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N0 R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N0 H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
    simpa only [← hb] using hdefect
  have hbase' :
      2 * (n : ℝ) * delta *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ D / 8 := by
    rw [hb] at hbase
    push_cast at hbase
    convert hbase using 1
    ring
  have hsmall :
      (n : ℝ) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤
        D / (16 * delta) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * delta)).2
    calc
      (n : ℝ) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 *
          (16 * delta) =
        8 * (2 * (n : ℝ) * delta *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) := by ring
      _ ≤ 8 * (D / 8) := mul_le_mul_of_nonneg_left hbase' (by norm_num)
      _ = D := by ring
  obtain ⟨lam, S, q, hgap, hS, hq, hband, hlarge, hmass, hsecond⟩ :=
    hforced hX hL hLX hXL hXexact hLscale hmuLo hmuHi hN hcomparable hH hR
      hHR hdelta hdeltaTwo hshellTop hcentral' hdefect' hcap hsmall
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hTone : (1 : ℝ) ≤ T := by linarith [hlength, htop]
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast routeTTrivialBoundaryBandCount_pos hTone
  have hmassUniform : D / (32 * Q) ≤ D / (16 * delta * Q) :=
    shellBandMass_uniform_of_width_le_two hD.le
      (zero_lt_one.trans_le hdelta) hdeltaTwo hQ
  refine ⟨n, delta, lam, S, q, hn, hdelta, hdeltaTwo, hb, hgap, hS, hq,
    hband, hlarge, ?_, hsecond⟩
  simpa only [Q] using hmassUniform.trans hmass

end RHTower.Sieve
