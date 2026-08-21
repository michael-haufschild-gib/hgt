import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryGapSequence
import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCanonicalCutoff

noncomputable section
namespace RHTower.Sieve

open Filter Topology

/-- Every fixed power of the shell logarithm is subpower uniformly through `mu ≤ 19/9`. -/
theorem eventually_routeTShellLogBase_pow_absorbed
    (q : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop,
      ∀ X : ℕ, 1 ≤ X → (X : ℝ) ≤ T ^ (19 / 9 : ℝ) →
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ q ≤ T ^ eta := by
  let D : ℝ := routeTTrivialBoundaryShellLogBaseConstant
  have hD0 : 0 < D := by
    dsimp only [D, routeTTrivialBoundaryShellLogBaseConstant]
    positivity
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := D ^ q) (α := (0 : ℝ)) (β := eta) q heta
  filter_upwards [hdom, Filter.eventually_ge_atTop (1 : ℝ)] with T hdomT hT
  intro X hX hXscale
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have habsLogT : |Real.log T| = Real.log T := abs_of_nonneg hlogT
  have hBupper : B ≤ D * (1 + |Real.log T|) := by
    rw [habsLogT]
    simpa only [B, D] using routeTShellLogBase_le_one_add_log hT hX hXscale
  have hMone : (1 : ℝ) ≤ (((2 ^ 120 * X : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hMone]
  have hpow : B ^ q ≤ (D * (1 + |Real.log T|)) ^ q :=
    pow_le_pow_left₀ hB0 hBupper q
  have hdomT' : D ^ q * (1 + |Real.log T|) ^ q ≤ T ^ eta := by
    simpa only [Real.rpow_zero, mul_one] using hdomT
  change B ^ q ≤ T ^ eta
  exact hpow.trans (by simpa only [mul_pow] using hdomT')

/-- Complete frozen-source polylog envelope remains subpower after exact shell reparameterization. -/
theorem eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_shell_absorbed
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (N : ℝ) (L X : ℕ), 1 ≤ N → 1 ≤ L → 1 ≤ X → L ≤ X →
        (X : ℝ) ≤ 4 * N → (X : ℝ) ≤ T ^ (19 / 9 : ℝ) →
        heathBrownWindowRelevantFixedPolylogBound L X 60 N 1 ≤ T ^ eta := by
  let eps : ℝ := eta / 5
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have h60 := eventually_routeTShellLogBase_pow_absorbed 60 heps
  have h1 := eventually_routeTShellLogBase_pow_absorbed 1 heps
  have hE := eventually_routeTShellLogBase_pow_absorbed (2 ^ 121 - 1) heps
  have hconst : ∀ᶠ T : ℝ in atTop,
      routeTPrimeGapPacketPolylogConstant ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop routeTPrimeGapPacketPolylogConstant
  filter_upwards [h60, h1, hE, hconst, Filter.eventually_ge_atTop (1 : ℝ)] with
    T h60T h1T hET hconstT hT
  intro N L X hN _hL hX hLX hXN hXscale
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  let P : ℝ := T ^ eps
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hB60 : B ^ 60 ≤ P := by simpa only [B, P] using h60T X hX hXscale
  have hB1 : B ≤ P := by simpa only [B, P, pow_one] using h1T X hX hXscale
  have hBE : B ^ (2 ^ 121 - 1) ≤ P := by
    simpa only [B, P] using hET X hX hXscale
  have hM1 : (1 : ℝ) ≤ (((2 ^ 120 * X : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hM1]
  have hB600 : 0 ≤ B ^ 60 := pow_nonneg hB0 _
  have hBE0 : 0 ≤ B ^ (2 ^ 121 - 1) := pow_nonneg hB0 _
  have hP0 : 0 ≤ P := by dsimp only [P]; exact Real.rpow_nonneg hT0.le _
  have hC0 : 0 ≤ routeTPrimeGapPacketPolylogConstant := by
    unfold routeTPrimeGapPacketPolylogConstant
    positivity
  have h01 : routeTPrimeGapPacketPolylogConstant * B ^ 60 ≤ P * P :=
    mul_le_mul hconstT hB60 hB600 hP0
  have h012 : routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 ≤
      P * P * P :=
    mul_le_mul h01 hB60 hB600 (mul_nonneg hP0 hP0)
  have h0123 : routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B ≤
      P * P * P * P :=
    mul_le_mul h012 hB1 hB0 (mul_nonneg (mul_nonneg hP0 hP0) hP0)
  have hprod :
      routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B *
          B ^ (2 ^ 121 - 1) ≤ P * P * P * P * P :=
    mul_le_mul h0123 hBE hBE0
      (mul_nonneg (mul_nonneg (mul_nonneg hP0 hP0) hP0) hP0)
  have hmajor : heathBrownWindowRelevantFixedPolylogBound X X 60 N 1 ≤
      routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B *
        B ^ (2 ^ 121 - 1) := by
    simpa only [B] using
      heathBrownWindowRelevantFixedPolylogBound_sixty_comparable hN hX hXN
  have hmono := heathBrownWindowRelevantFixedPolylogBound_mono_left
    (k := 60) (N := N) (sigma := 1) hX (zero_le_one.trans hN) hLX
  calc
    heathBrownWindowRelevantFixedPolylogBound L X 60 N 1 ≤
        heathBrownWindowRelevantFixedPolylogBound X X 60 N 1 := hmono
    _ ≤ routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B *
        B ^ (2 ^ 121 - 1) := hmajor
    _ ≤ P * P * P * P * P := hprod
    _ = P ^ 5 := by ring
    _ = T ^ (eps * 5) := by
      dsimp only [P]
      rw [← Real.rpow_natCast (T ^ eps) 5, ← Real.rpow_mul hT0.le]
      norm_num
    _ = T ^ eta := by
      congr 1
      dsimp only [eps]
      ring

/-- Canonical `O(log T)` amplitude depth covers the complete frozen-source envelope on every
reparameterized shell through `mu ≤ 19/9`. -/
theorem eventually_heathBrownWindowRelevantFixedPolylogBound_le_shellBandCap :
    ∀ᶠ T : ℝ in atTop,
      ∀ {N : ℝ} {L X : ℕ},
      1 ≤ L → 1 < X → L ≤ X →
      (X : ℝ) ≤ 4 * N → N ≤ (X : ℝ) →
      (X : ℝ) ≤ T ^ (19 / 9 : ℝ) →
      1 < N / (2 ^ 120 : ℝ) →
      heathBrownWindowRelevantFixedPolylogBound L X 60 N 1 ≤
        ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N := by
  have hPevent :=
    eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_shell_absorbed
      (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hPevent, Filter.eventually_ge_atTop (1 : ℝ)] with T hPT hT
  intro N L X hL hX hLX hXN hNX hXscale hDbase
  let d : ℝ := N / (2 ^ 120 : ℝ)
  let C : ℝ := heathBrownEligibleBoxCost L X 60
  let a : ℝ := (1 + routeTGapMomentNu) / 2 - 1
  let V : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 N
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 N 1
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hd : 1 < d := by simpa only [d] using hDbase
  have hdpos : 0 < d := zero_lt_one.trans hd
  have hNpos : 0 < N := by
    have hden : 0 < (2 ^ 120 : ℝ) := by positivity
    exact hden.trans ((one_lt_div hden).mp hDbase)
  have hNone : 1 ≤ N := by
    have hdN : d ≤ N := by
      dsimp only [d]
      exact div_le_self hNpos.le (by norm_num)
    exact hd.le.trans hdN
  have hP : P ≤ T ^ (1 / 2 : ℝ) := by
    simpa only [P] using hPT N L X hNone hL hX.le hLX hXN hXscale
  have hdT : d ≤ T ^ (19 / 9 : ℝ) := by
    have hdN : d ≤ N := by
      dsimp only [d]
      exact div_le_self hNpos.le (by norm_num)
    exact hdN.trans (hNX.trans hXscale)
  have haLower : -(1 : ℝ) / 2 ≤ a := by
    dsimp only [a]
    linarith [routeTGapMomentNu_pos]
  have hscale :
      (T ^ (19 / 9 : ℝ)) ^ (-(1 : ℝ) / 2) ≤ d ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hdpos hdT (by norm_num)
  have hscaleEq :
      (T ^ (19 / 9 : ℝ)) ^ (-(1 : ℝ) / 2) = T ^ (-(19 : ℝ) / 18) := by
    rw [← Real.rpow_mul hTpos.le]
    congr 1
    ring
  have hdexp : d ^ (-(1 : ℝ) / 2) ≤ d ^ a :=
    Real.rpow_le_rpow_of_exponent_le hd.le haLower
  have hC : 1 ≤ C := by
    have hcard : 0 < Fintype.card (HeathBrownBoxChoice L X 60) :=
      Fintype.card_pos_iff.mpr (nonempty_heathBrownBoxChoice L X 60 (by norm_num))
    have hcardOne : (1 : ℝ) ≤ Fintype.card (HeathBrownBoxChoice L X 60) := by
      exact_mod_cast hcard
    dsimp only [C, heathBrownEligibleBoxCost]
    exact one_le_mul_of_one_le_of_one_le hcardOne (by norm_num)
  have hVlower : T ^ (-(19 : ℝ) / 18) ≤ V := by
    calc
      T ^ (-(19 : ℝ) / 18) =
          (T ^ (19 / 9 : ℝ)) ^ (-(1 : ℝ) / 2) := hscaleEq.symm
      _ ≤ d ^ (-(1 : ℝ) / 2) := hscale
      _ ≤ d ^ a := hdexp
      _ ≤ C * d ^ a := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC
          (Real.rpow_nonneg hdpos.le a)
      _ = V := by rfl
  have htwo := two_mul_sq_le_two_pow_routeTTrivialBoundaryBandCount hTpos
  have hproduct :
      (2 * T ^ 2) * T ^ (-(19 : ℝ) / 18) ≤
        ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) * V :=
    mul_le_mul htwo hVlower (Real.rpow_nonneg (zero_le_one.trans hT) _)
      (by positivity)
  have hleft :
      (2 * T ^ 2) * T ^ (-(19 : ℝ) / 18) =
        2 * T ^ (17 / 18 : ℝ) := by
    calc
      (2 * T ^ 2) * T ^ (-(19 : ℝ) / 18) =
          2 * (T ^ (2 : ℝ) * T ^ (-(19 : ℝ) / 18)) := by
        rw [Real.rpow_two]
        ring
      _ = 2 * T ^ ((2 : ℝ) + (-(19 : ℝ) / 18)) := by
        rw [Real.rpow_add hTpos]
      _ = 2 * T ^ (17 / 18 : ℝ) := by norm_num
  have hhalf : T ^ (1 / 2 : ℝ) ≤ T ^ (17 / 18 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hdouble : T ^ (17 / 18 : ℝ) ≤ 2 * T ^ (17 / 18 : ℝ) := by
    have hpow0 : 0 ≤ T ^ (17 / 18 : ℝ) :=
      Real.rpow_nonneg (zero_le_one.trans hT) _
    linarith
  calc
    heathBrownWindowRelevantFixedPolylogBound L X 60 N 1 = P := rfl
    _ ≤ T ^ (1 / 2 : ℝ) := hP
    _ ≤ T ^ (17 / 18 : ℝ) := hhalf
    _ ≤ 2 * T ^ (17 / 18 : ℝ) := hdouble
    _ = (2 * T ^ 2) * T ^ (-(19 : ℝ) / 18) := hleft.symm
    _ ≤ ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) * V := hproduct
    _ = ((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
        routeTTrivialBoundaryAmplitudeThreshold L X 60 N := rfl

end RHTower.Sieve
