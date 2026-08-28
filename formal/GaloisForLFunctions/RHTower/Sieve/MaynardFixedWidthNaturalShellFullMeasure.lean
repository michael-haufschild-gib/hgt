import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalShellSelectorMeasure

noncomputable section
namespace RHTower.Sieve

open Complex Filter Set MeasureTheory

/-- Literal fixed-width natural-shell bad-measure bound. Rung, ordinate-shell, amplitude-band,
and degree-60 selector losses are all discharged internally. -/
theorem eventually_volume_routeT_fixedWidth_canonicalNaturalShell_full_forcedSecond
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T₀ : ℝ in Filter.atTop,
      ∀ {L A B : ℕ} {R H H0 U W : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T₀ →
      routeTPrimeGapPacketSupport T₀ < (L + 1) ^ 60 →
      (L : ℝ) ≤ T₀ ^ (2 / 75 : ℝ) →
      T₀ ^ (8 / 11 : ℝ) ≤ (A : ℝ) →
      (A : ℝ) ≤ T₀ → B ≤ 2 * A →
      0 < R → 0 < H →
      0 < H0 → H0 ≤ 1 / 4 →
      routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T₀) ≤ H0 →
      1 ≤ U → U ≤ W → W ≤ T₀ →
      let X : ℕ := routeTPrimeGapPacketSupport T₀
      let M : ℝ := routeTPrimeGapPacketBase T₀
      let T₁ : ℝ := A
      let mu₁ : ℝ := routeTHeightMatchedExponent T₀ (8 / 5) T₁
      let Y : ℝ := T₀ ^ (8 / 5 : ℝ)
      let D : ℝ := ((routeTFixedWidthPacketDefectFloor /
        (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
          (routeTOrdinateShellCount U W : ℝ)
      let source : ℝ → ℂ := fun y =>
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T₁ (mu₁ / 120) M
          ((1 : ℂ) + (y : ℝ) * Complex.I)
      let Q : ℕ := routeTTrivialBoundaryBandCount T₁
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ Finset.Ico A B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖source ((m : ℝ) + u)‖ ≤ ‖source (c m)‖) →
      let spatial : ℝ := T₀ ^ eta * T₁ * Y ^ routeTGapMomentNu *
        (1 + 2 * (1 + Real.log ((2 * A : ℕ) : ℝ)))
      (volume.restrict (Set.Icc M (2 * M))).real
          {lambda | D ≤
            ‖maynardFixedAmbientPhysicalDefectPacket (Finset.Ico A B)
              source lambda 1 R H 1‖} ≤
        (32 * spatial) / (D / 2) ^ 2 +
          ∑ _r ∈ Finset.range Q,
            2 * ((128 * spatial) /
              ((D / (2 * (Q : ℝ))) / 2) ^ 2) := by
  have hmeasure :=
    eventually_volume_routeT_canonicalNaturalShell_full_forcedSecond_of_selectorCost
      routeTFixedWidthShellReceiverLogPower heta
  have hselector :=
    eventually_routeT_fixedWidth_rung_shell_band_selectorCost_le_receiverLog
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T₀ : ℝ in Filter.atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T₀ :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hmeasure, hselector, hbaseLarge,
    Filter.eventually_gt_atTop (1 : ℝ)] with
    T₀ hmeasureT hselectorT hbaseLargeT hT₀
  intro L A B R H H0 U W hL hLX hXL hLscale hAlower hAupper hB hR hH
    hH0 hH0quarter hwidth hU hUW hWT₀
  dsimp only
  intro c hc hmax
  let X : ℕ := routeTPrimeGapPacketSupport T₀
  let M : ℝ := routeTPrimeGapPacketBase T₀
  let T₁ : ℝ := A
  let Y : ℝ := T₀ ^ (8 / 5 : ℝ)
  let D : ℝ := ((routeTFixedWidthPacketDefectFloor /
    (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
      (routeTOrdinateShellCount U W : ℝ)
  let Q : ℕ := routeTTrivialBoundaryBandCount T₁
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := Real.strictMono_rpow_of_base_gt_one hT₀
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hAlower
  have hM : 1 ≤ M := by
    dsimp only [M]
    linarith
  have hX : 1 < X := by
    have hceil : 3 * M ≤ (X : ℝ) := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hXscale : (X : ℝ) ≤ T₁ ^ (11 / 5 : ℝ) := by
    have hsupport := routeTPrimeGapPacketSupport_comparable_eligibilityScale
      (zero_lt_one.trans hT₀) (by simpa only [M] using hM)
    have hexact : T₁ ^ routeTHeightMatchedExponent T₀ (8 / 5) T₁ = Y := by
      dsimp only [Y]
      exact rpow_routeTHeightMatchedExponent hT₀ hT₁
    have hmuHi := (routeTHeightMatchedExponent_mem_fourThird_elevenFifths
      hT₀ hAlower hAupper).2
    have hYscale : Y ≤ T₁ ^ (11 / 5 : ℝ) := by
      rw [← hexact]
      exact Real.rpow_le_rpow_of_exponent_le hT₁.le hmuHi
    have hsupport' : (X : ℝ) ≤ Y := by
      simpa only [X, Y] using hsupport.1
    exact hsupport'.trans hYscale
  have hRcount : 0 < (routeTFixedWidthRungCount H0 : ℝ) := by
    exact_mod_cast routeTFixedWidthRungCount_pos hH0 hH0quarter
  have hScount : 0 < (routeTOrdinateShellCount U W : ℝ) := by
    exact_mod_cast routeTOrdinateShellCount_pos (zero_lt_one.trans_le hU) hUW
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos
      (div_pos (div_pos routeTFixedWidthPacketDefectFloor_pos hRcount) (by norm_num))
      hScount
  have hselectorStrong := hselectorT (T₁ := T₁) (H0 := H0) (U := U) (V := W)
    (L := L) (X := X) hAlower hH0 hH0quarter
      (by simpa only [M] using hwidth) hU hUW hWT₀ hX.le
      (by simpa only [X] using hLX) hXscale
  have hcost0 : 0 ≤
      32 * (Q : ℝ) * heathBrownEligibleBoxCost L X 60 *
        (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg Q))
        (heathBrownEligibleBoxCost_pos L X 60 (by norm_num)).le)
      (Real.rpow_nonneg (by positivity) _)
  have hselectorWeak :
      32 * (Q : ℝ) * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T₁) ^ routeTFixedWidthShellReceiverLogPower := by
    calc
      32 * (Q : ℝ) * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent =
        1 * (32 * (Q : ℝ) * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent) := by ring
      _ ≤ (4 / 3 : ℝ) * (32 * (Q : ℝ) * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_right (by norm_num) hcost0
      _ = 32 * (Q : ℝ) * (4 / 3 : ℝ) * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T₁) ^ routeTFixedWidthShellReceiverLogPower := by
        simpa only [D, Q, T₁] using hselectorStrong
  have hout := hmeasureT (L := L) (A := A) (B := B) (R := R) (H := H)
    (D := D) hL hLX hXL hLscale hAlower hAupper hB hR hH hD c hc
      (by simpa only using hmax)
      (by simpa only [X, T₁, Q] using hselectorWeak)
  simpa only [X, M, T₁, Y, D, Q] using hout

end RHTower.Sieve
