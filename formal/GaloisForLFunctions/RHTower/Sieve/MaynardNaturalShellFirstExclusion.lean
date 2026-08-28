import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryShellCapStructural

noncomputable section
namespace RHTower.Sieve

open Filter

/-- Exact-boundary first-alternative exclusion at the receiver scale of a height-matched natural
shell. -/
theorem eventually_routeT_canonicalNaturalShell_amplitudeBand_firstExclusionThreshold
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T₀ : ℝ in atTop,
      ∀ {L A : ℕ} {V : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T₀ →
      T₀ ^ (8 / 11 : ℝ) ≤ (A : ℝ) →
      (A : ℝ) ≤ T₀ →
      0 < V →
      routeTTrivialBoundaryAmplitudeThreshold L (routeTPrimeGapPacketSupport T₀) 60
        (routeTPrimeGapPacketBase T₀) ≤ V →
      8 * V * (T₀ ^ (8 / 5 : ℝ)) ^
          (1 - routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T₀) 60
            (routeTPrimeGapPacketBase T₀) V) ≤
        ((D / (2 * (routeTTrivialBoundaryBandCount (A : ℝ) : ℝ))) / 2) *
          (Real.log (A : ℝ)) ^ routeTTrivialBoundaryReceiverLogPower := by
  obtain ⟨C0, hcost⟩ := Filter.eventually_atTop.1
    (eventually_thirtytwo_shellBandCount_selectorCost_le_receiverLog_elevenFifths hD)
  have hheight : ∀ᶠ T₀ : ℝ in atTop, C0 ≤ T₀ ^ (8 / 11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 11)).eventually_ge_atTop C0
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T₀ : ℝ in atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T₀ :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hheight, hbaseLarge, Filter.eventually_gt_atTop (1 : ℝ)] with
    T₀ hheightT hbase hT₀
  intro L A V hL hLX hAlower hAupper hV htrivial
  let X : ℕ := routeTPrimeGapPacketSupport T₀
  let M : ℝ := routeTPrimeGapPacketBase T₀
  let T₁ : ℝ := A
  let Y : ℝ := T₀ ^ (8 / 5 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 M V
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  let Q : ℝ := routeTTrivialBoundaryBandCount T₁
  have hT₀pos : 0 < T₀ := zero_lt_one.trans hT₀
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := Real.strictMono_rpow_of_base_gt_one hT₀
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hAlower
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hMcut : 1 < M / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [M]
    linarith
  have hX : 1 < X := by
    have hceil : 3 * M ≤ (X : ℝ) := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hXone : 1 ≤ X := hX.le
  have hsupport := routeTPrimeGapPacketSupport_comparable_eligibilityScale
    hT₀pos (by simpa only [M] using hM)
  have hSupport : (X : ℝ) ≤ Y := by
    simpa only [X, Y] using hsupport.1
  have hLowerComparable : Y ≤ kappa * (M / (2 ^ 120 : ℝ)) := by
    have hYM : Y = 4 * M := by
      dsimp only [Y, M, routeTPrimeGapPacketBase]
      field_simp
    rw [hYM]
    dsimp only [kappa]
    ring_nf
    exact le_rfl
  have halpha : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hMcut (by simpa only [X, M] using htrivial)
  have hA : V * Y ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hMcut hV hY
          (by dsimp only [kappa]; norm_num) hSupport hLowerComparable halpha)
  have hXscale : (X : ℝ) ≤ T₁ ^ (11 / 5 : ℝ) := by
    have hYscale : Y ≤ T₁ ^ (11 / 5 : ℝ) := by
      have hexact : T₁ ^ routeTHeightMatchedExponent T₀ (8 / 5) T₁ = Y := by
        dsimp only [Y]
        exact rpow_routeTHeightMatchedExponent hT₀ hT₁
      rw [← hexact]
      exact Real.rpow_le_rpow_of_exponent_le hT₁.le
        (routeTHeightMatchedExponent_mem_fourThird_elevenFifths
          hT₀ hAlower hAupper).2
    exact hSupport.trans hYscale
  have hcostT := hcost T₁ (hheightT.trans hAlower)
  have hcostBound :
      32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [Q, kappa] using hcostT L X hXone
      (by simpa only [X] using hLX) hXscale
  have hQnat : 0 < routeTTrivialBoundaryBandCount T₁ :=
    routeTTrivialBoundaryBandCount_pos hT₁.le
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  have hfull : 32 * Q * (V * Y ^ (1 - alpha)) ≤
      D * (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      32 * Q * (V * Y ^ (1 - alpha)) ≤
          32 * Q * (heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower := hcostBound
  have hden : 0 < 4 * Q := by positivity
  have hdiv : 8 * (V * Y ^ (1 - alpha)) ≤
      (D * (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      8 * (V * Y ^ (1 - alpha)) * (4 * Q) =
          32 * Q * (V * Y ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower := hfull
  have htarget :
      (D * (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) =
        ((D / (2 * Q)) / 2) *
          (Real.log T₁) ^ routeTTrivialBoundaryReceiverLogPower := by
    field_simp
    ring
  rw [htarget] at hdiv
  simpa only [X, M, T₁, Y, alpha, Q, mul_assoc] using hdiv

end RHTower.Sieve
