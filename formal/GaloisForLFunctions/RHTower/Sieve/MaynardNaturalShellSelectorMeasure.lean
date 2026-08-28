import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalShellFullMeasure
import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalShellAllBandFirstExclusion

noncomputable section
namespace RHTower.Sieve

open Complex Filter Set MeasureTheory

/-- Whole natural-shell equation-(111) from one literal selector budget. -/
theorem eventually_volume_routeT_canonicalNaturalShell_full_forcedSecond_of_selectorCost
    (receiverQ : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T₀ : ℝ in Filter.atTop,
      ∀ {L A B : ℕ} {R H D : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T₀ →
      routeTPrimeGapPacketSupport T₀ < (L + 1) ^ 60 →
      (L : ℝ) ≤ T₀ ^ (2 / 75 : ℝ) →
      T₀ ^ (8 / 11 : ℝ) ≤ (A : ℝ) →
      (A : ℝ) ≤ T₀ → B ≤ 2 * A →
      0 < R → 0 < H → 0 < D →
      let X : ℕ := routeTPrimeGapPacketSupport T₀
      let M : ℝ := routeTPrimeGapPacketBase T₀
      let T₁ : ℝ := A
      let mu₁ : ℝ := routeTHeightMatchedExponent T₀ (8 / 5) T₁
      let Y : ℝ := T₀ ^ (8 / 5 : ℝ)
      let source : ℝ → ℂ := fun y =>
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T₁ (mu₁ / 120) M
          ((1 : ℂ) + (y : ℝ) * Complex.I)
      let Q : ℕ := routeTTrivialBoundaryBandCount T₁
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ Finset.Ico A B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖source ((m : ℝ) + u)‖ ≤ ‖source (c m)‖) →
      (32 * (Q : ℝ) * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T₁) ^ receiverQ) →
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
  have hwhole :=
    eventually_volume_routeT_canonicalNaturalShell_full_forcedSecond_of_band_firstExclusion
      receiverQ heta
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T₀ : ℝ in Filter.atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T₀ :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hwhole, hbaseLarge, Filter.eventually_gt_atTop (1 : ℝ)] with
    T₀ hwholeT hbase hT₀
  intro L A B R H D hL hLX hXL hLscale hAlower hAupper hB hR hH hD
  dsimp only
  intro c hc hmax hselector
  apply hwholeT hL hLX hXL hLscale hAlower hAupper hB hR hH hD c hc hmax
  have hMcut : 1 < routeTPrimeGapPacketBase T₀ / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    linarith
  exact routeT_canonicalNaturalShell_all_amplitudeBands_firstExclusion_of_selectorCost
    receiverQ hT₀ hAlower hMcut hselector

end RHTower.Sieve
