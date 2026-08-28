import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalOrdinateShellSpatialBridge
import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalShellAllBandFirstExclusion

noncomputable section
namespace RHTower.Sieve

open Complex Filter Set MeasureTheory

set_option maxHeartbeats 400000

/-- Whole natural-shell equation-(111), assuming exactly the per-band scalar inequalities which
exclude the first receiver. The conclusion has no amplitude factor: base and every positive band
are separately cancelled before the finite bad-set union is taken. -/
theorem eventually_volume_routeT_canonicalNaturalShell_full_forcedSecond_of_band_firstExclusion
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
      let Vbase : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 M
      let Q : ℕ := routeTTrivialBoundaryBandCount T₁
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ Finset.Ico A B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖source ((m : ℝ) + u)‖ ≤ ‖source (c m)‖) →
      (∀ r ∈ Finset.range Q,
        4 * (((2 ^ r : ℕ) : ℝ) * Vbase) * Y ^
            (1 - routeTAdaptiveCellAmplitude L X 60 M
              (((2 ^ r : ℕ) : ℝ) * Vbase)) ≤
          ((D / (2 * (Q : ℝ))) / 2) *
            (Real.log T₁) ^ receiverQ) →
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
  have hbaseEvent :=
    eventually_volume_routeT_canonicalNaturalShell_baseAmplitude heta
  have hbandEvent :=
    eventually_volume_routeT_canonicalNaturalShell_amplitudeBand_forcedSecond
      receiverQ heta
  obtain ⟨Ccap, hcapEvent⟩ := Filter.eventually_atTop.1
    (eventually_heathBrownWindowRelevantFixedPolylogBound_le_shellBandCap_of_exponent_lt_four
      (mu := (11 / 5 : ℝ)) (by norm_num) (by norm_num))
  have hcapHeight : ∀ᶠ T₀ : ℝ in Filter.atTop,
      Ccap ≤ T₀ ^ (8 / 11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 11)).eventually_ge_atTop Ccap
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T₀ : ℝ in Filter.atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T₀ :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hbaseEvent, hbandEvent, hcapHeight, hbaseLarge,
    Filter.eventually_gt_atTop (1 : ℝ)] with
    T₀ hbaseT hbandT hcapHeightT hbaseLargeT hT₀
  intro L A B R H D hL hLX hXL hLscale hAlower hAupper hB hR hH hD
  dsimp only
  intro c hc hmax hfirst
  let X : ℕ := routeTPrimeGapPacketSupport T₀
  let M : ℝ := routeTPrimeGapPacketBase T₀
  let T₁ : ℝ := A
  let mu₁ : ℝ := routeTHeightMatchedExponent T₀ (8 / 5) T₁
  let Y : ℝ := T₀ ^ (8 / 5 : ℝ)
  let source : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T₁ (mu₁ / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let Vbase : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 M
  let Q : ℕ := routeTTrivialBoundaryBandCount T₁
  let spatial : ℝ := T₀ ^ eta * T₁ * Y ^ routeTGapMomentNu *
    (1 + 2 * (1 + Real.log ((2 * A : ℕ) : ℝ)))
  let Kbase : ℝ := (32 * spatial) / (D / 2) ^ 2
  let Kband : ℕ → ℝ := fun _ =>
    2 * ((128 * spatial) / ((D / (2 * (Q : ℝ))) / 2) ^ 2)
  have hT₀pos : 0 < T₀ := zero_lt_one.trans hT₀
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hMcut : 1 < M / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [M]
    linarith
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := Real.strictMono_rpow_of_base_gt_one hT₀
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hAlower
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact routeTTrivialBoundaryBandCount_pos hT₁.le
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hVbase : 0 < Vbase := by
    dsimp only [Vbase]
    exact routeTTrivialBoundaryAmplitudeThreshold_pos L X 60 (by norm_num) hMcut
  have hX : 1 < X := by
    have hceil : 3 * M ≤ (X : ℝ) := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hceilLower : 3 * M ≤ (X : ℝ) := by
    dsimp only [X, M, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * M + 1 := by
    dsimp only [X, M, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXN : (X : ℝ) ≤ 4 * M := by linarith
  have hNX : M ≤ (X : ℝ) := by linarith
  have hYeq : Y = 4 * M := by
    dsimp only [Y, M, routeTPrimeGapPacketBase]
    field_simp
  have hXscale : (X : ℝ) ≤ T₁ ^ (11 / 5 : ℝ) := by
    have hsupportY : (X : ℝ) ≤ Y := by rw [hYeq]; exact hXN
    have hexact : T₁ ^ mu₁ = Y := by
      dsimp only [mu₁, Y]
      exact rpow_routeTHeightMatchedExponent hT₀ hT₁
    have hmuHi : mu₁ ≤ 11 / 5 := by
      dsimp only [mu₁]
      exact (routeTHeightMatchedExponent_mem_fourThird_elevenFifths
        hT₀ hAlower hAupper).2
    have hYscale : Y ≤ T₁ ^ (11 / 5 : ℝ) := by
      rw [← hexact]
      exact Real.rpow_le_rpow_of_exponent_le hT₁.le hmuHi
    exact hsupportY.trans hYscale
  have hpolyCap : heathBrownWindowRelevantFixedPolylogBound L X 60 M 1 <
      ((2 ^ Q : ℕ) : ℝ) * Vbase := by
    simpa only [Q, Vbase] using
      (hcapEvent T₁ (hcapHeightT.trans hAlower)
        (N := M) (L := L) (X := X) hL hX
        (by simpa only [X] using hLX) hXN hNX hXscale hMcut)
  have hcap : ∀ m ∈ Finset.Ico A B,
      ‖source (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * Vbase := by
    intro m hm
    have hnorm : ‖source (c m)‖ ≤
        heathBrownWindowRelevantFixedPolylogBound L X 60 M 1 := by
      dsimp only [source]
      convert
        (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
          L X 60 hX.le T₁ (mu₁ / 120) M 1 (c m) hMpos (by norm_num)) using 1
      norm_num
    exact hnorm.trans_lt hpolyCap
  have hcontinuous : Continuous source := by
    dsimp only [source]
    exact continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X 60 T₁ (mu₁ / 120) M 1
  have hbaseMeasure :
      (volume.restrict (Set.Icc M (2 * M))).real
        {lambda | D / 2 ≤
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellBaseAmplitudeSet (Finset.Ico A B) source c Vbase)
            source lambda 1 R H 1‖} ≤ Kbase := by
    have hout := hbaseT (L := L) (A := A) (B := B) (R := R) (H := H)
      (D := D / 2) hLX hAlower hAupper hB hR hH (by positivity) c
      (by simpa only [source, X, M, T₁, mu₁] using hmax)
    simpa only [X, M, T₁, mu₁, Y, source, Vbase, spatial, Kbase,
      mul_assoc] using hout
  have hbandMeasure : ∀ r ∈ Finset.range Q,
      (volume.restrict (Set.Icc M (2 * M))).real
        {lambda | D / (2 * (Q : ℝ)) ≤
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellAmplitudeBand (Finset.Ico A B) source c
              (((2 ^ r : ℕ) : ℝ) * Vbase))
            source lambda 1 R H 1‖} ≤ Kband r := by
    intro r hr
    let Vr : ℝ := ((2 ^ r : ℕ) : ℝ) * Vbase
    have hVr : 0 < Vr := by dsimp only [Vr]; positivity
    have hVbaseVr : Vbase ≤ Vr := by
      have hpNat : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      have hp : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hpNat
      calc
        Vbase = 1 * Vbase := by ring
        _ ≤ ((2 ^ r : ℕ) : ℝ) * Vbase :=
          mul_le_mul_of_nonneg_right hp hVbase.le
        _ = Vr := rfl
    have hDb : 0 < D / (2 * (Q : ℝ)) :=
      div_pos hD (mul_pos (by norm_num) hQreal)
    have hout := hbandT (L := L) (A := A) (B := B) (R := R) (H := H)
      (D := D / (2 * (Q : ℝ))) (V := Vr)
      hL hLX hXL hLscale hAlower hAupper hB hR hH hDb hVr
      (by simpa only [X, M, Vbase, Vr] using hVbaseVr)
      (by simpa only [X, M, T₁, Y, Q, Vbase, Vr] using hfirst r hr)
      c hc (by simpa only [source, X, M, T₁, mu₁] using hmax)
    simpa only [X, M, T₁, mu₁, Y, source, Vbase, Q, Vr, spatial, Kband,
      mul_assoc] using hout
  have hassembly :=
    measureReal_maynardFixedAmbientPhysicalDefectPacket_full_le_base_add_sum_bands
      (x := M) (N := 1) (R := R) (H := H) (v := Vbase) (D := D) (Q := Q)
      hM (by norm_num) hR hH hVbase hD hQ (Finset.Ico A B) source hcontinuous c
      hcap Kbase Kband hbaseMeasure hbandMeasure
  simpa only [X, M, T₁, mu₁, Y, source, Vbase, Q, spatial, Kbase, Kband]
    using hassembly

end RHTower.Sieve
