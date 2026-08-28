import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalShellFirstExclusion

noncomputable section
namespace RHTower.Sieve

open Filter

/-- One literal selector budget excludes the first receiver simultaneously on every canonical
trivial-boundary amplitude band of a natural shell. -/
theorem routeT_canonicalNaturalShell_all_amplitudeBands_firstExclusion_of_selectorCost
    (receiverQ : ℕ) {T₀ D : ℝ} (hT₀ : 1 < T₀) {L A : ℕ}
    (hAlower : T₀ ^ (8 / 11 : ℝ) ≤ (A : ℝ))
    (hMcut : 1 < routeTPrimeGapPacketBase T₀ / (2 ^ 120 : ℝ))
    (hselector :
      32 * (routeTTrivialBoundaryBandCount (A : ℝ) : ℝ) *
          heathBrownEligibleBoxCost L (routeTPrimeGapPacketSupport T₀) 60 *
            (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log (A : ℝ)) ^ receiverQ) :
    ∀ r ∈ Finset.range (routeTTrivialBoundaryBandCount (A : ℝ)),
      4 * (((2 ^ r : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L
            (routeTPrimeGapPacketSupport T₀) 60 (routeTPrimeGapPacketBase T₀)) *
        (T₀ ^ (8 / 5 : ℝ)) ^
          (1 - routeTAdaptiveCellAmplitude L (routeTPrimeGapPacketSupport T₀) 60
            (routeTPrimeGapPacketBase T₀)
              (((2 ^ r : ℕ) : ℝ) *
                routeTTrivialBoundaryAmplitudeThreshold L
                  (routeTPrimeGapPacketSupport T₀) 60
                    (routeTPrimeGapPacketBase T₀))) ≤
      ((D / (2 * (routeTTrivialBoundaryBandCount (A : ℝ) : ℝ))) / 2) *
        (Real.log (A : ℝ)) ^ receiverQ := by
  let X : ℕ := routeTPrimeGapPacketSupport T₀
  let M : ℝ := routeTPrimeGapPacketBase T₀
  let T₁ : ℝ := A
  let Y : ℝ := T₀ ^ (8 / 5 : ℝ)
  let Vbase : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 M
  let Q : ℝ := routeTTrivialBoundaryBandCount T₁
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  have hT₀pos : 0 < T₀ := zero_lt_one.trans hT₀
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := Real.strictMono_rpow_of_base_gt_one hT₀
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hAlower
  have hMcut' : 1 < M / (2 ^ 120 : ℝ) := by simpa only [M] using hMcut
  intro r hr
  let Vr : ℝ := ((2 ^ r : ℕ) : ℝ) * Vbase
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 M Vr
  have hMpos : 0 < M := by
    have hden : 0 < (2 ^ 120 : ℝ) := by positivity
    exact hden.trans ((one_lt_div hden).mp hMcut')
  have hX : 1 < X := by
    have hceil : 3 * M ≤ (X : ℝ) := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hVbase : 0 < Vbase := by
    dsimp only [Vbase]
    exact routeTTrivialBoundaryAmplitudeThreshold_pos L X 60 (by norm_num) hMcut'
  have hVr : 0 < Vr := by dsimp only [Vr]; positivity
  have hVbaseVr : Vbase ≤ Vr := by
    have hpNat : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hp : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hpNat
    calc
      Vbase = 1 * Vbase := by ring
      _ ≤ ((2 ^ r : ℕ) : ℝ) * Vbase :=
        mul_le_mul_of_nonneg_right hp hVbase.le
      _ = Vr := rfl
  have hSupport : (X : ℝ) ≤ Y := by
    have hceilUpper : (X : ℝ) < 3 * M + 1 := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.ceil_lt_add_one (by positivity)
    have hYM : Y = 4 * M := by
      dsimp only [Y, M, routeTPrimeGapPacketBase]
      field_simp
    rw [hYM]
    linarith
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
      L X 60 (by norm_num) hX hMcut'
        (by simpa only [Vr, Vbase] using hVbaseVr)
  have hA : Vr * Y ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hMcut' hVr hY
          (by dsimp only [kappa]; norm_num) hSupport hLowerComparable halpha)
  have hQnat : 0 < routeTTrivialBoundaryBandCount T₁ :=
    routeTTrivialBoundaryBandCount_pos hT₁.le
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  have hselector' :
      32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T₁) ^ receiverQ := by
    simpa only [Q, X, T₁, kappa] using hselector
  have hfull : 32 * Q * (Vr * Y ^ (1 - alpha)) ≤
      D * (Real.log T₁) ^ receiverQ := by
    calc
      32 * Q * (Vr * Y ^ (1 - alpha)) ≤
          32 * Q * (heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T₁) ^ receiverQ := hselector'
  have hden : 0 < 4 * Q := by positivity
  have hdiv : 8 * (Vr * Y ^ (1 - alpha)) ≤
      (D * (Real.log T₁) ^ receiverQ) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      8 * (Vr * Y ^ (1 - alpha)) * (4 * Q) =
          32 * Q * (Vr * Y ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T₁) ^ receiverQ := hfull
  have hfourEight : 4 * (Vr * Y ^ (1 - alpha)) ≤
      8 * (Vr * Y ^ (1 - alpha)) := by
    have hprod : 0 ≤ Vr * Y ^ (1 - alpha) :=
      mul_nonneg hVr.le (Real.rpow_nonneg hY.le _)
    linarith
  have htarget :
      (D * (Real.log T₁) ^ receiverQ) / (4 * Q) =
        ((D / (2 * Q)) / 2) *
          (Real.log T₁) ^ receiverQ := by
    field_simp
    ring
  rw [htarget] at hdiv
  simpa only [X, M, T₁, Y, Vbase, Q, Vr, alpha, mul_assoc] using
    hfourEight.trans hdiv

end RHTower.Sieve
