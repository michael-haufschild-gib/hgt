import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LowConductorCollarPairingsAndWindowLocalizedGarding
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NegativeDirectionsCannotEscapeLogarithmicWindows

/-!
# Whole-space collar Gårding

The three-band complement reserves absorb the nonpolar low-packet cross terms.
The sole remaining scalar loss is the conductor-one coefficient square.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Whole-space Gårding retains the completed packet diagonal, collar reserves, and Lévy energy,
with a single scalar polar loss. -/
theorem exists_wholeSpace_collar_garding_with_linear_mass :
    ∃ c_W C_B : ℝ, 0 < c_W ∧ 0 < C_B ∧
    ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) → ∀ {R : ℝ}, 0 < R →
    Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R) →
    ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      ∀ z ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ,
      ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
        let M := N / linearDefectCutoff (c N)
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients M (primeHorizonExtension w)) (c N) N
        let L := Real.log (N : ℝ)
        (1 / 4 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 +
        (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
          (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
          topCollarSeventhMass M N (primeHorizonExtension w) +
        (c N * c_W / (R + 1)) * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) +
        (c N / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U ≤
        completeWeilEnergy tiltedUnitSpline (c N) N
          ((∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) + z) +
        (c N * (C_B * (R + 2))) * (∫ u, U u ^ 2) + (C * c N / L) * b 1 ^ 2 := by
  obtain ⟨c_W, C_B, hcW, hCB, hG⟩ := exists_all_ratio_three_band_garding_with_linear_mass
  refine ⟨c_W, C_B, hcW, hCB, fun {c} hc {R} hR hcrit => ?_⟩
  obtain ⟨B, _, hBbound, hGN⟩ := hG (show 0 < R + 1 by linarith)
  let κ_P := 1 / (64 * explicitConductorCutoffConstant)
  let κ_S := dyadicTopMassConstant / 128
  have hκP : 0 < κ_P := by dsimp only [κ_P]; exact one_div_pos.mpr
    (mul_pos (by norm_num) explicitConductorCutoffConstant_pos)
  have hκS : 0 < κ_S := div_pos dyadicTopMassConstant_pos (by norm_num)
  obtain ⟨C, hC, hcross⟩ := eventually_lowPacket_cross_payment hc hR hcrit hκP hκS
  refine ⟨C, hC, ?_⟩
  filter_upwards [hGN, hcross, eventually_completeWeil_low_packet_energy_ge hc hR hcrit,
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hGN hcrossN hlow hratio hL b z hz
  have hc8 : c N ^ 8 ≤ (R + 1) * Real.log N := (div_le_iff₀ hL).mp hratio.le
  obtain ⟨u₀, u₁, w, hsplit, hu₀, _, _, _, hw, hnorm, hGarding, _⟩ :=
    hGN (hc N) hc8 hz
  refine ⟨w, hw, ?_⟩
  dsimp only at hGarding ⊢
  let y := ∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N
  have hcros := hcrossN b u₀ hu₀ u₁ w (by rwa [← hsplit])
  rw [← hsplit] at hcros
  have hlowN := hlow b
  change (1 / 2 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
    completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) ≤
      completeWeilEnergy tiltedUnitSpline (c N) N y at hlowN
  have henergy : completeWeilEnergy tiltedUnitSpline (c N) N (y + z) =
      completeWeilEnergy tiltedUnitSpline (c N) N y +
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, z⟫ +
      completeWeilEnergy tiltedUnitSpline (c N) N z :=
    hermitian_inner_add_eq_telescoped (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N) y z
  have hnegative := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, z⟫
  have hnorm' := congrArg (fun t : ℝ => (tiltedSplineSpectralFloorConstant + 2) * t) hnorm
  dsimp only [κ_P, κ_S, y] at hcros henergy hnegative hnorm' hlowN
  have hmass : 0 ≤ ∫ u, (normalizedCentredAtomicTest tiltedUnitSpline
      (atomicTailCoefficients (N / linearDefectCutoff (c N)) (primeHorizonExtension w)) (c N) N u) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hBpay := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBbound (zero_lt_one.trans_le (hc N)).le) hmass
  ring_nf at hGarding hcros henergy hnegative hnorm' hlowN hBpay ⊢
  linarith only [hGarding, hcros, henergy, hnegative, hnorm', hlowN, hBpay]

/-- Whole-space collar Gårding along a positive critical curve. -/
theorem exists_critical_wholeSpace_collar_garding
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ c_W B C : ℝ, 0 < c_W ∧ 0 < B ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      ∀ z ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ,
      ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
        let M := N / linearDefectCutoff (c N)
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients M (primeHorizonExtension w)) (c N) N
        let L := Real.log (N : ℝ)
        (1 / 4 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 +
        (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
          (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
          topCollarSeventhMass M N (primeHorizonExtension w) +
        (c N * c_W / (R + 1)) * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) +
        (c N / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U ≤
        completeWeilEnergy tiltedUnitSpline (c N) N
          ((∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) + z) +
        (c N * B) * (∫ u, U u ^ 2) + (C * c N / L) * b 1 ^ 2 := by
  obtain ⟨c_W, C_B, hcW, hCB, hall⟩ := exists_wholeSpace_collar_garding_with_linear_mass
  obtain ⟨C, hC, hN⟩ := hall hc hR hcrit
  exact ⟨c_W, C_B * (R + 2), C, hcW, by positivity, hC, hN⟩

/-- Primitive packets retain collar Gårding and an arbitrarily accurate far-energy bridge
for the same far component. -/
theorem exists_critical_primitive_collar_garding_and_far_bridge
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ c_W B : ℝ, 0 < c_W ∧ 0 < B ∧ ∀ {η : ℝ}, 0 < η →
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ z ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ,
      ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
        let M := N / linearDefectCutoff (c N)
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients M (primeHorizonExtension w)) (c N) N
        let L := Real.log (N : ℝ)
        let P := (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
          (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2)
        let S := (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
          topCollarSeventhMass M N (primeHorizonExtension w)
        let x := (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) + z
        ((1 / 8 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 + P + S +
        (c N * c_W / (R + 1)) * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) +
        (c N / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U ≤
        completeWeilEnergy tiltedUnitSpline (c N) N x + (c N * B) * (∫ u, U u ^ 2)) ∧
        completeWeilEnergy tiltedUnitSpline (c N) N w ≤
          completeWeilEnergy tiltedUnitSpline (c N) N x + η * (P + S) := by
  obtain ⟨c_W, hcW, hG⟩ := exists_all_ratio_three_band_garding_and_far_bridge
  obtain ⟨B, hB, hGN⟩ := hG (show 0 < R + 1 by linarith)
  let κ_P := 1 / (64 * explicitConductorCutoffConstant)
  let κ_S := dyadicTopMassConstant / 128
  have hκP : 0 < κ_P := by dsimp only [κ_P]; exact one_div_pos.mpr
    (mul_pos (by norm_num) explicitConductorCutoffConstant_pos)
  have hκS : 0 < κ_S := div_pos dyadicTopMassConstant_pos (by norm_num)
  obtain ⟨C₀, hC₀, hcross₀⟩ := eventually_lowPacket_cross_payment hc hR hcrit hκP hκS
  refine ⟨c_W, B, hcW, hB, fun {η} hη => ?_⟩
  obtain ⟨Cη, hCη, hcrossη⟩ := eventually_lowPacket_cross_payment hc hR hcrit
    (mul_pos (half_pos hη) hκP) (mul_pos (half_pos hη) hκS)
  have hell := (tendsto_atTop_add_const_left _ (1 : ℝ) Real.tendsto_log_atTop).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hGN, hcross₀, hcrossη,
    eventually_primitive_polar_penalty_le hc hR hcrit hC₀ (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_primitive_polar_penalty_le hc hR hcrit hCη (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_completeWeil_low_packet_energy_ge hc hR hcrit,
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hell.eventually_ge_atTop (8 / η)]
    with N hGN hcross₀N hcrossηN hpen₀ hpenη hlow hratio hL1 hellN b hprim z hz
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hc8 : c N ^ 8 ≤ (R + 1) * Real.log N := (div_le_iff₀ hL).mp hratio.le
  obtain ⟨u₀, u₁, w, hsplit, hu₀, _, _, _, hw, hnorm, hGarding, hbridge⟩ :=
    hGN (hc N) hc8 hz
  refine ⟨w, hw, ?_⟩
  dsimp only at hGarding hbridge ⊢
  let y := ∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N
  have hcros₀ := hcross₀N b u₀ hu₀ u₁ w (by rwa [← hsplit])
  have hcrosη := hcrossηN b u₀ hu₀ u₁ w (by rwa [← hsplit])
  rw [← hsplit] at hcros₀ hcrosη
  have hp₀ := hpen₀ b hprim
  have hpη := hpenη b hprim
  have hlowN := hlow b
  change (1 / 2 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
    completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) ≤
      completeWeilEnergy tiltedUnitSpline (c N) N y at hlowN
  have henergy : completeWeilEnergy tiltedUnitSpline (c N) N (y + z) =
      completeWeilEnergy tiltedUnitSpline (c N) N y +
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, z⟫ +
      completeWeilEnergy tiltedUnitSpline (c N) N z :=
    hermitian_inner_add_eq_telescoped (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N) y z
  have hnegative := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) y, z⟫
  have hnorm' := congrArg (fun t : ℝ => (tiltedSplineSpectralFloorConstant + 2) * t) hnorm
  dsimp only [κ_P, κ_S, y] at hcros₀ hcrosη henergy hnegative hnorm' hlowN
  constructor
  · ring_nf at hGarding hcros₀ hp₀ henergy hnegative hnorm' hlowN ⊢
    linarith only [hGarding, hcros₀, hp₀, henergy, hnegative, hnorm', hlowN]
  · let L := Real.log (N : ℝ)
    let M := N / linearDefectCutoff (c N)
    let P := (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
      (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2)
    let S := (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
      topCollarSeventhMass M N (primeHorizonExtension w)
    have hPS : 0 ≤ P + S := by
      have hp : 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 :=
        sum_nonneg fun _ _ => sq_nonneg _
      have hs := topCollarSeventhMass_nonneg M N (primeHorizonExtension w)
      have hc0 := zero_lt_one.trans_le (hc N)
      have hg := dyadicTopMassConstant_pos
      have hd := explicitConductorCutoffConstant_pos
      have hl := Real.log_nonneg hL1
      dsimp only [P, S]; positivity
    have hell0 : 0 < 1 + Real.log L := by have := Real.log_nonneg hL1; positivity
    have hsmall : 4 / (1 + Real.log L) ≤ η / 2 := by
      have hh : 8 / η ≤ 1 + Real.log L := hellN
      have hx := (div_le_iff₀ hη).mp hh
      apply (div_le_iff₀ hell0).mpr
      nlinarith only [hx]
    have hres := mul_le_mul_of_nonneg_right hsmall hPS
    have hE0 : 0 ≤ ∑ m ∈ Icc 1 (lowPacketCutoff N),
        completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 :=
      sum_nonneg fun m hm => mul_nonneg
        (completedConductorEnergy_tilted_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1).le
        (sq_nonneg _)
    have hband0 : 0 ≤ (tiltedSplineSpectralFloorConstant + 2) * ‖u₀‖ ^ 2 := by
      have := tiltedSplineSpectralFloorConstant_pos; positivity
    have hband1 : 0 ≤ (tiltedSplineSpectralFloorConstant + 2) * ‖u₁‖ ^ 2 := by
      have := tiltedSplineSpectralFloorConstant_pos; positivity
    dsimp only [P, S, M, L] at hres
    ring_nf at hbridge hcrosη hpη henergy hnegative hlowN hres hE0 hband0 hband1 ⊢
    linarith only [hbridge, hcrosη, hpη, henergy, hnegative, hlowN, hres, hE0, hband0, hband1]

/-- Whole-space Gårding has only terminal-window mass and one scalar polar loss. The window
length grows by at most one quarter of the logarithm of the critical ratio. -/
theorem exists_wholeSpace_window_localized_collar_garding :
    ∃ C_len : ℝ, 1 ≤ C_len ∧
    ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) → ∀ {R : ℝ}, 0 < R →
    Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R) →
    ∃ A B C a : ℝ, 1 ≤ A ∧ A ≤ (1 / 4 : ℝ) * Real.log (R + 1) + C_len ∧
      0 < B ∧ 0 < C ∧ 0 < a ∧
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      ∀ z ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ,
      ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
        let M := N / linearDefectCutoff (c N)
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients M (primeHorizonExtension w)) (c N) N
        let L := Real.log (N : ℝ)
        (1 / 4 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 +
        (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
          (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
          topCollarSeventhMass M N (primeHorizonExtension w) +
        (c N * a) * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) +
        (c N / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U ≤
        completeWeilEnergy tiltedUnitSpline (c N) N
          ((∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) + z) +
        (c N * B) * (∫ u in Set.Ioc (-A) 1, U u ^ 2) + (C * c N / L) * b 1 ^ 2 := by
  obtain ⟨c_W, C_B, hcW, hCB, hG⟩ := exists_wholeSpace_collar_garding_with_linear_mass
  let C_len := (1 / 8 : ℝ) * Real.log (4 * C_B / c_W + 1) + 1
  have hClen : 1 ≤ C_len := by
    have hlog : 0 ≤ Real.log (4 * C_B / c_W + 1) := Real.log_nonneg (by have hh : 0 < 4 * C_B / c_W := by positivity; linarith only [hh])
    dsimp only [C_len]; linarith only [hlog]
  refine ⟨C_len, hClen, fun {c} hc {R} hR hcrit => ?_⟩
  obtain ⟨C, hC, hGN⟩ := hG hc hR hcrit
  let A := (1 / 8 : ℝ) * Real.log (2 * C_B * (R + 1) * (R + 2) / c_W + 1) + 1
  have hA : 1 ≤ A := by
    have hlog : 0 ≤ Real.log (2 * C_B * (R + 1) * (R + 2) / c_W + 1) :=
      Real.log_nonneg (by have hh : 0 < 2 * C_B * (R + 1) * (R + 2) / c_W := by positivity; linarith only [hh])
    dsimp only [A]; linarith only [hlog]
  have hAlen : A ≤ (1 / 4 : ℝ) * Real.log (R + 1) + C_len := by
    have hR1 : 1 ≤ R + 1 := by linarith
    have hcoeff : 0 ≤ 2 * C_B / c_W := by positivity
    have hprod : (R + 1) * (R + 2) ≤ 2 * (R + 1) ^ 2 := by nlinarith only [hR, sq_nonneg R]
    have hh := mul_le_mul_of_nonneg_left hprod hcoeff
    have hsq := one_le_pow₀ hR1 (n := 2)
    have harg : 2 * C_B * (R + 1) * (R + 2) / c_W + 1 ≤
        (4 * C_B / c_W + 1) * (R + 1) ^ 2 := by nlinarith only [hh, hsq]
    have hlog := Real.log_le_log (by positivity) harg
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
    dsimp only [A, C_len]
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog]
  refine ⟨A, C_B * (R + 2), C, c_W / (2 * (R + 1)), hA, hAlen,
    by positivity, hC, by positivity, ?_⟩
  have hwidth : Tendsto (fun N : ℕ => c N / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  filter_upwards [hGN, eventually_ge_atTop 1, hwidth.eventually (gt_mem_nhds zero_lt_one)]
    with N hGN hN1 hwid b z hz
  obtain ⟨w, hw, hg⟩ := hGN b z hz
  refine ⟨w, hw, ?_⟩
  let y := atomicTailCoefficients (N / linearDefectCutoff (c N)) (primeHorizonExtension w)
  let U := normalizedCentredAtomicTest tiltedUnitSpline y (c N) N
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hUd : ContDiff ℝ 2 U :=
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ _ _)
  have hUc : HasCompactSupport U :=
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero y hc0 hN1).mul_left
  have hsupp : ∀ u, 1 < u → U u = 0 := by
    intro u hu
    have hs := tiltedUnitSpline_atom_support (div_pos hc0 hN0)
    dsimp only [U, normalizedCentredAtomicTest, centredAtomicTest, atomicTest]
    rw [mul_eq_zero]
    right
    refine sum_eq_zero fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hlog := Real.log_le_log hn0 (show (n : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn).2)
    rw [hs _ (fun hmem => by linarith only [hmem.2, hu, hwid, hlog]), mul_zero]
  have hsplit := integral_sq_eq_Iic_add_Ioc (zero_le_one.trans hA) hUd.continuous hUc hsupp
  have htail := iic_mass_le_exponential_mass hCB hcW (show 0 < R + 1 by positivity)
    hUd.continuous hUc
  change (2 * C_B * (R + 1 + 1)) *
      (∫ u, (Set.Iic (-((1 / 8 : ℝ) * Real.log (2 * C_B * (R + 1) * (R + 1 + 1) / c_W + 1) + 1))).indicator
        (fun v => U v ^ 2) u) ≤ (c_W / (R + 1)) * ∫ u, U u ^ 2 * Real.exp (-(8 * u)) at htail
  have hR2 : R + 1 + 1 = R + 2 := by ring
  rw [hR2] at htail
  have hpaid := mul_le_mul_of_nonneg_left htail (show 0 ≤ c N / 2 by positivity)
  dsimp only [A] at hsplit
  dsimp only at hg ⊢
  dsimp only [U, y] at hsplit hpaid
  rw [hsplit, mul_add] at hg
  ring_nf at hg hpaid ⊢
  linarith only [hg, hpaid]

#print axioms exists_wholeSpace_collar_garding_with_linear_mass
#print axioms exists_wholeSpace_window_localized_collar_garding
#print axioms exists_critical_wholeSpace_collar_garding
#print axioms exists_critical_primitive_collar_garding_and_far_bridge

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
