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
  obtain ⟨c_W, hcW, hG⟩ := exists_all_ratio_three_band_garding_and_far_bridge
  obtain ⟨B, hB, hGN⟩ := hG (show 0 < R + 1 by linarith)
  let κ_P := 1 / (64 * explicitConductorCutoffConstant)
  let κ_S := dyadicTopMassConstant / 128
  have hκP : 0 < κ_P := by dsimp only [κ_P]; exact one_div_pos.mpr
    (mul_pos (by norm_num) explicitConductorCutoffConstant_pos)
  have hκS : 0 < κ_S := div_pos dyadicTopMassConstant_pos (by norm_num)
  obtain ⟨C, hC, hcross⟩ := eventually_lowPacket_cross_payment hc hR hcrit hκP hκS
  refine ⟨c_W, B, C, hcW, hB, hC, ?_⟩
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
  linarith only [hGarding, hcros, henergy, hnegative, hnorm', hlowN]

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
  · linarith only [hGarding, hcros₀, hp₀, henergy, hnegative, hnorm', hlowN]
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
    linarith only [hbridge, hcrosη, hpη, henergy, hnegative, hlowN, hres, hE0, hband0, hband1]

#print axioms exists_critical_wholeSpace_collar_garding
#print axioms exists_critical_primitive_collar_garding_and_far_bridge

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
