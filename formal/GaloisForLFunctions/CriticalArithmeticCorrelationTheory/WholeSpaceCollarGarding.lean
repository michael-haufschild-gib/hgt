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

#print axioms exists_critical_wholeSpace_collar_garding

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
