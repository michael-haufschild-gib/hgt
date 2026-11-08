import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WholeSpaceCollarGarding
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AdaptiveLowPacketSchurPayments
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLowPacketRetainsTheActualPoleEnergy

/-!
# Whole-space Gårding retains the literal polar channel

One three-band decomposition supplies compactness, an upper bound for the far
energy, and an arbitrarily accurate energy comparison retaining the exact pole
diagonal and the polar collar pairing.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry ArithmeticElectrostatics

/-- The same collar carries Gårding, a bounded far-energy bridge, and the sharp charged
energy comparison. All discarded cross terms have arbitrarily small relative cost. -/
theorem exists_critical_wholeSpace_garding_and_polar_bridge
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ c_W B C₀ : ℝ, 0 < c_W ∧ 0 < B ∧ 0 < C₀ ∧ ∀ {ε η : ℝ}, 0 < ε → 0 < η → ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
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
        ((1 / 4 : ℝ) * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 + P + S +
        (c N * c_W / (R + 1)) * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) +
        (c N / (4 * ∫ u, tiltedUnitSpline u ^ 2)) * levyEnergy U ≤
        completeWeilEnergy tiltedUnitSpline (c N) N x + (c N * B) * (∫ u, U u ^ 2) +
          (C₀ * c N / L) * b 1 ^ 2) ∧
        completeWeilEnergy tiltedUnitSpline (c N) N w ≤
          completeWeilEnergy tiltedUnitSpline (c N) N x + 2 * (P + S) +
            (C₀ * c N / L) * b 1 ^ 2 ∧
        completeWeilEnergy tiltedUnitSpline (c N) N w +
            completeWeilEnergy tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) * b 1 ^ 2 +
            2 * b 1 * ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫ ≤
          completeWeilEnergy tiltedUnitSpline (c N) N x +
            ε * (∑ m ∈ Icc 1 (lowPacketCutoff N),
              completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) + η * (P + S) := by
  obtain ⟨c_W, hcW, hG⟩ := exists_all_ratio_three_band_garding_and_far_bridge
  obtain ⟨B, hB, hGN⟩ := hG (show 0 < R + 1 by linarith)
  let κ_P := 1 / (64 * explicitConductorCutoffConstant)
  let κ_S := dyadicTopMassConstant / 128
  have hκP : 0 < κ_P := by
    dsimp only [κ_P]
    exact one_div_pos.mpr (mul_pos (by norm_num) explicitConductorCutoffConstant_pos)
  have hκS : 0 < κ_S := div_pos dyadicTopMassConstant_pos (by norm_num)
  obtain ⟨C₀, hC₀, hcross₀⟩ := eventually_lowPacket_cross_payment hc hR hcrit hκP hκS
  refine ⟨c_W, B, C₀, hcW, hB, hC₀, fun {ε η} hε hη => ?_⟩
  have hcrossη := eventually_lowPacket_cross_sub_polar_le hc hR hcrit
    (half_pos hε) (mul_pos (half_pos hη) hκP) (mul_pos (half_pos hη) hκS)
  have hell := (tendsto_atTop_add_const_left _ (1 : ℝ) Real.tendsto_log_atTop).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hGN, hcross₀, hcrossη,
    eventually_completeWeil_low_packet_energy_ge hc hR hcrit,
    eventually_lowPacket_ge_actual_pole_sub hc hR hcrit (half_pos hε),
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hell.eventually_ge_atTop (8 / η), hell.eventually_ge_atTop 4]
    with N hGN hcross₀N hcrossηN hlow hpole hratio hL1 hellN hell4 b z hz
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
  let L := Real.log (N : ℝ)
  let M := N / linearDefectCutoff (c N)
  let P := (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
    (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2)
  let S := (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
    topCollarSeventhMass M N (primeHorizonExtension w)
  have hPS : 0 ≤ P + S := by
    have hp : 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
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
  have hsmall₀ : 4 / (1 + Real.log L) ≤ 1 := (div_le_one hell0).mpr hell4
  have hres := mul_le_mul_of_nonneg_right hsmall hPS
  have hres₀ := mul_le_mul_of_nonneg_right hsmall₀ hPS
  have hE0 : 0 ≤ ∑ m ∈ Icc 1 (lowPacketCutoff N),
      completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 :=
    sum_nonneg fun m hm => mul_nonneg
      (completedConductorEnergy_tilted_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1).le
      (sq_nonneg _)
  have hband0 : 0 ≤ (tiltedSplineSpectralFloorConstant + 2) * ‖u₀‖ ^ 2 := by
    have := tiltedSplineSpectralFloorConstant_pos; positivity
  have hband1 : 0 ≤ (tiltedSplineSpectralFloorConstant + 2) * ‖u₁‖ ^ 2 := by
    have := tiltedSplineSpectralFloorConstant_pos; positivity
  dsimp only [P, S, M, L] at hres hres₀
  constructor
  · simp only [div_eq_mul_inv, mul_inv_rev] at hGarding hcros₀ henergy hnegative hnorm' hlowN ⊢
    ring_nf at hGarding hcros₀ henergy hnegative hnorm' hlowN ⊢
    linarith only [hGarding, hcros₀, henergy, hnegative, hnorm', hlowN]
  · constructor
    · simp only [div_eq_mul_inv, mul_inv_rev] at hbridge hcros₀ henergy hnegative hlowN hres₀ hE0 hband0 hband1 ⊢
      ring_nf at hbridge hcros₀ henergy hnegative hlowN hres₀ hE0 hband0 hband1 ⊢
      linarith only [hbridge, hcros₀, henergy, hnegative, hlowN, hres₀, hE0, hband0, hband1]
    · have hpoleN := hpole b
      change completeWeilEnergy tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) * b 1 ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline (c N) N
          (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N) +
        (ε / 2) * ∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 at hpoleN
      have hcharged := neg_abs_le
        (⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N), z⟫ -
          b 1 * ⟪conductorResidualVector (c N) 1 N,
            horizonCollarVector (N / linearDefectCutoff (c N)) w⟫)
      simp only [div_eq_mul_inv, mul_inv_rev] at hbridge hcrosη henergy hcharged hpoleN hres hband0 hband1 ⊢
      ring_nf at hbridge hcrosη henergy hcharged hpoleN hres hband0 hband1 ⊢
      linarith only [hbridge, hcrosη, henergy, hcharged, hpoleN, hres, hband0, hband1]

#print axioms exists_critical_wholeSpace_garding_and_polar_bridge
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
