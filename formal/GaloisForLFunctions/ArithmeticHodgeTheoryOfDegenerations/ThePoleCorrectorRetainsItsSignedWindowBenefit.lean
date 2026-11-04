import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolarSourceAboveHalf
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheCriticalConductorFormRetainsThePolarGenus
import GaloisForLFunctions.HTGeometry.PositiveOperatorInner

/-!
# The signed benefit of a growing pole corrector

The complete pole energy and its terminal source determine an exact
two-dimensional critical form. Completing its scalar square improves
the compensated window bound on the established positive critical band.
The aliasing term remains in that bound.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  ArithmeticDegenerationTheory CriticalArithmeticCorrelationTheory ArithmeticElectrostatics

/-- The complete polar source received by an interior terminal window. -/
def interiorTerminalPolarSource (h : ℝ → ℝ) : ℝ :=
  ((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
    ((∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile h) x) -
      Real.log (2 * Real.pi) * ∫ x in (0 : ℝ)..1, logProfile h x)

/-- The full critical pole energy, including its positive genus. -/
def criticalPoleWindowCost (R : ℝ) : ℝ :=
  (jordanCoefficient 1 + criticalGenusCoefficient R) / R

theorem criticalPoleWindowCost_pos {R : ℝ} (hR : 0 < R) :
    0 < criticalPoleWindowCost R :=
  div_pos (add_pos_of_pos_of_nonneg (jordanCoefficient_pos one_pos)
    (criticalGenusCoefficient_nonneg hR.le)) hR

/-- The pole corrector has finite positive energy at every positive critical ratio. -/
theorem tendsto_critical_pole_window_cost {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.log N / c N *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector 1 N), normalizedRamanujanHorizonVector 1 N⟫)
      atTop (𝓝 (criticalPoleWindowCost R)) := by
  have hg := tendsto_critical_rescaledConductorGram hc hR hcrit (m := 1) (l := 1) one_pos one_pos
  simp only [and_self, if_true] at hg
  have ht := hg.div hcrit hR.ne'
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  dsimp only [Pi.div_apply, rescaledConductorGram, conductorEntry]
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  field_simp [hc0.ne', hL.ne']

/-- The complete critical form on a window and a growing pole corrector. -/
theorem tendsto_complete_window_add_pole_corrector
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      let z := horizonProfileVector (horizonWeights h N) N +
        (t * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector 1 N
      (c N)⁻¹ * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫)
      atTop (𝓝 (((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h) +
        7 * tiltedJordanOne / R * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) +
        2 * t * interiorTerminalPolarSource h + t ^ 2 * criticalPoleWindowCost R)) := by
  let x := fun N : ℕ => horizonProfileVector (horizonWeights h N) N
  let v := fun N : ℕ => normalizedRamanujanHorizonVector 1 N
  let B := fun N : ℕ => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
  have hbase : Tendsto (fun N : ℕ => (c N)⁻¹ * ⟪B N (x N), x N⟫) atTop
      (𝓝 (((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h) +
        7 * tiltedJordanOne / R * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
    refine (horizon_layer_criticalCurve_exact hh hA hsupp hc hR hcrit).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp only [B, x]
    rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline tiltedUnitSpline_support
      (zero_lt_one.trans_le (hc N)) hN]
    have ht := atomicTest_congr (N := N)
      (x := primeHorizonExtension (horizonProfileVector (horizonWeights h N) N))
      (x' := horizonWeights h N)
      (fun n hn => primeHorizonExtension_coe (horizonProfileVector (horizonWeights h N) N) ⟨n, hn⟩)
      (atomDilate tiltedUnitSpline (c N / N))
    rw [ht]
  have hsource := tendsto_complete_terminal_pole_above_half contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hh hA hsupp
    hδ hη hlow hhigh hc hR hcrit
  change Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N * ⟪B N (v N), x N⟫)
    atTop (𝓝 (interiorTerminalPolarSource h)) at hsource
  have hself := tendsto_critical_pole_window_cost hc hR hcrit
  have ht := (hbase.add (hsource.const_mul (2 * t))).add (hself.const_mul (t ^ 2))
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  have hB := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N)
  have hquad := HTGeometry.tInner_self_add_smul hB (x N) (v N) (t * Real.sqrt (Real.log N))
  rw [HTGeometry.tInner_comm hB (x N) (v N)] at hquad
  simp only [HTGeometry.tInner_def] at hquad
  have hsquare : (t * Real.sqrt (Real.log N)) * (t * Real.sqrt (Real.log N)) =
      t ^ 2 * Real.log N := by
    calc
      _ = t ^ 2 * (Real.sqrt (Real.log N)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL.le]
  rw [hsquare] at hquad
  change _ = (c N)⁻¹ * ⟪B N (x N + (t * Real.sqrt (Real.log N)) • v N),
    x N + (t * Real.sqrt (Real.log N)) • v N⟫
  rw [hquad]
  dsimp only [B, v]
  ring

/-- Whole-space positivity on the established band pays the exact optimized polar correction. -/
theorem exists_critical_band_window_pencil_ge_polar_source_square :
    ∃ K : ℝ, 0 < K ∧ 2 * K ≤ 1 ∧
      ∀ R : ℝ, 0 < R → R ≤ (2 * K) ^ 8 →
        ∀ {h : ℝ → ℝ} {A : ℝ}, ContDiff ℝ 2 h → 0 ≤ A →
          (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
          ∀ {δ η : ℝ}, (1 / 2 : ℝ) < δ → η < 1 →
            (∀ x, x ≤ δ → logProfile h x = 0) →
            (∀ x, η ≤ x → logProfile h x = 0) →
            interiorTerminalPolarSource h ^ 2 / criticalPoleWindowCost R ≤
              ((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
                weilQuad (halfWeight h) +
              7 * tiltedJordanOne / R * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
  obtain ⟨K, hK, h2K, hfloor⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  refine ⟨K, hK, h2K, ?_⟩
  intro R hR hRK h A hh hA hsupp δ η hδ hη hlow hhigh
  let c := canonicalCriticalCurve R
  have hc : ∀ N, 1 ≤ c N := one_le_canonicalCriticalCurve R
  have hcrit := tendsto_canonicalCriticalCurve_pow_eight hR
  let S := interiorTerminalPolarSource h
  let D := criticalPoleWindowCost R
  have hD : 0 < D := criticalPoleWindowCost_pos hR
  have ht := tendsto_complete_window_add_pole_corrector hh hA hsupp hδ hη hlow hhigh
    hc hR hcrit (-S / D)
  have hnonneg : 0 ≤
      ((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
      7 * tiltedJordanOne / R * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) +
      2 * (-S / D) * S + (-S / D) ^ 2 * D := by
    apply ge_of_tendsto ht
    filter_upwards [hfloor, eventually_canonicalCriticalCurve_le_and_eq hK hR hRK]
      with N hN hband
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    let z := horizonProfileVector (horizonWeights h N) N +
      ((-S / D) * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector 1 N
    have hz := hN (c N) (hc N) hband.1 z
    have hκ := tiltedSplineSpectralFloorConstant_pos
    have hz0 : 0 ≤ completeWeilEnergy tiltedUnitSpline (c N) N z :=
      (by positivity : 0 ≤ tiltedSplineSpectralFloorConstant / (2 * c N ^ 7) * ‖z‖ ^ 2).trans hz
    exact mul_nonneg (inv_nonneg.mpr hc0.le) hz0
  have heq : 2 * (-S / D) * S + (-S / D) ^ 2 * D = -(S ^ 2 / D) := by
    field_simp [hD.ne'] <;> ring
  rw [add_assoc _ (2 * (-S / D) * S), heq] at hnonneg
  change S ^ 2 / D ≤ _
  linarith only [hnonneg]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_complete_window_add_pole_corrector
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.exists_critical_band_window_pencil_ge_polar_source_square
