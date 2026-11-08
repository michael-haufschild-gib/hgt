import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NonpositiveDirectionsHaveChargedCompactCollarProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalPositivityThresholdLaw

/-!
# Nonpositive directions have normalized charged profiles

A nonpositive discrete direction yields a collar and scalar pole coordinate of unit
joint mass. Scaling preserves compactness bounds and the sharp charged comparison.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis CompletedArithmeticForms ArithmeticElectrostatics

/-- A normalized atomic source cannot extend beyond its atom width. -/
theorem normalizedCentredAtomicTest_vanish_above_width {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) (y : ℕ → ℝ) {u : ℝ} (hu : c / (N : ℝ) < u) :
    normalizedCentredAtomicTest tiltedUnitSpline y c N u = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc hN0
  have hsupp := tiltedUnitSpline_atom_support hw
  simp only [normalizedCentredAtomicTest, centredAtomicTest, atomicTest]
  rw [mul_eq_zero]
  right
  refine sum_eq_zero fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  rw [hsupp _ fun hmem => by linarith only [hmem.2, hu, hlog], mul_zero]

/-- Every nonpositive direction yields a collar and pole coordinate of unit joint mass,
with uniform compactness bounds and arbitrarily small charged energy. -/
theorem exists_normalized_charged_collar_bridge
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ K_W K_S K_Q : ℝ, 0 < K_W ∧ 0 < K_S ∧ 0 < K_Q ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
      completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0 →
      ∃ (β : ℝ) (z : EuclideanSpace ℝ (PrimeHorizonIndex N)),
        let U := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N
        (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension z n = 0) ∧
        (∫ u, U u ^ 2) + β ^ 2 = 1 ∧
        (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ K_W ∧
        topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension z) ≤ K_S ∧
        weilQuad U ≤ K_Q ∧
        weilQuad U + (∫ u, tiltedUnitSpline u ^ 2) *
          ((Real.log N / c N) * completeWeilEnergy tiltedUnitSpline (c N) N
            (normalizedRamanujanHorizonVector 1 N) * β ^ 2) +
          2 * (∫ u, tiltedUnitSpline u ^ 2) * β *
            (Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫) ≤ ε := by
  obtain ⟨K_W, K_L, K_S, K_Q, hKW, _, hKS, hKQ, hbridge⟩ :=
    exists_critical_charged_collar_weilQuad_bridge hc hR hcrit
  refine ⟨K_W, K_S, K_Q, hKW, hKS, hKQ, fun {ε} hε => ?_⟩
  filter_upwards [eventually_ge_atTop 1, hbridge hε,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN hbr hL x hne hnonpos
  change 0 < Real.log (N : ℝ) at hL
  obtain ⟨τ, w, _, hJ, hW, _, hS, hQ, hsharp⟩ := hbr x hne hnonpos
  let M := N / linearDefectCutoff (c N)
  let y := atomicTailCoefficients M (primeHorizonExtension w)
  let U := normalizedCentredAtomicTest tiltedUnitSpline y (c N) N
  let J := (∫ u, U u ^ 2) + τ ^ 2 / Real.log N
  change 0 < J at hJ
  let ν := Real.sqrt J
  have hν : 0 < ν := Real.sqrt_pos.mpr hJ
  have hν2 : ν ^ 2 = J := Real.sq_sqrt hJ.le
  let β := τ / (Real.sqrt (Real.log N) * ν)
  let z := ν⁻¹ • horizonCollarVector M w
  let V := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  have hxe : primeHorizonExtension z = fun n => ν⁻¹ * y n := by
    have he : primeHorizonExtension z = ν⁻¹ • primeHorizonExtension (horizonCollarVector M w) := by
      funext n
      simp only [z, primeHorizonExtension, Pi.smul_apply, smul_eq_mul]
      split_ifs
      · rfl
      · exact (mul_zero _).symm
    rw [he, primeHorizonExtension_horizonCollarVector]
    rfl
  have hV : V = fun u => ν⁻¹ * U u := by
    dsimp only [V]
    rw [hxe]
    exact normalizedCentredAtomicTest_const_mul _ y _ _
  have hUd : ContDiff ℝ 2 U := contDiff_normalizedCentredAtomicTest contDiff_tiltedUnitSpline hc0 hN y
  have hUc : HasCompactSupport U := hasCompactSupport_normalizedCentredAtomicTest tiltedUnitSpline_eq_zero hc0 hN y
  have hV2 : (∫ u, V u ^ 2) = ν⁻¹ ^ 2 * ∫ u, U u ^ 2 := by
    simp only [hV, mul_pow, integral_const_mul]
  have hβ2 : β ^ 2 = ν⁻¹ ^ 2 * (τ ^ 2 / Real.log N) := by
    dsimp only [β]
    rw [div_pow, mul_pow, Real.sq_sqrt hL.le]
    ring
  have hscale {a C : ℝ} (ha : a ≤ C * J) : ν⁻¹ ^ 2 * a ≤ C :=
    (mul_le_mul_of_nonneg_left ha (sq_nonneg _)).trans_eq (by
      rw [inv_pow, hν2]
      field_simp [hJ.ne'])
  have hV8 : (∫ u, V u ^ 2 * Real.exp (-(8 * u))) =
      ν⁻¹ ^ 2 * ∫ u, U u ^ 2 * Real.exp (-(8 * u)) := by
    simp only [hV, mul_pow, mul_assoc, integral_const_mul]
  have hVS : topCollarSeventhMass M N (primeHorizonExtension z) =
      ν⁻¹ ^ 2 * topCollarSeventhMass M N (primeHorizonExtension w) := by
    rw [hxe]
    unfold topCollarSeventhMass
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    simp only [y, atomicTailCoefficients, (mem_Ioc.mp hn).1, if_true, mul_pow]
    ring
  have hVQ : weilQuad V = ν⁻¹ ^ 2 * weilQuad U := by
    rw [hV]
    exact weilQuad_const_mul hUd hUc _
  refine ⟨β, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    change n ≤ M at hn
    rw [hxe]
    simp only [y, atomicTailCoefficients, not_lt.mpr hn, if_false, mul_zero]
  · change (∫ u, V u ^ 2) + β ^ 2 = 1
    rw [hV2, hβ2, ← mul_add]
    change ν⁻¹ ^ 2 * J = 1
    rw [inv_pow, hν2, inv_mul_cancel₀ hJ.ne']
  · change (∫ u, V u ^ 2 * Real.exp (-(8 * u))) ≤ K_W
    rw [hV8]
    exact hscale hW
  · rw [hVS]
    exact hscale hS
  · change weilQuad V ≤ K_Q
    rw [hVQ]
    exact hscale hQ
  · have hb := hscale hsharp
    change weilQuad V + _ + _ ≤ ε
    rw [hVQ, hβ2]
    have hi : ⟪conductorResidualVector (c N) 1 N, z⟫ =
        ν⁻¹ * ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫ := by
      dsimp only [z]
      rw [real_inner_smul_right]
    rw [hi]
    have he : ν⁻¹ ^ 2 * weilQuad U + (∫ u, tiltedUnitSpline u ^ 2) *
        ((Real.log N / c N) * completeWeilEnergy tiltedUnitSpline (c N) N
          (normalizedRamanujanHorizonVector 1 N) * (ν⁻¹ ^ 2 * (τ ^ 2 / Real.log N))) +
        2 * (∫ u, tiltedUnitSpline u ^ 2) * β *
          (Real.sqrt (Real.log N) / c N *
            (ν⁻¹ * ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫)) =
        ν⁻¹ ^ 2 * (weilQuad U + ((∫ u, tiltedUnitSpline u ^ 2) / c N) *
          (completeWeilEnergy tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) * τ ^ 2 +
            2 * τ * ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫)) := by
      dsimp only [β]
      field_simp [hν.ne', hsL.ne', hL.ne', hc0.ne']
      ring
    rw [he]
    exact hb

#print axioms exists_normalized_charged_collar_bridge
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
