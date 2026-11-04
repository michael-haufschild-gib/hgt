import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TerminalConductorSourcesConcentrateAtThePole
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketRetainsItsSignedPolarPart

/-!
# The logarithmic packet cannot improve a zero-source terminal window

Completing one scalar square per conductor bounds the benefit of every
packet corrector by its total inverse-energy source mass. That mass is
polar, so on the kernel of the polar source every possible benefit
vanishes, uniformly over the growing coefficients.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations ArithmeticDegenerationTheory
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

private theorem positive_conductor_energy {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    0 < completedConductorEnergy tiltedUnitSpline c m := by
  by_cases hmc : (m : ℝ) ≤ c
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hp := (mul_pos tiltedSplineSpectralFloorConstant_pos (pow_pos hm0 7)).trans_le
      (seventh_mul_completedConductorEnergy_ge_below_overlap hc hm hmc)
    rcases mul_pos_iff.mp hp with hp | hn
    · exact hp.2
    · exact False.elim ((pow_pos hc 7).not_gt hn.1)
  · exact tiltedSplineSpectralFloorConstant_pos.trans_le
      (tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc hm (lt_of_not_ge hmc).le)

/-- The actual packet floor bounds the benefit of every correction by its inverse-energy source. -/
theorem eventually_low_packet_correction_ge_source_budget
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ (h : ℝ → ℝ) (b : ℕ → ℝ),
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let x := horizonProfileVector (horizonWeights h N) N
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) x, x⟫ / c N -
        2 * (∑ m ∈ Icc 1 Q, terminalConductorSourceSquare h (c N) N m) ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) (x + y), x + y⟫ /
          c N := by
  filter_upwards [eventually_completeWeil_low_packet_energy_ge hc hR hcrit] with N hfloor
  intro h b Q x y
  let M := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  let p := fun m => ⟪M (normalizedRamanujanHorizonVector m N), x⟫
  let q := fun m => terminalConductorSourceSquare h (c N) N m
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hpoint : ∀ m ∈ Icc 1 Q,
      (-2 * c N) * q m ≤ (1 / 2 : ℝ) * (E m * b m ^ 2) + 2 * (b m * p m) := by
    intro m hm
    have hE : 0 < E m := positive_conductor_energy hc0 (mem_Icc.mp hm).1
    have hs : 0 ≤ (E m * b m + 2 * p m) ^ 2 / (2 * E m) := by positivity
    have he : (E m * b m + 2 * p m) ^ 2 / (2 * E m) =
        (1 / 2 : ℝ) * (E m * b m ^ 2) + 2 * (b m * p m) + 2 * p m ^ 2 / E m := by
      field_simp [hE.ne']
      <;> ring
    rw [he] at hs
    have hq : (-2 * c N) * q m = -(2 * p m ^ 2 / E m) := by
      dsimp only [q, terminalConductorSourceSquare, p, M, E, x]
      field_simp [hc0.ne', hE.ne']
      <;> ring
    rw [hq]
    linarith only [hs]
  have hsum := sum_le_sum hpoint
  rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hf := hfloor b
  change (1 / 2 : ℝ) * (∑ m ∈ Icc 1 Q, E m * b m ^ 2) ≤ ⟪M y, y⟫ at hf
  have hmixed : ⟪M y, x⟫ = ∑ m ∈ Icc 1 Q, b m * p m := by
    simp only [y, map_sum, map_smul, sum_inner, real_inner_smul_left, p]
  have hM := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N)
  have hquad := HTGeometry.tInner_self_add_smul hM x y 1
  rw [HTGeometry.tInner_comm hM x y] at hquad
  simp only [HTGeometry.tInner_def, one_smul, one_mul, mul_one] at hquad
  change ⟪M (x + y), x + y⟫ = ⟪M x, x⟫ + 2 * ⟪M y, x⟫ + ⟪M y, y⟫ at hquad
  rw [hmixed] at hquad
  have hraw : ⟪M x, x⟫ - 2 * c N * (∑ m ∈ Icc 1 Q, q m) ≤
      ⟪M (x + y), x + y⟫ := by linarith only [hsum, hf, hquad]
  change ⟪M x, x⟫ / c N - 2 * (∑ m ∈ Icc 1 Q, q m) ≤ _
  calc
    _ = (⟪M x, x⟫ - 2 * c N * (∑ m ∈ Icc 1 Q, q m)) / c N := by
      field_simp [hc0.ne']
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right hraw hc0.le

/-- At every critical ratio, all packet corrections have a benefit controlled by one polar source. -/
theorem eventually_low_packet_correction_ge_polar_budget
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let x := horizonProfileVector (horizonWeights h N) N
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) x, x⟫ / c N -
        (2 * (interiorTerminalPolarSource h ^ 2 * R / jordanCoefficient 1) + ε) ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) (x + y), x + y⟫ /
          c N := by
  have ht := (tendsto_sum_terminal_source_critical_packet hh hA hsupp hδ hη hlow hhigh
    hc hR hcrit).const_mul 2
  filter_upwards [eventually_low_packet_correction_ge_source_budget hc hR hcrit,
    ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with N hb hs
  intro b Q x y
  exact (sub_le_sub_left hs.le _).trans (hb h b)

/-- On the kernel of the actual polar source, no growing low-packet correction has a limiting gain. -/
theorem eventually_low_packet_correction_ge_zero_source_window
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    (hsource : interiorTerminalPolarSource h = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let x := horizonProfileVector (horizonWeights h N) N
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) x, x⟫ / c N - ε ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) (x + y), x + y⟫ /
          c N := by
  simpa only [hsource, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div, zero_add] using
    eventually_low_packet_correction_ge_polar_budget hh hA hsupp hδ hη hlow hhigh hc hR hcrit hε

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_low_packet_correction_ge_source_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_low_packet_correction_ge_polar_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_low_packet_correction_ge_zero_source_window
