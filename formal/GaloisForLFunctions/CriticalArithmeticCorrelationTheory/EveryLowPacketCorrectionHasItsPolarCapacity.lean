import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryTerminalWindowHasAPolarConductorSource
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketRetainsItsSignedPolarPart

/-!
# The exact capacity of a terminal low-packet correction

Retaining the positive polar part in the uniform packet approximation
gives a sharp inverse-energy budget. All nonpolar source mass disappears,
and a single growing pole coefficient attains the remaining capacity.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations ArithmeticDegenerationTheory
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem conductor_energy_pos {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    0 < completedConductorEnergy tiltedUnitSpline c m := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  exact (div_pos (div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos)
    integral_tiltedUnitSpline_sq_pos) (pow_pos hc0 7)).trans_le
      (tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc hm)

/-- The inverse-energy budget after retaining the polar part of the packet form. -/
def retainedPoleCorrectionBudget (h : ℝ → ℝ) (c : ℝ) (N : ℕ) (η : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N),
      horizonProfileVector (horizonWeights h N) N⟫ ^ 2 /
      (c * ((1 - η) * completedConductorEnergy tiltedUnitSpline c m +
        if m = 1 then tiltedPolarFinitePart * (c / Real.log N) else 0))

/-- Completing each conductor square preserves the full positive polar denominator. -/
theorem eventually_low_packet_correction_ge_retained_pole_budget
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ (h : ℝ → ℝ) (b : ℕ → ℝ),
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let x := horizonProfileVector (horizonWeights h N) N
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) x, x⟫ / c N -
        retainedPoleCorrectionBudget h (c N) N η ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) (x + y), x + y⟫ /
          c N := by
  filter_upwards [eventually_completeWeil_low_packet_signed_approx hc hR hcrit hη,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N happ hL
  change 1 ≤ Real.log (N : ℝ) at hL
  intro h b Q x y
  let M := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  let P := tiltedPolarFinitePart * (c N / Real.log N)
  let d := fun m => (1 - η) * E m + if m = 1 then P else 0
  let p := fun m => ⟪M (normalizedRamanujanHorizonVector m N), x⟫
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hα : 0 < 1 - η := sub_pos.mpr hη1
  have hP : 0 ≤ P := mul_nonneg tiltedPolarFinitePart_nonneg
    (div_nonneg hc0.le (zero_le_one.trans hL))
  have hQ : 1 ≤ Q := Nat.le_floor
    (by exact_mod_cast Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 13 / 32))
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  have hd : ∀ m ∈ Icc 1 Q, 0 < d m := by
    intro m hm
    apply add_pos_of_pos_of_nonneg (mul_pos hα (conductor_energy_pos (hc N) (mem_Icc.mp hm).1))
    split_ifs
    · exact hP
    · exact le_rfl
  have hpoint : ∀ m ∈ Icc 1 Q,
      -(p m ^ 2 / d m) ≤ d m * b m ^ 2 + 2 * (b m * p m) := by
    intro m hm
    have hdm : 0 < d m := hd m hm
    have hs : 0 ≤ (d m * b m + p m) ^ 2 / d m := by positivity
    have he : (d m * b m + p m) ^ 2 / d m =
        d m * b m ^ 2 + 2 * (b m * p m) + p m ^ 2 / d m := by
      field_simp [(hd m hm).ne'] <;> ring
    rw [he] at hs
    linarith only [hs]
  have hsum := sum_le_sum hpoint
  rw [sum_neg_distrib, sum_add_distrib, ← mul_sum] at hsum
  have hpolar : (∑ m ∈ Icc 1 Q, (if m = 1 then P else 0) * b m ^ 2) = P * b 1 ^ 2 := by
    rw [sum_eq_single_of_mem 1 h1]
    · rw [if_pos rfl]
    · intro m hm hm1
      rw [if_neg hm1, zero_mul]
  have hdform : (∑ m ∈ Icc 1 Q, d m * b m ^ 2) =
      (1 - η) * (∑ m ∈ Icc 1 Q, E m * b m ^ 2) + P * b 1 ^ 2 := by
    simp only [d, add_mul, mul_assoc, sum_add_distrib, ← mul_sum, hpolar]
  have hfloor := (abs_le.mp (happ b)).1
  change -(η * (∑ m ∈ Icc 1 Q, E m * b m ^ 2)) ≤
    ⟪M y, y⟫ - (∑ m ∈ Icc 1 Q, E m * b m ^ 2) - P * b 1 ^ 2 at hfloor
  have hf : (∑ m ∈ Icc 1 Q, d m * b m ^ 2) ≤ ⟪M y, y⟫ := by
    rw [hdform]
    linarith only [hfloor]
  have hmixed : ⟪M y, x⟫ = ∑ m ∈ Icc 1 Q, b m * p m := by
    simp only [y, map_sum, map_smul, sum_inner, real_inner_smul_left, p]
  have hM := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N)
  have hquad := HTGeometry.tInner_self_add_smul hM x y 1
  rw [HTGeometry.tInner_comm hM x y] at hquad
  simp only [HTGeometry.tInner_def, one_smul, mul_one] at hquad
  change ⟪M (x + y), x + y⟫ = ⟪M y, y⟫ + 2 * ⟪M y, x⟫ + ⟪M x, x⟫ at hquad
  rw [hmixed] at hquad
  have hraw : ⟪M x, x⟫ - (∑ m ∈ Icc 1 Q, p m ^ 2 / d m) ≤
      ⟪M (x + y), x + y⟫ := by linarith only [hsum, hf, hquad]
  have hbudget : retainedPoleCorrectionBudget h (c N) N η =
      (∑ m ∈ Icc 1 Q, p m ^ 2 / d m) / c N := by
    rw [sum_div]
    apply sum_congr rfl
    intro m _
    dsimp only [retainedPoleCorrectionBudget, p, d, E, P, M, x]
    ring
  rw [hbudget]
  change ⟪M x, x⟫ / c N - _ ≤ _
  rw [← sub_div]
  exact div_le_div_of_nonneg_right hraw hc0.le

private theorem retainedPoleCorrectionBudget_eq
    (h : ℝ → ℝ) {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hL : 1 ≤ Real.log (N : ℝ))
    {η : ℝ} (hη1 : η < 1) :
    retainedPoleCorrectionBudget h c N η =
      (Real.sqrt (Real.log N) / c *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector 1 N),
          horizonProfileVector (horizonWeights h N) N⟫) ^ 2 /
        ((1 - η) * (Real.log N / c * completedConductorEnergy tiltedUnitSpline c 1) +
          tiltedPolarFinitePart) +
      (∑ m ∈ Icc 2 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
        terminalConductorSourceSquare h c N m) / (1 - η) := by
  let Q : ℕ := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hα : 0 < 1 - η := sub_pos.mpr hη1
  have hQ : 1 ≤ Q := Nat.le_floor
    (by exact_mod_cast Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 13 / 32))
  have hset : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext m
    simp only [mem_Icc, mem_insert]
    omega
  have hnot : 1 ∉ Icc 2 Q := by simp only [mem_Icc]; omega
  unfold retainedPoleCorrectionBudget
  change (∑ m ∈ Icc 1 Q, _) = _
  rw [hset, sum_insert hnot]
  apply congrArg₂ (· + ·)
  · rw [if_pos rfl]
    have hE := conductor_energy_pos hc (m := 1) one_pos
    have hd : 0 < (1 - η) * (Real.log N / c * completedConductorEnergy tiltedUnitSpline c 1) +
        tiltedPolarFinitePart := add_pos_of_pos_of_nonneg (by positivity) tiltedPolarFinitePart_nonneg
    have hd' : 0 < (1 - η) * completedConductorEnergy tiltedUnitSpline c 1 +
        tiltedPolarFinitePart * (c / Real.log N) :=
      add_pos_of_pos_of_nonneg (mul_pos hα hE)
        (mul_nonneg tiltedPolarFinitePart_nonneg (div_nonneg hc0.le hL0.le))
    simp only [mul_pow, div_pow, Real.sq_sqrt hL0.le]
    field_simp [hc0.ne', hL0.ne', hd.ne', hd'.ne'] <;> ring
  · rw [sum_div]
    apply sum_congr rfl
    intro m hm
    have hm1 : m ≠ 1 := by have := (mem_Icc.mp hm).1; omega
    rw [if_neg hm1, add_zero]
    unfold terminalConductorSourceSquare
    ring

private theorem tendsto_critical_pole_reference_cost
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.log N / c N * completedConductorEnergy tiltedUnitSpline (c N) 1)
      atTop (𝓝 (jordanCoefficient 1 / R)) := by
  have hJ := (tendsto_rpow_seven_mul_completedConductorEnergy_jordan 1).comp
    (criticalCurve_facts hc hR hcrit).1
  have ht := hJ.div hcrit hR.ne'
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  dsimp only [Function.comp_def]
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  field_simp [hc0.ne', hL.ne'] <;> ring

/-- The retained inverse-energy budget has exactly one limiting polar charge. -/
theorem tendsto_retainedPoleCorrectionBudget
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {η : ℝ} (hη1 : η < 1) :
    Tendsto (fun N : ℕ => retainedPoleCorrectionBudget h (c N) N η) atTop
      (𝓝 (generalTerminalPolarSource A h ^ 2 /
        ((1 - η) * (jordanCoefficient 1 / R) + tiltedPolarFinitePart))) := by
  have hsource := tendsto_complete_terminal_pole contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hh hA hsupp hc hR hcrit
  change Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector 1 N),
      horizonProfileVector (horizonWeights h N) N⟫) atTop
        (𝓝 (generalTerminalPolarSource A h)) at hsource
  have hden := ((tendsto_critical_pole_reference_cost hc hR hcrit).const_mul (1 - η)).add_const
    tiltedPolarFinitePart
  have hd : 0 < (1 - η) * (jordanCoefficient 1 / R) + tiltedPolarFinitePart :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hη1)
      (div_pos (jordanCoefficient_pos one_pos) hR)) tiltedPolarFinitePart_nonneg
  have hpolar := (hsource.pow 2).div hden hd.ne'
  have hnonpolar := (tendsto_sum_nonpolar_terminal_source_critical_packet_all_windows
    hh hA hsupp hc hR hcrit).div_const (1 - η)
  have ht := hpolar.add hnonpolar
  simp only [zero_div, add_zero] at ht
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hL
  exact (retainedPoleCorrectionBudget_eq h (hc N) hL hη1).symm

private theorem criticalPoleWindowCost_eq {R : ℝ} (hR : 0 < R) :
    criticalPoleWindowCost R = jordanCoefficient 1 / R + tiltedPolarFinitePart := by
  unfold criticalPoleWindowCost criticalGenusCoefficient tiltedPolarFinitePart RHTower.poleSharpConstant
  field_simp [hR.ne'] <;> ring

/-- No low-packet coefficient family improves a compact window beyond its exact polar capacity. -/
theorem eventually_low_packet_correction_ge_sharp_polar_capacity
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let x := horizonProfileVector (horizonWeights h N) N
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) x, x⟫ / c N -
        (generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R + ε) ≤
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) (x + y), x + y⟫ /
          c N := by
  let S := generalTerminalPolarSource A h
  let D := criticalPoleWindowCost R
  have hD : 0 < D := criticalPoleWindowCost_pos hR
  have hden := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (tendsto_const_div_atTop_nhds_zero_nat 1)).mul_const (jordanCoefficient 1 / R)).add_const
      tiltedPolarFinitePart
  simp only [sub_zero, one_mul, ← criticalPoleWindowCost_eq hR] at hden
  have hgain := (tendsto_const_nhds : Tendsto (fun _ : ℕ => S ^ 2) atTop (𝓝 (S ^ 2))).div hden hD.ne'
  obtain ⟨k, hk, hkgain⟩ := ((eventually_ge_atTop 2).and
    (hgain.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε))))).exists
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  let η : ℝ := 1 / k
  have hη : 0 < η := div_pos zero_lt_one hk0
  have hη1 : η < 1 := (div_lt_one hk0).mpr hk1
  have ht := tendsto_retainedPoleCorrectionBudget hh hA hsupp hc hR hcrit hη1
  filter_upwards [eventually_low_packet_correction_ge_retained_pole_budget hc hR hcrit hη hη1,
    ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε)))] with N hbound hbudget
  intro b Q x y
  have htotal : retainedPoleCorrectionBudget h (c N) N η < S ^ 2 / D + ε := by
    change S ^ 2 / ((1 - η) * (jordanCoefficient 1 / R) + tiltedPolarFinitePart) <
      S ^ 2 / D + ε / 2 at hkgain
    change retainedPoleCorrectionBudget h (c N) N η <
      S ^ 2 / ((1 - η) * (jordanCoefficient 1 / R) + tiltedPolarFinitePart) + ε / 2 at hbudget
    linarith only [hkgain, hbudget]
  exact (sub_le_sub_left htotal.le _).trans (hbound h b)

/-- A single growing pole coefficient attains the capacity of the entire low packet. -/
theorem tendsto_pole_corrector_attains_terminal_capacity
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      let x := horizonProfileVector (horizonWeights h N) N
      let z := x + ((-generalTerminalPolarSource A h / criticalPoleWindowCost R) *
        Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector 1 N
      (⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫ -
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) x, x⟫) / c N)
      atTop (𝓝 (-(generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R))) := by
  let S := generalTerminalPolarSource A h
  let D := criticalPoleWindowCost R
  let t := -S / D
  have hD : 0 < D := criticalPoleWindowCost_pos hR
  have hsource := tendsto_complete_terminal_pole contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hh hA hsupp hc hR hcrit
  change Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector 1 N),
      horizonProfileVector (horizonWeights h N) N⟫) atTop (𝓝 S) at hsource
  have ht := (hsource.const_mul (2 * t)).add
    ((tendsto_critical_pole_window_cost hc hR hcrit).const_mul (t ^ 2))
  have he : 2 * t * S + t ^ 2 * D = -(S ^ 2 / D) := by
    dsimp only [t]
    field_simp [hD.ne'] <;> ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  let x := horizonProfileVector (horizonWeights h N) N
  let v := normalizedRamanujanHorizonVector 1 N
  let M := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
  have hM := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N)
  have hquad := HTGeometry.tInner_self_add_smul hM x v (t * Real.sqrt (Real.log N))
  rw [HTGeometry.tInner_comm hM x v] at hquad
  simp only [HTGeometry.tInner_def] at hquad
  have hsquare : (t * Real.sqrt (Real.log N)) * (t * Real.sqrt (Real.log N)) =
      t ^ 2 * Real.log N := by
    calc
      _ = t ^ 2 * (Real.sqrt (Real.log N)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL.le]
  rw [hsquare] at hquad
  change _ = (⟪M (x + (t * Real.sqrt (Real.log N)) • v),
    x + (t * Real.sqrt (Real.log N)) • v⟫ - ⟪M x, x⟫) / c N
  rw [hquad]
  dsimp only [M, x, v]
  ring

/-- The optimally corrected complete energy retains precisely the polar capacity. -/
theorem tendsto_optimized_terminal_window_energy
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      let x := horizonProfileVector (horizonWeights h N) N
      let z := x + ((-generalTerminalPolarSource A h / criticalPoleWindowCost R) *
        Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector 1 N
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) z, z⟫ / c N)
      atTop (𝓝 (((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h) +
        7 * tiltedJordanOne / R * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) -
        generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R)) := by
  let x := fun N : ℕ => horizonProfileVector (horizonWeights h N) N
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
  have ht := hbase.add (tendsto_pole_corrector_attains_terminal_capacity hh hA hsupp hc hR hcrit)
  simp only [← sub_eq_add_neg] at ht
  apply ht.congr
  intro N
  dsimp only [B, x]
  ring

/-- The established critical band pays the optimized polar charge of every compact window. -/
theorem exists_critical_band_all_windows_ge_polar_capacity :
    ∃ K : ℝ, 0 < K ∧ 2 * K ≤ 1 ∧
      ∀ R : ℝ, 0 < R → R ≤ (2 * K) ^ 8 →
        ∀ {h : ℝ → ℝ} {A : ℝ}, ContDiff ℝ 2 h → 0 ≤ A →
          (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
          generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R ≤
            ((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
              weilQuad (halfWeight h) +
            7 * tiltedJordanOne / R * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
  obtain ⟨K, hK, h2K, hfloor⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  refine ⟨K, hK, h2K, ?_⟩
  intro R hR hRK h A hh hA hsupp
  let c := canonicalCriticalCurve R
  have hc : ∀ N, 1 ≤ c N := one_le_canonicalCriticalCurve R
  have hcrit := tendsto_canonicalCriticalCurve_pow_eight hR
  have ht := tendsto_optimized_terminal_window_energy hh hA hsupp hc hR hcrit
  apply sub_nonneg.mp
  apply ge_of_tendsto ht
  filter_upwards [hfloor, eventually_canonicalCriticalCurve_le_and_eq hK hR hRK]
    with N hN hband
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  let z := horizonProfileVector (horizonWeights h N) N +
    ((-generalTerminalPolarSource A h / criticalPoleWindowCost R) *
      Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector 1 N
  have hz := hN (c N) (hc N) hband.1 z
  have hκ := tiltedSplineSpectralFloorConstant_pos
  have hz0 : 0 ≤ completeWeilEnergy tiltedUnitSpline (c N) N z :=
    (by positivity : 0 ≤ tiltedSplineSpectralFloorConstant / (2 * c N ^ 7) * ‖z‖ ^ 2).trans hz
  exact div_nonneg hz0 hc0.le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_low_packet_correction_ge_retained_pole_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_retainedPoleCorrectionBudget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_low_packet_correction_ge_sharp_polar_capacity
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_pole_corrector_attains_terminal_capacity
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_optimized_terminal_window_energy
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_critical_band_all_windows_ge_polar_capacity
