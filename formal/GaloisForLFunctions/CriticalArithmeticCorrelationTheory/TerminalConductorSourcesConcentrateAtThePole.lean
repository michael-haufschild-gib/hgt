import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TerminalConductorSourcesAreSummableBelowOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpperCriticalPacketHasVanishingMixedMass
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalNonpolarSourceAboveHalf
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleCorrectorRetainsItsSignedWindowBenefit
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure

/-!
# Concentration of terminal conductor sources at the pole

For an interior terminal window, every fixed nonpolar source vanishes.
The inverse-energy fifth-power envelope gives uniform convergence below
overlap. The direct high-conductor estimate then covers the entire
packet of logarithmic exponent `13/32`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations ArithmeticDegenerationTheory
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The squared complete source in its actual conductor-energy normalization. -/
def terminalConductorSourceSquare (h : ℝ → ℝ) (c : ℝ) (N m : ℕ) : ℝ :=
  ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N),
    horizonProfileVector (horizonWeights h N) N⟫ ^ 2 /
    (c * completedConductorEnergy tiltedUnitSpline c m)

theorem terminalConductorSourceSquare_nonneg (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (N : ℕ) {m : ℕ} (hm : 0 < m) : 0 ≤ terminalConductorSourceSquare h c N m :=
  div_nonneg (sq_nonneg _) (mul_nonneg hc.le
    (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
      integral_tiltedUnitSpline_sq_pos hc hm))

/-- The polar source retains its exact inverse-energy mass. -/
theorem tendsto_terminalConductorSourceSquare_polar
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => terminalConductorSourceSquare h (c N) N 1) atTop
      (𝓝 (interiorTerminalPolarSource h ^ 2 * R / jordanCoefficient 1)) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hsource := tendsto_complete_terminal_pole_above_half contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hh hA hsupp
    hδ hη hlow hhigh hc hR hcrit
  change Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector 1 N),
      horizonProfileVector (horizonWeights h N) N⟫) atTop
        (𝓝 (interiorTerminalPolarSource h)) at hsource
  have hE : Tendsto (fun N : ℕ => c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) 1)
      atTop (𝓝 (jordanCoefficient 1)) := by
    apply ((tendsto_rpow_seven_mul_completedConductorEnergy_jordan 1).comp hcinf).congr
    intro N
    dsimp only [Function.comp_def]
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have ht := ((hsource.pow 2).mul hcrit).div hE (jordanCoefficient_pos one_pos).ne'
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hfloor := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 one_pos
    (by simpa only [Nat.cast_one] using hc N)
  have hE0 : 0 < completedConductorEnergy tiltedUnitSpline (c N) 1 := by
    have hp : 0 < c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) 1 := by
      have ht := tiltedSplineSpectralFloorConstant_pos
      simpa only [Nat.cast_one, one_pow, mul_one] using ht.trans_le hfloor
    rcases mul_pos_iff.mp hp with hp | hn
    · exact hp.2
    · exact False.elim ((pow_pos hc0 7).not_gt hn.1)
  dsimp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  unfold terminalConductorSourceSquare
  simp only [mul_pow, div_pow, Real.sq_sqrt hL.le]
  field_simp [hc0.ne', hL.ne', hE0.ne']
  <;> ring

/-- Each fixed nonpolar source vanishes also after inverse-energy normalization. -/
theorem tendsto_terminalConductorSourceSquare_nonpolar
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => terminalConductorSourceSquare h (c N) N m) atTop (𝓝 0) := by
  have hm0 : 0 < m := by omega
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hsource := tendsto_complete_terminal_nonpolar_above_half contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hh hA hsupp
    hδ hη hlow hhigh hm hc hR hcrit
  have hE : Tendsto (fun N : ℕ => c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) m)
      atTop (𝓝 (jordanCoefficient m)) := by
    apply ((tendsto_rpow_seven_mul_completedConductorEnergy_jordan m).comp hcinf).congr
    intro N
    dsimp only [Function.comp_def]
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have ht := ((hsource.pow 2).mul hcrit).div hE (jordanCoefficient_pos hm0).ne'
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div] at ht
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    hcinf.eventually_ge_atTop (m : ℝ)] with N hL hmc
  change 0 < Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hEfloor := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 hm0 hmc
  have hE0 : 0 < completedConductorEnergy tiltedUnitSpline (c N) m := by
    have hp := (mul_pos tiltedSplineSpectralFloorConstant_pos (pow_pos (Nat.cast_pos.mpr hm0) 7)).trans_le hEfloor
    rcases mul_pos_iff.mp hp with hp | hn
    · exact hp.2
    · exact False.elim ((pow_pos hc0 7).not_gt hn.1)
  dsimp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  unfold terminalConductorSourceSquare
  simp only [mul_pow, div_pow, Real.sq_sqrt hL.le]
  field_simp [hc0.ne', hL.ne', hE0.ne']
  <;> ring

/-- Zero extension of the nonpolar sources below overlap. -/
def belowOverlapNonpolarSourceSquare (h : ℝ → ℝ) (c : ℝ) (N m : ℕ) : ℝ :=
  if 2 ≤ m ∧ (m : ℝ) ≤ c then terminalConductorSourceSquare h c N m else 0

theorem belowOverlapNonpolarSourceSquare_nonneg (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (N m : ℕ) : 0 ≤ belowOverlapNonpolarSourceSquare h c N m := by
  unfold belowOverlapNonpolarSourceSquare
  split_ifs with hm
  · exact terminalConductorSourceSquare_nonneg h hc N (by omega)
  · exact le_rfl

/-- All nonpolar terminal sources below overlap vanish jointly in squared sum. -/
theorem tendsto_tsum_belowOverlapNonpolarSourceSquare
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑' m : ℕ, belowOverlapNonpolarSourceSquare h (c N) N m)
      atTop (𝓝 0) := by
  obtain ⟨B, _, hB, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨C, hC, hbound⟩ := exists_terminal_complete_inverse_energy_envelope hsupp hB
    (fun x hx => hlow x (hx.trans hδ.le)) hc hR hcrit
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hpoint : ∀ m : ℕ,
      Tendsto (fun N : ℕ => belowOverlapNonpolarSourceSquare h (c N) N m) atTop (𝓝 (0 : ℝ)) := by
    intro m
    by_cases hm : 2 ≤ m
    · apply (tendsto_terminalConductorSourceSquare_nonpolar hh hA hsupp hδ hη hlow hhigh
        hm hc hR hcrit).congr'
      filter_upwards [hcinf.eventually_ge_atTop (m : ℝ)] with N hmc
      simp only [belowOverlapNonpolarSourceSquare, if_pos ⟨hm, hmc⟩]
    · simpa only [belowOverlapNonpolarSourceSquare, hm, false_and, if_false] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hnorm : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      ‖belowOverlapNonpolarSourceSquare h (c N) N m‖ ≤ C / (m : ℝ) ^ 5 := by
    filter_upwards [hbound] with N hN
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg
      (belowOverlapNonpolarSourceSquare_nonneg h (zero_lt_one.trans_le (hc N)) N m)]
    unfold belowOverlapNonpolarSourceSquare
    split_ifs with hm
    · exact hN m (by omega) hm.2
    · positivity
  have hs : Summable (fun m : ℕ => C / (m : ℝ) ^ 5) := by
    have hh : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 5) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (hh.mul_left C).congr fun m => by ring
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs hpoint hnorm

/-- The zero extension is the literal finite sum through the overlap cutoff. -/
theorem tsum_belowOverlapNonpolarSourceSquare_eq (h : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    (∑' m : ℕ, belowOverlapNonpolarSourceSquare h c N m) =
      ∑ m ∈ Icc 2 ⌊c⌋₊, terminalConductorSourceSquare h c N m := by
  have hsupport : ∀ m ∉ Icc 2 ⌊c⌋₊, belowOverlapNonpolarSourceSquare h c N m = 0 := by
    intro m hm
    apply if_neg
    intro h
    exact hm (mem_Icc.mpr ⟨h.1, Nat.le_floor h.2⟩)
  rw [tsum_eq_sum hsupport]
  apply sum_congr rfl
  intro m hm
  exact if_pos ⟨(mem_Icc.mp hm).1,
    (Nat.cast_le.mpr (mem_Icc.mp hm).2).trans (Nat.floor_le hc)⟩

/-- The nonpolar complete source vanishes uniformly over the full moving below-overlap packet. -/
theorem tendsto_sum_nonpolar_source_below_overlap
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑ m ∈ Icc 2 ⌊c N⌋₊, terminalConductorSourceSquare h (c N) N m)
      atTop (𝓝 0) :=
  (tendsto_tsum_belowOverlapNonpolarSourceSquare hh hA hsupp hδ hη hlow hhigh hc hR hcrit).congr
    fun N => tsum_belowOverlapNonpolarSourceSquare_eq h (zero_le_one.trans (hc N)) N

/-- The entire growing logarithmic packet has no nonpolar terminal source in inverse energy. -/
theorem tendsto_sum_nonpolar_terminal_source_critical_packet
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑ m ∈ Icc 2 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
      terminalConductorSourceSquare h (c N) N m) atTop (𝓝 0) := by
  obtain ⟨B, _, hB, _⟩ := exists_bound_lipschitz hh hsupp
  have hlo := tendsto_sum_nonpolar_source_below_overlap hh hA hsupp hδ hη hlow hhigh hc hR hcrit
  have hhi := tendsto_upper_critical_packet_complete_mixed_mass hsupp hB hc hR hcrit
  change Tendsto (fun N : ℕ =>
    ∑ m ∈ (Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊).filter (fun m => c N < (m : ℝ)),
      terminalConductorSourceSquare h (c N) N m) atTop (𝓝 0) at hhi
  have ht := hlo.add hhi
  simp only [zero_add] at ht
  apply squeeze_zero _ _ ht
  · intro N
    exact sum_nonneg fun m hm => terminalConductorSourceSquare_nonneg h
      (zero_lt_one.trans_le (hc N)) N (by have := (mem_Icc.mp hm).1; omega)
  · intro N
    let Q : ℕ := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
    let q := fun m => terminalConductorSourceSquare h (c N) N m
    have hsplit : (∑ m ∈ Icc 2 Q, q m) =
        (∑ m ∈ (Icc 2 Q).filter (fun m => (m : ℝ) ≤ c N), q m) +
        ∑ m ∈ (Icc 2 Q).filter (fun m => c N < (m : ℝ)), q m := by
      simp only [sum_filter]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro m _
      by_cases hm : (m : ℝ) ≤ c N
      · simp only [if_pos hm, if_neg (not_lt_of_ge hm), add_zero]
      · simp only [if_neg hm, if_pos (lt_of_not_ge hm), zero_add]
    change (∑ m ∈ Icc 2 Q, q m) ≤ _
    rw [hsplit]
    apply add_le_add
    · apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨hmQ, hmc⟩ := mem_filter.mp hm
        exact mem_Icc.mpr ⟨(mem_Icc.mp hmQ).1, Nat.le_floor hmc⟩
      · intro m hm _
        exact terminalConductorSourceSquare_nonneg h (zero_lt_one.trans_le (hc N)) N
          (by have := (mem_Icc.mp hm).1; omega)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨hmQ, hmc⟩ := mem_filter.mp hm
        obtain ⟨hm2, hmQ⟩ := mem_Icc.mp hmQ
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hmQ⟩, hmc⟩
      · intro m hm _
        exact terminalConductorSourceSquare_nonneg h (zero_lt_one.trans_le (hc N)) N
          (mem_Icc.mp (mem_filter.mp hm).1).1

/-- The total inverse-energy source mass of the moving packet is exactly polar. -/
theorem tendsto_sum_terminal_source_critical_packet
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {δ η : ℝ} (hδ : (1 / 2 : ℝ) < δ) (hη : η < 1)
    (hlow : ∀ x, x ≤ δ → logProfile h x = 0)
    (hhigh : ∀ x, η ≤ x → logProfile h x = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
      terminalConductorSourceSquare h (c N) N m) atTop
      (𝓝 (interiorTerminalPolarSource h ^ 2 * R / jordanCoefficient 1)) := by
  have ht := (tendsto_terminalConductorSourceSquare_polar hh hA hsupp hδ hη hlow hhigh
    hc hR hcrit).add (tendsto_sum_nonpolar_terminal_source_critical_packet hh hA hsupp
      hδ hη hlow hhigh hc hR hcrit)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hL
  change 1 ≤ Real.log (N : ℝ) at hL
  let Q : ℕ := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
  have hQ : 1 ≤ Q := Nat.le_floor
    (by exact_mod_cast (Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 13 / 32)))
  have hset : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext m
    simp only [mem_Icc, mem_insert]
    omega
  have hnot : 1 ∉ Icc 2 Q := by simp only [mem_Icc]; omega
  change terminalConductorSourceSquare h (c N) N 1 +
    (∑ m ∈ Icc 2 Q, terminalConductorSourceSquare h (c N) N m) =
      ∑ m ∈ Icc 1 Q, terminalConductorSourceSquare h (c N) N m
  rw [hset, sum_insert hnot]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_terminalConductorSourceSquare_nonpolar
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_terminalConductorSourceSquare_polar
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_sum_nonpolar_source_below_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_sum_nonpolar_terminal_source_critical_packet
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_sum_terminal_source_critical_packet
