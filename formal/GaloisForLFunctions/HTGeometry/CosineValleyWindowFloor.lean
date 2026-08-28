import GaloisForLFunctions.HTGeometry.CosineSublevelPeriodMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# All-phase, all-frequency valley floor for the cosine

Every logarithmic-scale window `(0, U]` meets the deep valley `{cos (γ·u + φ) ≤ -1/2}` of a
single-frequency oscillation in measure at least `U/3 - 2π/(3γ)`, for every frequency `γ > 0`
and every phase `φ`.  The chain: the deep sublevel set of the cosine is `2π`-periodic and fills
exactly one third of every period (window-position independent, by periodicity of the indicator
and translation invariance of Lebesgue measure), so `n` consecutive periods carry exactly
`n·(2π/3)`, and an affine change of variable transports the floor to arbitrary frequency and
phase.  The pigeonhole corollary is the incompatibility engine for single-frequency anomalies:
any function bounded below outside a set of measure less than the valley floor must meet the
valley — a one-sided bound holding past two thirds of scales is incompatible with a persistent
half-amplitude single-frequency deficit.
-/

open Real Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The deep sublevel set of the cosine: phases where `cos` is below half its minimum. -/
def cosDeepSublevel : Set ℝ := {v : ℝ | Real.cos v ≤ -(1 / 2)}

theorem measurableSet_cosDeepSublevel : MeasurableSet cosDeepSublevel :=
  measurableSet_le Real.continuous_cos.measurable measurable_const

/-- The deep sublevel set is `2π`-periodic. -/
theorem cosDeepSublevel_add_two_pi (v : ℝ) :
    v + 2 * π ∈ cosDeepSublevel ↔ v ∈ cosDeepSublevel := by
  simp [cosDeepSublevel, Real.cos_add_two_pi]

/-- The indicator of the deep sublevel set is a periodic function. -/
theorem periodic_indicator_cosDeepSublevel :
    Function.Periodic (cosDeepSublevel.indicator (fun _ => (1 : ℝ))) (2 * π) := by
  intro v
  by_cases h : v ∈ cosDeepSublevel
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((cosDeepSublevel_add_two_pi v).2 h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hc => h ((cosDeepSublevel_add_two_pi v).1 hc))]

/-- In the base period window the deep sublevel set is exactly the middle third. -/
theorem cosDeepSublevel_inter_Ioc_zero :
    cosDeepSublevel ∩ Ioc (0 : ℝ) (2 * π) = Icc (2 * π / 3) (4 * π / 3) := by
  have hpi := Real.pi_pos
  ext v
  constructor
  · rintro ⟨hv, h0, h2⟩
    have hmem : v ∈ {v ∈ Icc (0 : ℝ) (2 * π) | Real.cos v ≤ -(1 / 2)} :=
      ⟨⟨le_of_lt h0, h2⟩, hv⟩
    rwa [cos_sublevel_period_eq] at hmem
  · intro hv
    have hv' : v ∈ {v ∈ Icc (0 : ℝ) (2 * π) | Real.cos v ≤ -(1 / 2)} := by
      rw [cos_sublevel_period_eq]; exact hv
    obtain ⟨⟨_, h2⟩, hc⟩ := hv'
    exact ⟨hc, lt_of_lt_of_le (by positivity) hv.1, h2⟩

theorem volume_cosDeepSublevel_inter_Ioc_zero :
    volume (cosDeepSublevel ∩ Ioc (0 : ℝ) (2 * π)) = ENNReal.ofReal (2 * π / 3) := by
  rw [cosDeepSublevel_inter_Ioc_zero, Real.volume_Icc]
  congr 1
  ring

/-- **Window-position independence**: every window of one full period carries deep sublevel
measure exactly `2π/3`, wherever the window sits. -/
theorem volume_cosDeepSublevel_inter_Ioc (c : ℝ) :
    volume (cosDeepSublevel ∩ Ioc c (c + 2 * π)) = ENNReal.ofReal (2 * π / 3) := by
  have hpi := Real.pi_pos
  have hint : ∀ a : ℝ, ∫ x in a..(a + 2 * π), cosDeepSublevel.indicator (fun _ => (1 : ℝ)) x
      = (volume (cosDeepSublevel ∩ Ioc a (a + 2 * π))).toReal := by
    intro a
    rw [intervalIntegral.integral_of_le (by linarith),
      ← MeasureTheory.integral_indicator measurableSet_Ioc, Set.indicator_indicator,
      MeasureTheory.integral_indicator_const _
        (measurableSet_Ioc.inter measurableSet_cosDeepSublevel), Set.inter_comm]
    simp [MeasureTheory.measureReal_def]
  have hbase : volume (cosDeepSublevel ∩ Ioc (0 : ℝ) (0 + 2 * π)) = ENNReal.ofReal (2 * π / 3) := by
    rw [zero_add]
    exact volume_cosDeepSublevel_inter_Ioc_zero
  have hfin : volume (cosDeepSublevel ∩ Ioc c (c + 2 * π)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hfin0 : volume (cosDeepSublevel ∩ Ioc (0 : ℝ) (0 + 2 * π)) ≠ ⊤ := by
    rw [hbase]; exact ENNReal.ofReal_ne_top
  have hper := periodic_indicator_cosDeepSublevel.intervalIntegral_add_eq c 0
  rw [hint c, hint 0] at hper
  rw [← ENNReal.ofReal_toReal hfin, hper, ENNReal.ofReal_toReal hfin0, hbase]

/-- `n` consecutive periods carry deep sublevel measure exactly `n·(2π/3)`. -/
theorem volume_cosDeepSublevel_inter_Ioc_nat (c : ℝ) (n : ℕ) :
    volume (cosDeepSublevel ∩ Ioc c (c + n * (2 * π)))
      = ENNReal.ofReal (n * (2 * π / 3)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hpi := Real.pi_pos
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    have h1 : c ≤ c + (m : ℝ) * (2 * π) := by nlinarith
    have h2 : c + (m : ℝ) * (2 * π) ≤ c + ((m : ℝ) + 1) * (2 * π) := by nlinarith
    have hunion : Ioc c (c + ((m : ℝ) + 1) * (2 * π))
        = Ioc c (c + (m : ℝ) * (2 * π))
          ∪ Ioc (c + (m : ℝ) * (2 * π)) (c + ((m : ℝ) + 1) * (2 * π)) :=
      (Set.Ioc_union_Ioc_eq_Ioc h1 h2).symm
    have hdisj : Disjoint
        (cosDeepSublevel ∩ Ioc c (c + (m : ℝ) * (2 * π)))
        (cosDeepSublevel ∩ Ioc (c + (m : ℝ) * (2 * π)) (c + ((m : ℝ) + 1) * (2 * π))) := by
      refine Disjoint.mono inter_subset_right inter_subset_right ?_
      rw [Set.disjoint_left]
      rintro x ⟨_, hx2⟩ ⟨hx3, _⟩
      exact absurd hx3 (not_lt.mpr hx2)
    rw [hunion, Set.inter_union_distrib_left,
      measure_union hdisj (measurableSet_cosDeepSublevel.inter measurableSet_Ioc), ih,
      show c + ((m : ℝ) + 1) * (2 * π) = (c + (m : ℝ) * (2 * π)) + 2 * π by ring,
      volume_cosDeepSublevel_inter_Ioc,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

/-- **The valley floor at unit frequency**: every window `(a, b]` carries deep sublevel
measure at least `(b-a)/3 - 2π/3`. -/
theorem le_volume_cosDeepSublevel_inter_Ioc (a b : ℝ) :
    ENNReal.ofReal ((b - a) / 3 - 2 * π / 3) ≤ volume (cosDeepSublevel ∩ Ioc a b) := by
  have hpi := Real.pi_pos
  rcases le_or_gt ((b - a) / 3 - 2 * π / 3) 0 with hneg | hpos
  · rw [ENNReal.ofReal_eq_zero.mpr hneg]
    exact zero_le
  · have h2pi : (0 : ℝ) < 2 * π := by linarith
    have hba : 2 * π < b - a := by linarith
    have hq : (0 : ℝ) ≤ (b - a) / (2 * π) := div_nonneg (by linarith) (by positivity)
    have hfl : (⌊(b - a) / (2 * π)⌋₊ : ℝ) ≤ (b - a) / (2 * π) := Nat.floor_le hq
    have hfl' : (b - a) / (2 * π) < ⌊(b - a) / (2 * π)⌋₊ + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ h2pi] at hfl
    rw [div_lt_iff₀ h2pi] at hfl'
    have hnb : a + (⌊(b - a) / (2 * π)⌋₊ : ℝ) * (2 * π) ≤ b := by linarith
    calc ENNReal.ofReal ((b - a) / 3 - 2 * π / 3)
        ≤ ENNReal.ofReal ((⌊(b - a) / (2 * π)⌋₊ : ℝ) * (2 * π / 3)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = volume (cosDeepSublevel ∩ Ioc a (a + (⌊(b - a) / (2 * π)⌋₊ : ℝ) * (2 * π))) :=
          (volume_cosDeepSublevel_inter_Ioc_nat a _).symm
      _ ≤ volume (cosDeepSublevel ∩ Ioc a b) :=
          measure_mono (inter_subset_inter_right _ (Ioc_subset_Ioc_right hnb))

/-- **The all-phase, all-frequency valley floor.**  For every frequency `γ > 0`, phase `φ`, and
horizon `U`, the deep valley of `cos (γ·u + φ)` inside `(0, U]` has measure at least
`U/3 - 2π/(3γ)`: a single-frequency oscillation spends a third of all scales, minus one period's
boundary cost, at depth half its amplitude. -/
theorem le_volume_cos_valley_window (γ φ U : ℝ) (hγ : 0 < γ) :
    ENNReal.ofReal (U / 3 - 2 * π / (3 * γ)) ≤
      volume {u ∈ Ioc (0 : ℝ) U | Real.cos (γ * u + φ) ≤ -(1 / 2)} := by
  have hγ' : γ ≠ 0 := ne_of_gt hγ
  have hset : {u ∈ Ioc (0 : ℝ) U | Real.cos (γ * u + φ) ≤ -(1 / 2)}
      = (fun u : ℝ => γ * u) ⁻¹'
          ((fun v : ℝ => v + φ) ⁻¹' (cosDeepSublevel ∩ Ioc φ (φ + γ * U))) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc,
      cosDeepSublevel, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h0, hU⟩, hc⟩
      have ha : 0 < γ * u := mul_pos hγ h0
      have hb : γ * u ≤ γ * U := mul_le_mul_of_nonneg_left hU hγ.le
      exact ⟨hc, by linarith, by linarith⟩
    · rintro ⟨hc, h1, h2⟩
      have ha : 0 < γ * u := by linarith
      have hb : γ * u ≤ γ * U := by linarith
      have h0u : 0 < u := by
        by_contra h
        rw [not_lt] at h
        nlinarith [mul_nonneg hγ.le (neg_nonneg.mpr h)]
      exact ⟨⟨h0u, le_of_mul_le_mul_left hb hγ⟩, hc⟩
  rw [hset]
  have hmeasB : MeasurableSet
      ((fun v : ℝ => v + φ) ⁻¹' (cosDeepSublevel ∩ Ioc φ (φ + γ * U))) :=
    (measurableSet_cosDeepSublevel.inter measurableSet_Ioc).preimage (by fun_prop)
  have hmap : volume ((fun u : ℝ => γ * u) ⁻¹'
        ((fun v : ℝ => v + φ) ⁻¹' (cosDeepSublevel ∩ Ioc φ (φ + γ * U))))
      = ENNReal.ofReal |γ⁻¹|
          * volume ((fun v : ℝ => v + φ) ⁻¹' (cosDeepSublevel ∩ Ioc φ (φ + γ * U))) := by
    rw [← MeasureTheory.Measure.map_apply (by fun_prop) hmeasB, Real.map_volume_mul_left hγ']
    simp
  rw [hmap, MeasureTheory.measure_preimage_add_right]
  have hfloor := le_volume_cosDeepSublevel_inter_Ioc φ (φ + γ * U)
  have harg : φ + γ * U - φ = γ * U := by ring
  rw [harg] at hfloor
  calc ENNReal.ofReal (U / 3 - 2 * π / (3 * γ))
      = ENNReal.ofReal |γ⁻¹| * ENNReal.ofReal (γ * U / 3 - 2 * π / 3) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr hγ)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal |γ⁻¹|
          * volume (cosDeepSublevel ∩ Ioc φ (φ + γ * U)) := by
        gcongr

/-- **The single-frequency pigeonhole.**  Any set `G ⊆ (0, U]` whose complement in `(0, U]` has
measure strictly below the valley floor `U/3 - 2π/(3γ)` must contain a scale lying in the deep
valley of `cos (γ·u + φ)`.  This is the incompatibility engine for single-frequency anomalies:
a one-sided bound valid past two thirds of scales cannot coexist with a persistent
half-amplitude cosine deficit.  No measurability of `G` is required. -/
theorem exists_valley_mem_of_volume_compl_lt (γ φ U : ℝ) (hγ : 0 < γ) {G : Set ℝ}
    (hvol : volume (Ioc (0 : ℝ) U \ G) < ENNReal.ofReal (U / 3 - 2 * π / (3 * γ))) :
    ∃ u ∈ G, Real.cos (γ * u + φ) ≤ -(1 / 2) := by
  by_contra hempty
  have hsub : {u ∈ Ioc (0 : ℝ) U | Real.cos (γ * u + φ) ≤ -(1 / 2)}
      ⊆ Ioc (0 : ℝ) U \ G := by
    rintro u ⟨hu, hc⟩
    exact ⟨hu, fun huG => hempty ⟨u, huG, hc⟩⟩
  exact absurd ((le_volume_cos_valley_window γ φ U hγ).trans (measure_mono hsub))
    (not_le.mpr hvol)

end GaloisForLFunctions.HTGeometry
