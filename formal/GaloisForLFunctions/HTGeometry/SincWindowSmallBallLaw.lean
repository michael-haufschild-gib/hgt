import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Finite-window small-ball bounds for sine responses

A sine sublevel occupies at most a threshold-proportional fraction of each
period. Covering a finite window by complete periods costs one boundary period.
-/

open Real Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

def absSinSublevel (u : ℝ) : Set ℝ := {t | |Real.sin t| ≤ u}

theorem measurableSet_absSinSublevel (u : ℝ) :
    MeasurableSet (absSinSublevel u) :=
  measurableSet_le Real.continuous_sin.abs.measurable measurable_const

theorem periodic_indicator_absSinSublevel (u : ℝ) :
    Function.Periodic ((absSinSublevel u).indicator (fun _ => (1 : ℝ))) π := by
  intro t
  have hp : t + π ∈ absSinSublevel u ↔ t ∈ absSinSublevel u := by
    simp only [absSinSublevel, mem_setOf_eq, Real.sin_add_pi, abs_neg]
  by_cases ht : t ∈ absSinSublevel u
  · rw [indicator_of_mem ht, indicator_of_mem (hp.mpr ht)]
  · rw [indicator_of_notMem ht, indicator_of_notMem (mt hp.mp ht)]

/-- On a half-period, concavity places every small value near an endpoint. -/
theorem absSinSublevel_inter_Ioc_subset (u : ℝ) :
    absSinSublevel u ∩ Ioc (0 : ℝ) π ⊆
      Icc (0 : ℝ) (π * u / 2) ∪ Icc (π - π * u / 2) π := by
  rintro t ⟨ht, h0, hπ⟩
  have hs : Real.sin t ≤ u := (le_abs_self _).trans ht
  rcases le_total t (π / 2) with hhalf | hhalf
  · left
    refine ⟨h0.le, ?_⟩
    have hchord := Real.mul_le_sin h0.le hhalf
    have hbound : 2 / π * t ≤ u := hchord.trans hs
    have hmul := mul_le_mul_of_nonneg_right hbound Real.pi_pos.le
    have hcancel : (2 / π * t) * π = 2 * t := by field_simp
    rw [hcancel] at hmul
    linarith
  · right
    refine ⟨?_, hπ⟩
    have hchord := Real.mul_le_sin (show 0 ≤ π - t by linarith)
      (show π - t ≤ π / 2 by linarith)
    rw [Real.sin_pi_sub] at hchord
    have hmul := mul_le_mul_of_nonneg_right (hchord.trans hs) Real.pi_pos.le
    have hcancel : (2 / π * (π - t)) * π = 2 * (π - t) := by field_simp
    rw [hcancel] at hmul
    linarith

theorem volume_absSinSublevel_inter_Ioc_zero_le (u : ℝ) (hu : 0 ≤ u) :
    volume (absSinSublevel u ∩ Ioc (0 : ℝ) π) ≤ ENNReal.ofReal (π * u) := by
  calc
    _ ≤ volume (Icc (0 : ℝ) (π * u / 2) ∪ Icc (π - π * u / 2) π) :=
      measure_mono (absSinSublevel_inter_Ioc_subset u)
    _ ≤ volume (Icc (0 : ℝ) (π * u / 2)) +
        volume (Icc (π - π * u / 2) π) := measure_union_le _ _
    _ = ENNReal.ofReal (π * u) := by
      rw [Real.volume_Icc, Real.volume_Icc, sub_zero,
        show π - (π - π * u / 2) = π * u / 2 by ring,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

theorem volume_absSinSublevel_inter_Ioc (u c : ℝ) :
    volume (absSinSublevel u ∩ Ioc c (c + π)) =
      volume (absSinSublevel u ∩ Ioc (0 : ℝ) π) := by
  have hint (a : ℝ) :
      (∫ x in a..(a + π), (absSinSublevel u).indicator (fun _ => (1 : ℝ)) x) =
        (volume (absSinSublevel u ∩ Ioc a (a + π))).toReal := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      ← MeasureTheory.integral_indicator measurableSet_Ioc, indicator_indicator,
      MeasureTheory.integral_indicator_const _
        (measurableSet_Ioc.inter (measurableSet_absSinSublevel u)), inter_comm]
    simp only [MeasureTheory.measureReal_def, smul_eq_mul, mul_one]
  have hfin (a : ℝ) : volume (absSinSublevel u ∩ Ioc a (a + π)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hp := (periodic_indicator_absSinSublevel u).intervalIntegral_add_eq c 0
  rw [hint c, hint 0] at hp
  have heq : volume (absSinSublevel u ∩ Ioc c (c + π)) =
      volume (absSinSublevel u ∩ Ioc (0 : ℝ) (0 + π)) := by
    rw [← ENNReal.ofReal_toReal (hfin c), hp, ENNReal.ofReal_toReal (hfin 0)]
  simpa only [zero_add] using heq

theorem volume_absSinSublevel_inter_Ioc_nat_le (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    volume (absSinSublevel u ∩ Ioc (0 : ℝ) (n * π)) ≤
      ENNReal.ofReal (n * (π * u)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n * π := mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le
    have hnext : (n : ℝ) * π ≤ n * π + π := le_add_of_nonneg_right Real.pi_pos.le
    rw [Nat.cast_succ, add_mul, one_mul,
      ← Ioc_union_Ioc_eq_Ioc hn hnext, inter_union_distrib_left]
    calc
      _ ≤ volume (absSinSublevel u ∩ Ioc (0 : ℝ) (n * π)) +
          volume (absSinSublevel u ∩ Ioc (n * π) (n * π + π)) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (n * (π * u)) + ENNReal.ofReal (π * u) :=
        add_le_add ih (by
          rw [volume_absSinSublevel_inter_Ioc]
          exact volume_absSinSublevel_inter_Ioc_zero_le u hu)
      _ = ENNReal.ofReal (((n : ℝ) + 1) * (π * u)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- A finite window costs at most one extra period; no frequency-separation
assumption enters the scalar estimate. -/
theorem volume_absSinSublevel_inter_Ioc_le (u L : ℝ) (hu : 0 ≤ u) (hL : 0 ≤ L) :
    volume (absSinSublevel u ∩ Ioc (0 : ℝ) L) ≤
      ENNReal.ofReal ((L + π) * u) := by
  let n := ⌊L / π⌋₊ + 1
  have hupper : L ≤ (n : ℝ) * π := by
    have h := Nat.lt_floor_add_one (L / π)
    rw [div_lt_iff₀ Real.pi_pos] at h
    simpa only [n, Nat.cast_add, Nat.cast_one] using h.le
  have hlower : (n : ℝ) * π ≤ L + π := by
    have h := Nat.floor_le (div_nonneg hL Real.pi_pos.le)
    rw [le_div_iff₀ Real.pi_pos] at h
    dsimp [n]
    push_cast
    nlinarith only [h]
  calc
    _ ≤ volume (absSinSublevel u ∩ Ioc (0 : ℝ) (n * π)) :=
      measure_mono (inter_subset_inter_right _ (Ioc_subset_Ioc_right hupper))
    _ ≤ ENNReal.ofReal (n * (π * u)) :=
      volume_absSinSublevel_inter_Ioc_nat_le u hu n
    _ ≤ ENNReal.ofReal ((L + π) * u) :=
      ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_right hlower hu])

/-- Rescaling the half-period estimate controls the integrated differential
response even when its oscillation frequency approaches zero. -/
theorem volume_sincResponse_inter_Ioc_le_of_pos (ω T x : ℝ)
    (hω : 0 < ω) (hT : 0 ≤ T) (hx : 0 ≤ x) :
    volume {t ∈ Ioc (0 : ℝ) T | |t * Real.sinc (ω * t)| ≤ x} ≤
      ENNReal.ofReal ((ω * T + π) * x) := by
  have hresponse (t : ℝ) : t * Real.sinc (ω * t) = Real.sin (ω * t) / ω := by
    by_cases ht : t = 0
    · simp only [ht, mul_zero, zero_mul, Real.sin_zero, zero_div]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hω.ne' ht)]
      field_simp
  have hset : {t ∈ Ioc (0 : ℝ) T | |t * Real.sinc (ω * t)| ≤ x} =
      (fun t : ℝ => ω * t) ⁻¹' (absSinSublevel (ω * x) ∩ Ioc 0 (ω * T)) := by
    ext t
    simp only [mem_setOf_eq, mem_Ioc, mem_preimage, mem_inter_iff,
      absSinSublevel, hresponse, abs_div, abs_of_pos hω, div_le_iff₀ hω]
    constructor
    · rintro ⟨⟨ht0, htT⟩, hs⟩
      exact ⟨by simpa only [mul_comm x ω] using hs,
        mul_pos hω ht0, mul_le_mul_of_nonneg_left htT hω.le⟩
    · rintro ⟨hs, ht0, htT⟩
      exact ⟨⟨(mul_pos_iff_of_pos_left hω).mp ht0,
        le_of_mul_le_mul_left htT hω⟩, by simpa only [mul_comm x ω] using hs⟩
  have hmeas : MeasurableSet (absSinSublevel (ω * x) ∩ Ioc 0 (ω * T)) :=
    (measurableSet_absSinSublevel _).inter measurableSet_Ioc
  have hmap : volume ((fun t : ℝ => ω * t) ⁻¹'
        (absSinSublevel (ω * x) ∩ Ioc 0 (ω * T))) =
      ENNReal.ofReal |ω⁻¹| * volume (absSinSublevel (ω * x) ∩ Ioc 0 (ω * T)) := by
    rw [← Measure.map_apply (by fun_prop) hmeas, Real.map_volume_mul_left hω.ne']
    simp only [Measure.smul_apply, smul_eq_mul]
  rw [hset, hmap]
  calc
    _ ≤ ENNReal.ofReal |ω⁻¹| * ENNReal.ofReal ((ω * T + π) * (ω * x)) :=
      mul_le_mul_right (volume_absSinSublevel_inter_Ioc_le (ω * x) (ω * T)
        (mul_nonneg hω.le hx) (mul_nonneg hω.le hT)) _
    _ = ENNReal.ofReal ((ω * T + π) * x) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr hω)]
      congr 1
      field_simp

/-- The zero-frequency response is linear, not singular. -/
noncomputable def sincWindowScale (ω T : ℝ) : ℝ :=
  if ω = 0 then 1 else |ω| * max T 0 + π

/-- Unconditional finite-window small-ball law. Empty windows, negative
thresholds, zero frequency, and negative frequency are included. -/
theorem volume_sincResponse_inter_Ioc_le (ω T x : ℝ) :
    volume {t ∈ Ioc (0 : ℝ) T | |t * Real.sinc (ω * t)| ≤ x} ≤
      ENNReal.ofReal (sincWindowScale ω T * max x 0) := by
  by_cases hT : 0 ≤ T
  · by_cases hx : 0 ≤ x
    · rw [max_eq_left hx]
      by_cases hω : ω = 0
      · subst ω
        simp only [sincWindowScale, ite_true, one_mul, zero_mul, Real.sinc_zero,
          mul_one]
        calc
          _ ≤ volume (Icc (0 : ℝ) x) := by
            apply measure_mono
            rintro t ⟨⟨ht, _⟩, hx⟩
            exact ⟨ht.le, (le_abs_self t).trans hx⟩
          _ = ENNReal.ofReal x := by rw [Real.volume_Icc, sub_zero]
      · have heven (t : ℝ) : Real.sinc (ω * t) = Real.sinc (|ω| * t) := by
          by_cases hnonneg : 0 ≤ ω
          · rw [abs_of_nonneg hnonneg]
          · rw [abs_of_neg (lt_of_not_ge hnonneg), neg_mul, Real.sinc_neg]
        simp_rw [heven]
        simpa only [sincWindowScale, if_neg hω, max_eq_left hT] using
          volume_sincResponse_inter_Ioc_le_of_pos |ω| T x (abs_pos.mpr hω) hT hx
    · have hempty : {t ∈ Ioc (0 : ℝ) T | |t * Real.sinc (ω * t)| ≤ x} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro t ⟨_, h⟩
        exact hx ((abs_nonneg _).trans h)
      rw [hempty, measure_empty]
      exact zero_le
  · have hwindow : Ioc (0 : ℝ) T = ∅ := Ioc_eq_empty_of_le (le_of_not_ge hT)
    simp only [hwindow, mem_empty_iff_false, false_and, setOf_false, measure_empty]
    exact zero_le

end GaloisForLFunctions.HTGeometry


