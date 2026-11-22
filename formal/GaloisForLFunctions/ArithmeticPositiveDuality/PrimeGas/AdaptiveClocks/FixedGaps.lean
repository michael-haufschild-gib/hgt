import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Necessity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Fixed additive gaps at the critical resolution

For a positive label separation d, the chord scaled by the square root
of the product of the labels tends to d|t|. Its strict pointwise bound
settles the equality case for every starting label.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks

open Filter Topology
open scoped NNReal

def criticalClock (t : ℝ) (r : {r : ℝ // 0 < r}) : Clock := ⟨t,r,1/2⟩

private def start (n : ℕ) : ℕ+ := ⟨n+1,Nat.succ_pos n⟩

def lane (d : ℕ+) (n : ℕ) : Pair := (Clock.offset (start n) d.val,start n)

/-- Half the difference of the two logarithmic energies. -/
def halfGap (p : Pair) := (energy p.1-energy p.2)/2

private def mid (p : Pair) := (energy p.1+energy p.2)/2

def scaledChord (t : ℝ) (p : Pair) := Real.exp (mid p)*dist (clockPhase t p.1) (clockPhase t p.2)

theorem scaledChord_sqrt (t : ℝ) (p : Pair) :
    scaledChord t p = Real.sqrt (((p.1:ℕ):ℝ)*(p.2:ℕ)) * dist (clockPhase t p.1) (clockPhase t p.2) := by
  have he : Real.exp (mid p)^2 = ((p.1:ℕ):ℝ)*(p.2:ℕ) := by
    rw [sq,← Real.exp_add,show mid p+mid p = energy p.1+energy p.2 by unfold mid; ring,
      Real.exp_add,exp_energy,exp_energy]
  rw [← he,Real.sqrt_sq (Real.exp_pos _).le]
  rfl

theorem critical_passes (t : ℝ) (r : {r : ℝ // 0 < r}) (p : Pair) :
    (criticalClock t r).Passes p ↔ scaledChord t p < r.val := by
  have hw : weight ((criticalClock t r).exponent : ℝ) p = (Real.exp (mid p))⁻¹ := by
    rw [← Real.exp_neg]
    unfold weight
    congr 1
    change -(↑(1/2 : ℝ≥0) : ℝ)*(energy p.1+energy p.2) = -((energy p.1+energy p.2)/2)
    push_cast
    ring
  change dist (clockPhase t p.1) (clockPhase t p.2) < r.val*weight ((criticalClock t r).exponent : ℝ) p ↔ _
  rw [hw,← div_eq_mul_inv,lt_div_iff₀ (Real.exp_pos _)]
  change _ * _ < _ ↔ Real.exp (mid p)*_ < _
  rw [mul_comm]

private theorem gap_pos (d : ℕ+) (n : ℕ) : 0 < halfGap (lane d n) := by
  have h : ((start n).val:ℝ) < (((start n).val+d.val:ℕ):ℝ) :=
    Nat.cast_lt.mpr (by have := d.pos; omega)
  exact div_pos (sub_pos.mpr (Real.log_lt_log (Nat.cast_pos.mpr (start n).pos) h)) (by norm_num)

private theorem sinh_gap (d : ℕ+) (n : ℕ) :
    Real.exp (mid (lane d n))*(2*Real.sinh (halfGap (lane d n))) = (d.val:ℝ) := by
  let p := lane d n
  have h₁ : mid p + halfGap p = energy p.1 := by unfold mid halfGap; ring
  have h₂ : mid p + -(halfGap p) = energy p.2 := by unfold mid halfGap; ring
  calc
    _ = Real.exp (mid p+halfGap p)-Real.exp (mid p+ -(halfGap p)) := by
      rw [Real.sinh_eq,Real.exp_add,Real.exp_add]
      ring
    _ = _ := by
      rw [h₁,h₂,exp_energy,exp_energy]
      change (((start n).val+d.val : ℕ):ℝ)-((start n).val:ℝ) = d.val
      rw [Nat.cast_add,add_sub_cancel_left]

theorem scaled_lane (t : ℝ) (d : ℕ+) (n : ℕ) :
    scaledChord t (lane d n) = d.val * |Real.sin (t*halfGap (lane d n))| / Real.sinh (halfGap (lane d n)) := by
  let p := lane d n
  have hs := (Real.sinh_pos_iff.mpr (gap_pos d n)).ne'
  rw [scaledChord,chord,eq_div_iff hs]
  change Real.exp (mid p)*(2*|Real.sin (t*(energy p.1-energy p.2)/2)|)*Real.sinh (halfGap p) = _
  rw [show t*(energy p.1-energy p.2)/2 = t*halfGap p by unfold halfGap; ring,← sinh_gap d n]
  ring

private theorem gap_tendsto (d : ℕ+) :
    Tendsto (fun n => halfGap (lane d n)) atTop (𝓝[≠] 0) := by
  have hn : Tendsto (fun n => ((start n).val:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun n => (d.val:ℝ)/(start n).val) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have h0 : Tendsto (fun n => halfGap (lane d n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (gap_pos d n).le) _ hd
    intro n
    have h := Clock.log_offset (start n) d.val
    have hp := gap_pos d n
    change 0 < (energy (Clock.offset (start n) d.val)-energy (start n))/2 at hp
    change (energy (Clock.offset (start n) d.val)-energy (start n))/2 ≤ _
    linarith only [h,hp]
  exact tendsto_nhdsWithin_iff.mpr ⟨h0,Eventually.of_forall fun n => (gap_pos d n).ne'⟩

private theorem sin_slope (t : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (t*x)/x) (𝓝[≠] 0) (𝓝 t) := by
  have hd : HasDerivAt (fun x : ℝ => Real.sin (t*x)) t 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul t).sin
  refine (hasDerivAt_iff_tendsto_slope.mp hd).congr fun x => ?_
  simp [slope_def_field]

private theorem sinh_slope : Tendsto (fun x : ℝ => Real.sinh x/x) (𝓝[≠] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.sinh 1 0 := by simpa using Real.hasDerivAt_sinh 0
  refine (hasDerivAt_iff_tendsto_slope.mp hd).congr fun x => ?_
  simp [slope_def_field]

theorem scaled_lane_tendsto (t : ℝ) (d : ℕ+) :
    Tendsto (fun n => scaledChord t (lane d n)) atTop (𝓝 (|t| * d.val)) := by
  have h := (((sin_slope t).div sinh_slope one_ne_zero).comp (gap_tendsto d)).abs.mul_const (d.val:ℝ)
  simp only [div_one] at h
  refine h.congr fun n => ?_
  let u := halfGap (lane d n)
  change |(Real.sin (t*u)/u)/(Real.sinh u/u)| * d.val = _
  have hu : u ≠ 0 := (gap_pos d n).ne'
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (gap_pos d n)
  have hq : (Real.sin (t*u)/u)/(Real.sinh u/u) = Real.sin (t*u)/Real.sinh u := by
    field_simp
  rw [hq,abs_div,abs_of_pos hs,scaled_lane]
  ring

private theorem lane_passes_of_le (t : ℝ) (r : {r : ℝ // 0 < r}) (d : ℕ+)
    (h : |t| *d.val ≤ r.val) (n : ℕ) : (criticalClock t r).Passes (lane d n) := by
  rw [critical_passes,scaled_lane]
  let u := halfGap (lane d n)
  have hu : 0 < u := gap_pos d n
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  by_cases ht : t = 0
  · simpa only [ht,zero_mul,Real.sin_zero,abs_zero,mul_zero,zero_div] using r.property
  · rw [div_lt_iff₀ hs]
    have hh : |Real.sin (t*u)| < |t| * Real.sinh u := by
      have hb := Real.abs_sin_le_abs (x := t*u)
      rw [abs_mul,abs_of_pos hu] at hb
      exact hb.trans_lt (mul_lt_mul_of_pos_left (Real.self_lt_sinh_iff.mpr hu) (abs_pos.mpr ht))
    calc
      _ < (d.val:ℝ)*(|t| *Real.sinh u) := mul_lt_mul_of_pos_left hh (Nat.cast_pos.mpr d.pos)
      _ = (|t| *d.val)*Real.sinh u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h hs.le

/-- At critical precision the same closed time interval governs all-label and eventual acceptance. -/
theorem lane_eventually_iff (t : ℝ) (r : {r : ℝ // 0 < r}) (d : ℕ+) :
    (∀ᶠ n : ℕ in atTop, (criticalClock t r).Passes (lane d n)) ↔ |t| *d.val ≤ r.val := by
  constructor
  · intro h
    exact le_of_tendsto (scaled_lane_tendsto t d) (h.mono fun n hn => ((critical_passes t r _).mp hn).le)
  · exact fun h => Eventually.of_forall (lane_passes_of_le t r d h)

theorem lane_all_iff (t : ℝ) (r : {r : ℝ // 0 < r}) (d : ℕ+) :
    (∀ n : ℕ, (criticalClock t r).Passes (lane d n)) ↔ |t| *d.val ≤ r.val :=
  ⟨fun h => (lane_eventually_iff t r d).mp (Eventually.of_forall h),lane_passes_of_le t r d⟩

theorem lane_eventually_rejected (t : ℝ) (r : {r : ℝ // 0 < r}) (d : ℕ+) :
    (∀ᶠ n : ℕ in atTop, ¬(criticalClock t r).Passes (lane d n)) ↔ r.val < |t| *d.val := by
  constructor
  · intro h
    by_contra! hl
    obtain ⟨n,hn⟩ := h.exists
    exact hn (lane_passes_of_le t r d hl n)
  · intro h
    filter_upwards [(scaled_lane_tendsto t d).eventually (lt_mem_nhds h)] with n hn
    exact fun hp => (not_lt.mpr hn.le) ((critical_passes t r _).mp hp)

#print axioms scaledChord_sqrt
#print axioms scaled_lane_tendsto
#print axioms lane_eventually_iff
#print axioms lane_all_iff
#print axioms lane_eventually_rejected

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks
