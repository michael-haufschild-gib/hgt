import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The Hurwitz zeta function at a small shift

For `Re w > 0` and a small real shift `b`, the difference between the shifted and unshifted
`ζ`-series converges absolutely and is `O(|b|)`.  This isolates the exact singular part of the
Hurwitz zeta function as the shift tends to zero:

`ζ(w, a) = a^{-w} + ζ(w) + O(|a|)`,   `ζ(w, 1 - a) = ζ(w) + O(|a|)`,

which is the input to Jonquière's boundary expansion of the polylogarithm.
-/

open Complex HurwitzZeta Filter Topology Set

namespace RHTower

/-- The termwise difference between the shifted and unshifted `ζ`-series. -/
noncomputable def shiftDiffTerm (b : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 + b : ℝ) : ℂ) ^ (-w) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-w)

/-- The shift-difference series. -/
noncomputable def shiftDiffSeries (b : ℝ) (w : ℂ) : ℂ := ∑' n : ℕ, shiftDiffTerm b w n

/-- **A mean-value bound for the shifted power.** -/
theorem norm_cpow_shift_sub_le {x b : ℝ} (hx : 1 ≤ x) (hb : |b| ≤ 1 / 2) {w : ℂ}
    (hw : 0 < w.re) :
    ‖((x + b : ℝ) : ℂ) ^ (-w) - ((x : ℝ) : ℂ) ^ (-w)‖
      ≤ ‖w‖ * 2 ^ (w.re + 1) * x ^ (-w.re - 1) * |b| := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hwne : (-w) ≠ 0 := by
    intro hcon
    have : w = 0 := by linear_combination -hcon
    rw [this] at hw
    simp at hw
  have hb' : -(1 / 2 : ℝ) ≤ b := (abs_le.1 hb).1
  have hmem : ∀ t ∈ Set.uIcc x (x + b), x / 2 ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hderiv : ∀ t ∈ Set.uIcc x (x + b),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-w))
        ((-w) * (t : ℂ) ^ (-w - 1)) (Set.uIcc x (x + b)) t := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) (hmem t ht)
    exact (hasDerivAt_ofReal_cpow_const htpos.ne' hwne).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc x (x + b),
      ‖(-w) * (t : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * 2 ^ (w.re + 1) * x ^ (-w.re - 1) := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) (hmem t ht)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [hre]
    have hstep : t ^ (-w.re - 1) ≤ (x / 2) ^ (-w.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hmem t ht) (by linarith)
    have hval : (x / 2 : ℝ) ^ (-w.re - 1) = 2 ^ (w.re + 1) * x ^ (-w.re - 1) := by
      rw [Real.div_rpow hx0.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [show -(-w.re - 1) = w.re + 1 by ring, mul_comm]
    calc ‖w‖ * t ^ (-w.re - 1) ≤ ‖w‖ * ((x / 2) ^ (-w.re - 1)) :=
          mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      _ = ‖w‖ * (2 ^ (w.re + 1) * x ^ (-w.re - 1)) := by rw [hval]
      _ = ‖w‖ * 2 ^ (w.re + 1) * x ^ (-w.re - 1) := by ring
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => (y : ℂ) ^ (-w))
    (f' := fun y : ℝ => (-w) * (y : ℂ) ^ (-w - 1))
    hderiv hbound (convex_uIcc _ _) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simpa [Real.norm_eq_abs] using hmain

/-- The termwise bound for the shift-difference series. -/
theorem norm_shiftDiffTerm_le {b : ℝ} (hb : |b| ≤ 1 / 2) {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ‖shiftDiffTerm b w n‖
      ≤ (‖w‖ * 2 ^ (w.re + 1) * |b|) * (((n : ℝ) + 1) ^ (-w.re - 1)) := by
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp [Nat.cast_nonneg]
  have h := norm_cpow_shift_sub_le (x := (n : ℝ) + 1) (b := b) hx hb hw
  rw [shiftDiffTerm]
  calc ‖(((n : ℝ) + 1 + b : ℝ) : ℂ) ^ (-w) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-w)‖
      ≤ ‖w‖ * 2 ^ (w.re + 1) * ((n : ℝ) + 1) ^ (-w.re - 1) * |b| := h
    _ = (‖w‖ * 2 ^ (w.re + 1) * |b|) * (((n : ℝ) + 1) ^ (-w.re - 1)) := by ring

/-- The majorant of the shift-difference series is summable exactly in the right half plane. -/
theorem summable_shiftMajorant {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-w.re - 1)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-w.re - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-w.re - 1)) 1).mpr hbase
  refine this.congr fun _ => ?_
  norm_cast

theorem summable_norm_shiftDiffTerm {b : ℝ} (hb : |b| ≤ 1 / 2) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ‖shiftDiffTerm b w n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_shiftDiffTerm_le hb hw)
    ((summable_shiftMajorant hw).mul_left _)

theorem summable_shiftDiffTerm {b : ℝ} (hb : |b| ≤ 1 / 2) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => shiftDiffTerm b w n) :=
  Summable.of_norm (summable_norm_shiftDiffTerm hb hw)

/-- **The shift-difference series is `O(|b|)`.** -/
theorem norm_shiftDiffSeries_le {b : ℝ} (hb : |b| ≤ 1 / 2) {w : ℂ} (hw : 0 < w.re) :
    ‖shiftDiffSeries b w‖
      ≤ (‖w‖ * 2 ^ (w.re + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - 1))) * |b| := by
  rw [shiftDiffSeries]
  refine (norm_tsum_le_tsum_norm (summable_norm_shiftDiffTerm hb hw)).trans ?_
  refine (Summable.tsum_le_tsum (norm_shiftDiffTerm_le hb hw)
    (summable_norm_shiftDiffTerm hb hw) ((summable_shiftMajorant hw).mul_left _)).trans ?_
  rw [tsum_mul_left]
  ring_nf
  exact le_rfl

/-- The shifted `ζ`-series as a `HasSum` statement in the convergent regime. -/
theorem hasSum_riemannZeta_shift {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) (riemannZeta w) := by
  have hsum := hasSum_hurwitzZeta_of_one_lt_re (a := (1 : ℝ)) (by norm_num) hw
  have hcoe : (((1 : ℝ)) : UnitAddCircle) = (0 : UnitAddCircle) := by
    simp
  have hz : hurwitzZeta ((1 : ℝ) : UnitAddCircle) w = riemannZeta w := by
    rw [hcoe, HurwitzZeta.hurwitzZeta_zero]
  rw [hz] at hsum
  refine hsum.congr_fun fun n => ?_
  norm_num

/-- **In the convergent regime the Hurwitz zeta function splits.** -/
theorem hurwitzZeta_eq_add_shiftDiffSeries_of_one_lt_re {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1)
    {w : ℂ} (hw : 1 < w.re) :
    hurwitzZeta ((a : ℝ) : UnitAddCircle) w
      = ((a : ℝ) : ℂ) ^ (-w) + riemannZeta w + shiftDiffSeries a w := by
  have hmem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨h0.le, h1⟩
  set f : ℕ → ℂ := fun m => 1 / ((m : ℂ) + (a : ℂ)) ^ w with hf
  have hsum : HasSum f (hurwitzZeta ((a : ℝ) : UnitAddCircle) w) :=
    hasSum_hurwitzZeta_of_one_lt_re hmem hw
  have hf0 : f 0 = ((a : ℝ) : ℂ) ^ (-w) := by
    rw [hf]
    simp only [Nat.cast_zero, zero_add]
    rw [Complex.cpow_neg, one_div]
  have hpeel : HasSum (fun n : ℕ => f (n + 1))
      (hurwitzZeta ((a : ℝ) : UnitAddCircle) w - f 0) := by
    refine (hasSum_nat_add_iff (f := f) 1).mpr ?_
    simp only [Finset.sum_range_one, sub_add_cancel]
    exact hsum
  have hdiff := hpeel.sub (hasSum_riemannZeta_shift hw)
  have hcongr : ∀ n : ℕ, shiftDiffTerm a w n = f (n + 1) - 1 / ((n : ℂ) + 1) ^ w := by
    intro n
    simp only [hf, shiftDiffTerm, one_div, Complex.cpow_neg]
    push_cast
    ring_nf
  have hfinal := hdiff.congr_fun hcongr
  rw [shiftDiffSeries, hfinal.tsum_eq, hf0]
  ring

/-- **The negative-shift split in the convergent regime.** -/
theorem hurwitzZeta_neg_eq_add_shiftDiffSeries_of_one_lt_re {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1)
    {w : ℂ} (hw : 1 < w.re) :
    hurwitzZeta ((-a : ℝ) : UnitAddCircle) w = riemannZeta w + shiftDiffSeries (-a) w := by
  have hmem : (1 - a) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcoe : (((-a : ℝ)) : UnitAddCircle) = (((1 - a : ℝ)) : UnitAddCircle) := by
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by simp
    rw [show (1 - a : ℝ) = 1 + (-a) by ring]
    rw [show (((1 + (-a) : ℝ)) : UnitAddCircle)
      = ((1 : ℝ) : UnitAddCircle) + ((-a : ℝ) : UnitAddCircle) from rfl, hone, zero_add]
  have hsum : HasSum (fun n : ℕ => 1 / ((n : ℂ) + ((1 - a : ℝ) : ℂ)) ^ w)
      (hurwitzZeta ((-a : ℝ) : UnitAddCircle) w) := by
    rw [hcoe]
    exact hasSum_hurwitzZeta_of_one_lt_re hmem hw
  have hdiff := hsum.sub (hasSum_riemannZeta_shift hw)
  have hcongr : ∀ n : ℕ, shiftDiffTerm (-a) w n
      = 1 / ((n : ℂ) + ((1 - a : ℝ) : ℂ)) ^ w - 1 / ((n : ℂ) + 1) ^ w := by
    intro n
    simp only [shiftDiffTerm, one_div, Complex.cpow_neg]
    push_cast
    ring_nf
  have hfinal := hdiff.congr_fun hcongr
  rw [shiftDiffSeries, hfinal.tsum_eq]
  ring

/-- Each term of the shift-difference series is entire. -/
theorem differentiable_shiftDiffTerm (b : ℝ) (hb : |b| ≤ 1 / 2) (n : ℕ) :
    Differentiable ℂ (fun w : ℂ => shiftDiffTerm b w n) := by
  have hb' : -(1 / 2 : ℝ) ≤ b := (abs_le.1 hb).1
  have h1 : ((n : ℝ) + 1 + b : ℝ) ≠ 0 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    intro hcon
    have : ((n : ℝ) + 1 + b) ≥ 1 / 2 := by linarith
    linarith [hcon ▸ this]
  have h2 : ((n : ℝ) + 1 : ℝ) ≠ 0 := by positivity
  intro w
  refine DifferentiableAt.sub ?_ ?_
  · exact DifferentiableAt.const_cpow (differentiableAt_id.neg)
      (Or.inl (by exact_mod_cast Complex.ofReal_ne_zero.mpr h1))
  · exact DifferentiableAt.const_cpow (differentiableAt_id.neg)
      (Or.inl (by exact_mod_cast Complex.ofReal_ne_zero.mpr h2))

/-- **The shift-difference series is analytic on the right half plane.** -/
theorem differentiableAt_shiftDiffSeries {b : ℝ} (hb : |b| ≤ 1 / 2) {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    DifferentiableAt ℂ (fun w : ℂ => shiftDiffSeries b w) w₀ := by
  set r : ℝ := w₀.re / 2 with hrdef
  have hr : 0 < r := by positivity
  set U : Set ℂ := Metric.ball w₀ r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hmemU : w₀ ∈ U := Metric.mem_ball_self hr
  have hfacts : ∀ w ∈ U, r ≤ w.re ∧ ‖w‖ ≤ ‖w₀‖ + r ∧ w.re ≤ w₀.re + r := by
    intro w hw
    have hdist : ‖w - w₀‖ < r := by
      rw [hUdef] at hw
      simpa [Complex.dist_eq] using hw
    have hre : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
      simpa using Complex.abs_re_le_norm (w - w₀)
    have h1 : |w.re - w₀.re| < r := lt_of_le_of_lt hre hdist
    have h2 := (abs_lt.1 h1).1
    have h3 := (abs_lt.1 h1).2
    refine ⟨by rw [hrdef] at *; linarith, ?_, by linarith⟩
    have : ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by
      simpa using norm_add_le (w - w₀) w₀
    linarith
  set u : ℕ → ℝ :=
    fun n => ((‖w₀‖ + r) * 2 ^ (w₀.re + r + 1) * |b|) * (((n : ℝ) + 1) ^ (-r - 1)) with hudef
  have hu : Summable u := (summable_shiftMajorant (w := (r : ℂ)) (by simpa using hr)).mul_left _
  have hle : ∀ n : ℕ, ∀ w ∈ U, ‖(fun w : ℂ => shiftDiffTerm b w n) w‖ ≤ u n := by
    intro n w hw
    obtain ⟨hre1, hnorm, hre2⟩ := hfacts w hw
    have hwre : 0 < w.re := lt_of_lt_of_le hr hre1
    have hstep := norm_shiftDiffTerm_le hb hwre n
    refine hstep.trans ?_
    have hb0 : (0 : ℝ) ≤ |b| := abs_nonneg b
    have hpow : ((n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-r - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le (by simp [Nat.cast_nonneg]) (by linarith)
    have htwo : (2 : ℝ) ^ (w.re + 1) ≤ 2 ^ (w₀.re + r + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpos1 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-r - 1) := Real.rpow_nonneg (by positivity) _
    have hpos2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-w.re - 1) := Real.rpow_nonneg (by positivity) _
    have hpos3 : (0 : ℝ) ≤ (2 : ℝ) ^ (w.re + 1) := Real.rpow_nonneg (by norm_num) _
    rw [hudef]
    have hA : ‖w‖ * 2 ^ (w.re + 1) * |b| ≤ (‖w₀‖ + r) * 2 ^ (w₀.re + r + 1) * |b| := by
      have h4 : ‖w‖ * 2 ^ (w.re + 1) ≤ (‖w₀‖ + r) * 2 ^ (w₀.re + r + 1) :=
        mul_le_mul hnorm htwo hpos3 (by positivity)
      exact mul_le_mul_of_nonneg_right h4 hb0
    calc ‖w‖ * 2 ^ (w.re + 1) * |b| * ((n : ℝ) + 1) ^ (-w.re - 1)
        ≤ ‖w‖ * 2 ^ (w.re + 1) * |b| * ((n : ℝ) + 1) ^ (-r - 1) := by
          refine mul_le_mul_of_nonneg_left hpow ?_
          positivity
      _ ≤ (‖w₀‖ + r) * 2 ^ (w₀.re + r + 1) * |b| * ((n : ℝ) + 1) ^ (-r - 1) :=
          mul_le_mul_of_nonneg_right hA hpos1
  have hdiffOn := differentiableOn_tsum_of_summable_norm hu
    (fun n => (differentiable_shiftDiffTerm b hb n).differentiableOn) hU hle
  exact hdiffOn.differentiableAt (hU.mem_nhds hmemU)

/-- The right half plane. -/
theorem isOpen_reGT_zero : IsOpen {w : ℂ | 0 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_reGT_zero : IsPreconnected {w : ℂ | 0 < w.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- The difference of the Hurwitz and Riemann zeta functions is entire. -/
theorem differentiable_hurwitzZeta_sub_riemannZeta (a : UnitAddCircle) :
    Differentiable ℂ (fun w : ℂ => hurwitzZeta a w - riemannZeta w) := by
  have h := differentiable_hurwitzZeta_sub_hurwitzZeta a 0
  simpa [HurwitzZeta.hurwitzZeta_zero] using h

/-- **The small-shift expansion of the Hurwitz zeta function, positive shift.** -/
theorem hurwitzZeta_sub_riemannZeta_eq {a : ℝ} (h0 : 0 < a) (ha : a ≤ 1 / 2) {w : ℂ}
    (hw : 0 < w.re) :
    hurwitzZeta ((a : ℝ) : UnitAddCircle) w - riemannZeta w
      = ((a : ℝ) : ℂ) ^ (-w) + shiftDiffSeries a w := by
  have hb : |a| ≤ 1 / 2 := by rwa [abs_of_pos h0]
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  set F : ℂ → ℂ := fun w =>
    (hurwitzZeta ((a : ℝ) : UnitAddCircle) w - riemannZeta w)
      - (((a : ℝ) : ℂ) ^ (-w) + shiftDiffSeries a w) with hFdef
  have hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub (differentiable_hurwitzZeta_sub_riemannZeta _ z) ?_
    refine DifferentiableAt.add ?_ (differentiableAt_shiftDiffSeries hb hz)
    exact DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hane)
  have hFan : AnalyticOnNhd ℂ F {w : ℂ | 0 < w.re} :=
    hF.analyticOnNhd isOpen_reGT_zero
  have hmem2 : (2 : ℂ) ∈ {w : ℂ | 0 < w.re} := by norm_num
  have hnhds : {w : ℂ | 1 < w.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : F =ᶠ[nhds (2 : ℂ)] 0 := by
    filter_upwards [hnhds] with z hz
    have h1 := hurwitzZeta_eq_add_shiftDiffSeries_of_one_lt_re h0 (by linarith) hz
    rw [hFdef]
    simp only [Pi.zero_apply]
    rw [h1]
    ring
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_reGT_zero hmem2 hev
  have := hzero hw
  rw [hFdef] at this
  simp only [Pi.zero_apply] at this
  linear_combination this

/-- **The small-shift expansion of the Hurwitz zeta function, negative shift.** -/
theorem hurwitzZeta_neg_sub_riemannZeta_eq {a : ℝ} (h0 : 0 < a) (ha : a ≤ 1 / 2) {w : ℂ}
    (hw : 0 < w.re) :
    hurwitzZeta ((-a : ℝ) : UnitAddCircle) w - riemannZeta w = shiftDiffSeries (-a) w := by
  have hb : |(-a)| ≤ 1 / 2 := by rw [abs_neg, abs_of_pos h0]; exact ha
  set F : ℂ → ℂ := fun w =>
    (hurwitzZeta ((-a : ℝ) : UnitAddCircle) w - riemannZeta w) - shiftDiffSeries (-a) w with hFdef
  have hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re} := by
    intro z hz
    exact ((differentiable_hurwitzZeta_sub_riemannZeta _ z).sub
      (differentiableAt_shiftDiffSeries hb hz)).differentiableWithinAt
  have hFan : AnalyticOnNhd ℂ F {w : ℂ | 0 < w.re} :=
    hF.analyticOnNhd isOpen_reGT_zero
  have hmem2 : (2 : ℂ) ∈ {w : ℂ | 0 < w.re} := by norm_num
  have hnhds : {w : ℂ | 1 < w.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : F =ᶠ[nhds (2 : ℂ)] 0 := by
    filter_upwards [hnhds] with z hz
    have h1 := hurwitzZeta_neg_eq_add_shiftDiffSeries_of_one_lt_re h0 (by linarith) hz
    rw [hFdef]
    simp only [Pi.zero_apply]
    rw [h1]
    ring
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_reGT_zero hmem2 hev
  have := hzero hw
  rw [hFdef] at this
  simp only [Pi.zero_apply] at this
  linear_combination this

/-- The shift-difference terms are continuous in the shift on the admissible window. -/
theorem continuousOn_shiftDiffTerm (w : ℂ) (n : ℕ) :
    ContinuousOn (fun b : ℝ => shiftDiffTerm b w n) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  refine ContinuousOn.sub ?_ continuousOn_const
  intro b hb
  have hpos : (0 : ℝ) < (n : ℝ) + 1 + b := by
    have h1 : -(1 / 2 : ℝ) ≤ b := hb.1
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hslit : ((((n : ℝ) + 1 + b : ℝ)) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa using hpos)
  have h1 : ContinuousAt (fun c : ℝ => ((((n : ℝ) + 1 + c : ℝ)) : ℂ)) b := by fun_prop
  have hcomp : ContinuousAt (fun c : ℝ => ((((n : ℝ) + 1 + c : ℝ)) : ℂ) ^ (-w)) b :=
    ContinuousAt.comp (g := fun z : ℂ => z ^ (-w))
      (f := fun c : ℝ => ((((n : ℝ) + 1 + c : ℝ)) : ℂ)) (x := b)
      (continuousAt_cpow_const hslit) h1
  exact hcomp.continuousWithinAt

/-- **The shift-difference series is continuous in the shift.** -/
theorem continuousOn_shiftDiffSeries {w : ℂ} (hw : 0 < w.re) :
    ContinuousOn (fun b : ℝ => shiftDiffSeries b w) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  set u : ℕ → ℝ := fun n => (‖w‖ * 2 ^ (w.re + 1) * (1 / 2)) * (((n : ℝ) + 1) ^ (-w.re - 1))
    with hu
  have husum : Summable u := (summable_shiftMajorant hw).mul_left _
  have hbound : ∀ (n : ℕ), ∀ b ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖shiftDiffTerm b w n‖ ≤ u n := by
    intro n b hb
    have habs : |b| ≤ 1 / 2 := abs_le.mpr ⟨hb.1, hb.2⟩
    refine (norm_shiftDiffTerm_le habs hw n).trans ?_
    rw [hu]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
    refine mul_le_mul_of_nonneg_left habs ?_
    positivity
  have huniform := tendstoUniformlyOn_tsum husum hbound
  refine huniform.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall ?_))
  intro N
  exact continuousOn_finsetSum _ fun n _ => continuousOn_shiftDiffTerm w n

/-- **A mean-value bound for a nonnegative shift, with no size restriction.** -/
theorem norm_cpow_shift_sub_le_of_nonneg {x b : ℝ} (hx : 0 < x) (hb : 0 ≤ b) {w : ℂ}
    (hw : 0 < w.re) :
    ‖((x + b : ℝ) : ℂ) ^ (-w) - ((x : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * x ^ (-w.re - 1) * b := by
  have hwne : (-w) ≠ 0 := by
    intro hcon
    have : w = 0 := by linear_combination -hcon
    rw [this] at hw
    simp at hw
  have hmem : ∀ t ∈ Set.uIcc x (x + b), x ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith
  have hderiv : ∀ t ∈ Set.uIcc x (x + b),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-w))
        ((-w) * (t : ℂ) ^ (-w - 1)) (Set.uIcc x (x + b)) t := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hx (hmem t ht)
    exact (hasDerivAt_ofReal_cpow_const htpos.ne' hwne).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc x (x + b),
      ‖(-w) * (t : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * x ^ (-w.re - 1) := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hx (hmem t ht)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [hre]
    have hstep : t ^ (-w.re - 1) ≤ x ^ (-w.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hx (hmem t ht) (by linarith)
    exact mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => (y : ℂ) ^ (-w))
    (f' := fun y : ℝ => (-w) * (y : ℂ) ^ (-w - 1))
    hderiv hbound (convex_uIcc _ _) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hnorm : ‖((x + b : ℝ)) - x‖ = b := by
    rw [Real.norm_eq_abs, show (x + b) - x = b by ring, abs_of_nonneg hb]
  rw [hnorm] at hmain
  exact hmain

/-! ## The second-order small-shift expansion -/

/-- **A second-order mean-value bound for the shifted power.** -/
theorem norm_cpow_shift_sub_linear_le {x b : ℝ} (hx : 1 ≤ x) (hb : |b| ≤ 1 / 2) {w : ℂ}
    (hw : 0 < w.re) :
    ‖((x + b : ℝ) : ℂ) ^ (-w) - ((x : ℝ) : ℂ) ^ (-w)
        + (w * (b : ℂ)) * ((x : ℝ) : ℂ) ^ (-w - 1)‖
      ≤ (‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2))) * x ^ (-w.re - 2) * |b| ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hw1 : 0 < (w + 1).re := by simp; linarith
  have hwne : (-w) ≠ 0 := by
    intro hcon
    have : w = 0 := by linear_combination -hcon
    rw [this] at hw
    simp at hw
  have hb' : -(1 / 2 : ℝ) ≤ b := (abs_le.1 hb).1
  have hmem : ∀ y ∈ Set.uIcc x (x + b), x / 2 ≤ y := by
    intro y hy
    rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hdiff : ∀ y ∈ Set.uIcc x (x + b), |y - x| ≤ |b| := by
    intro y hy
    rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (by linarith)]
      have := (abs_le.1 hb).2
      have hb0 : 0 ≤ b := by linarith
      rw [abs_of_nonneg hb0]
      linarith
    · rw [abs_of_nonpos (by linarith)]
      have hb0 : b ≤ 0 := by linarith
      rw [abs_of_nonpos hb0]
      linarith
  have hderiv : ∀ y ∈ Set.uIcc x (x + b),
      HasDerivWithinAt (fun z : ℝ => (z : ℂ) ^ (-w) + (w * ((z : ℂ) - (x : ℂ)))
          * ((x : ℝ) : ℂ) ^ (-w - 1))
        ((-w) * (y : ℂ) ^ (-w - 1) + w * ((x : ℝ) : ℂ) ^ (-w - 1))
        (Set.uIcc x (x + b)) y := by
    intro y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) (hmem y hy)
    have h1 := (hasDerivAt_ofReal_cpow_const hypos.ne' hwne).hasDerivWithinAt
      (s := Set.uIcc x (x + b))
    have h2 : HasDerivWithinAt (fun z : ℝ => (w * ((z : ℂ) - (x : ℂ)))
        * ((x : ℝ) : ℂ) ^ (-w - 1)) (w * ((x : ℝ) : ℂ) ^ (-w - 1))
        (Set.uIcc x (x + b)) y := by
      have hbase : HasDerivWithinAt (fun z : ℝ => ((z : ℂ) - (x : ℂ))) 1
          (Set.uIcc x (x + b)) y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).hasDerivWithinAt.sub_const (x : ℂ)
      have := ((hbase.const_mul w).mul_const (((x : ℝ) : ℂ) ^ (-w - 1)))
      simpa using this
    exact h1.add h2
  have hbound : ∀ y ∈ Set.uIcc x (x + b),
      ‖(-w) * (y : ℂ) ^ (-w - 1) + w * ((x : ℝ) : ℂ) ^ (-w - 1)‖
        ≤ (‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2))) * x ^ (-w.re - 2) * |b| := by
    intro y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) (hmem y hy)
    have hrew : ((y : ℝ) : ℂ) = ((x + (y - x) : ℝ) : ℂ) := by push_cast; ring
    have hexp : (-w - 1) = -(w + 1) := by ring
    have hstep := norm_cpow_shift_sub_le (x := x) (b := y - x) hx
      (le_trans (hdiff y hy) hb) hw1
    have hval : ‖(-w) * (y : ℂ) ^ (-w - 1) + w * ((x : ℝ) : ℂ) ^ (-w - 1)‖
        = ‖w‖ * ‖((x + (y - x) : ℝ) : ℂ) ^ (-(w + 1)) - ((x : ℝ) : ℂ) ^ (-(w + 1))‖ := by
      rw [hexp, hrew, ← norm_neg (a := w), ← norm_mul]
      congr 1
      ring
    rw [hval]
    have hre : (w + 1).re = w.re + 1 := by simp
    rw [hre] at hstep
    have hchain : ‖((x + (y - x) : ℝ) : ℂ) ^ (-(w + 1)) - ((x : ℝ) : ℂ) ^ (-(w + 1))‖
        ≤ ‖w + 1‖ * 2 ^ (w.re + 1 + 1) * x ^ (-(w.re + 1) - 1) * |b| :=
      hstep.trans (by
        refine mul_le_mul_of_nonneg_left (le_trans (hdiff y hy) le_rfl) ?_
        positivity)
    have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
    have hrw1 : (w.re + 1 + 1) = w.re + 2 := by ring
    have hrw2 : (-(w.re + 1) - 1) = -w.re - 2 := by ring
    rw [hrw1, hrw2] at hchain
    calc ‖w‖ * ‖((x + (y - x) : ℝ) : ℂ) ^ (-(w + 1)) - ((x : ℝ) : ℂ) ^ (-(w + 1))‖
        ≤ ‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2) * x ^ (-w.re - 2) * |b|) :=
          mul_le_mul_of_nonneg_left hchain hnn
      _ = (‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2))) * x ^ (-w.re - 2) * |b| := by ring
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z : ℝ => (z : ℂ) ^ (-w) + (w * ((z : ℂ) - (x : ℂ))) * ((x : ℝ) : ℂ) ^ (-w - 1))
    (f' := fun z : ℝ => (-w) * (z : ℂ) ^ (-w - 1) + w * ((x : ℝ) : ℂ) ^ (-w - 1))
    hderiv hbound (convex_uIcc _ _) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hsimp : ((((x + b : ℝ)) : ℂ) ^ (-w)
        + (w * ((((x + b : ℝ)) : ℂ) - (x : ℂ))) * ((x : ℝ) : ℂ) ^ (-w - 1))
      - (((x : ℝ) : ℂ) ^ (-w) + (w * (((x : ℝ) : ℂ) - (x : ℂ))) * ((x : ℝ) : ℂ) ^ (-w - 1))
      = ((x + b : ℝ) : ℂ) ^ (-w) - ((x : ℝ) : ℂ) ^ (-w)
        + (w * (b : ℂ)) * ((x : ℝ) : ℂ) ^ (-w - 1) := by
    push_cast
    ring
  rw [hsimp] at hmain
  refine hmain.trans (le_of_eq ?_)
  have hnormb : ‖((x + b : ℝ)) - x‖ = |b| := by
    rw [Real.norm_eq_abs]
    congr 1
    ring
  rw [hnormb]
  ring

/-- The shifted `ζ`-series at the incremented exponent. -/
theorem hasSum_riemannZeta_shift_succ {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun n : ℕ => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - 1)) (riemannZeta (w + 1)) := by
  have hw1 : 1 < (w + 1).re := by simp; linarith
  refine (hasSum_riemannZeta_shift hw1).congr_fun fun n => ?_
  rw [show (-w - 1) = -(w + 1) by ring, Complex.cpow_neg, one_div]
  congr 2
  push_cast
  ring

theorem summable_shiftMajorant_succ {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-w.re - 2)) := by
  have hw1 : 0 < (w + 1).re := by simp; linarith
  have h := summable_shiftMajorant hw1
  refine h.congr fun n => ?_
  congr 1
  simp
  ring

/-- **The second-order small-shift expansion.** -/
theorem norm_shiftDiffSeries_add_linear_le {b : ℝ} (hb : |b| ≤ 1 / 2) {w : ℂ} (hw : 0 < w.re) :
    ‖shiftDiffSeries b w + (w * (b : ℂ)) * riemannZeta (w + 1)‖
      ≤ ((‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2))) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - 2)))
        * |b| ^ 2 := by
  set C : ℝ := ‖w‖ * (‖w + 1‖ * 2 ^ (w.re + 2)) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (w.re + 2) := Real.rpow_nonneg (by norm_num) _
    positivity
  have hterm : ∀ n : ℕ,
      ‖shiftDiffTerm b w n + (w * (b : ℂ)) * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - 1)‖
        ≤ (C * |b| ^ 2) * (((n : ℝ) + 1) ^ (-w.re - 2)) := by
    intro n
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp [Nat.cast_nonneg]
    have h := norm_cpow_shift_sub_linear_le (x := (n : ℝ) + 1) (b := b) hx hb hw
    rw [shiftDiffTerm]
    refine h.trans (le_of_eq ?_)
    rw [hC]
    ring
  have hsummaj : Summable (fun n : ℕ => (C * |b| ^ 2) * (((n : ℝ) + 1) ^ (-w.re - 2))) :=
    (summable_shiftMajorant_succ hw).mul_left _
  have hsum1 : Summable (fun n : ℕ => shiftDiffTerm b w n) := summable_shiftDiffTerm hb hw
  have hsum2 : Summable (fun n : ℕ => (w * (b : ℂ)) * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - 1)) :=
    ((hasSum_riemannZeta_shift_succ hw).summable).mul_left _
  have hsum : Summable (fun n : ℕ =>
      shiftDiffTerm b w n + (w * (b : ℂ)) * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - 1)) :=
    hsum1.add hsum2
  have hval : shiftDiffSeries b w + (w * (b : ℂ)) * riemannZeta (w + 1)
      = ∑' n : ℕ, (shiftDiffTerm b w n
          + (w * (b : ℂ)) * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - 1)) := by
    rw [hsum1.tsum_add hsum2, shiftDiffSeries, ← (hasSum_riemannZeta_shift_succ hw).tsum_eq,
      tsum_mul_left]
  rw [hval]
  have hnormsum : Summable (fun n : ℕ =>
      ‖shiftDiffTerm b w n + (w * (b : ℂ)) * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-w - 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsummaj
  refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
  refine (Summable.tsum_le_tsum hterm hnormsum hsummaj).trans ?_
  rw [tsum_mul_left]
  ring_nf
  exact le_rfl

end RHTower
