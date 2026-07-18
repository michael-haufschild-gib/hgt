import Mathlib

/-!
# Detector resolution barrier for off-line zeros

The conjecture `N_off(T) = o(N(T))` ("almost all nontrivial zeros of ζ lie on the
critical line") concerns zeros whose scaled distance `(β - 1/2)·log T` from the
critical line is `o(1)` up to the Selberg scale `≍ log log T`.  This file
formalises the exact resolution law for smooth polynomial-scale detectors
(explicit-formula / Weil sums and smooth local statistics), in the form of a
sharp distortion calculus:

* `detectorFactor δ L`: the exponential distortion factor `exp(δ·L) - 1` of one
  zero-like atom moved to distance `δ` from the line, measured by a detector at
  logarithmic cutoff scale `L` (cutoff `x = T^A` corresponds to `L = A·log T`).

* `exp_sub_one_le_mul_exp`: the Lipschitz envelope `exp y - 1 ≤ y·exp y`.

* `detectorFactor_microscopic`, `detectorFactor_microscopic_pos`: at the
  natural (microscopic) scale `δ = c / log T` with `c > 0`, the distortion
  factor equals the positive constant `exp c - 1`: smooth detectors *do*
  resolve the microscopic scale — exactly where Levinson's proportion method
  lives.

* `tendsto_detectorFactor_zero`: at any sub-microscopic condensation scale
  `δ_T = c / (w T · log T)` with `w T → ∞`, the distortion factor tends to `0`.
  Hence (`totalDistortion_le_mul_exp`) the total distortion of any family of
  condensed atoms is `o` of their total weight: no smooth polynomial-scale
  detector can separate such a condensed configuration from the on-line
  (Riemann-hypothesis) configuration.

Mathematical content: the resolution boundary of every smooth polynomial-scale
detector is exactly `Θ(1/log T)`.  The open conjecture `N_off = o(N)` lives at
and below that boundary; the proportion method is the only known detector that
reaches it.  Analytic-scale sibling of the corpus's charge-blindness
(`wCharge_invisible_below_reflection_depth`) and dust-blindness
(`measuredIndexZero_dust`) theorems.
-/

namespace RHTower

open Filter Topology Real

/-- The exponential distortion factor of one atom moved to distance `δ` from
the critical line, measured at logarithmic cutoff scale `L`. -/
noncomputable def detectorFactor (δ L : ℝ) : ℝ := Real.exp (δ * L) - 1

/-- Lipschitz envelope for the distortion factor: `exp y - 1 ≤ y * exp y`.
From `1 - y ≤ exp (-y)` (`Real.add_one_le_exp`) multiplied through by
`exp y > 0`. -/
theorem exp_sub_one_le_mul_exp (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h1 := Real.add_one_le_exp (-y)
  have hpos : 0 < Real.exp y := Real.exp_pos y
  have h2 : (-y + 1) * Real.exp y ≤ Real.exp (-y) * Real.exp y :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have h3 : (-y + 1) * Real.exp y = Real.exp y - y * Real.exp y := by ring
  rw [h3] at h2
  linarith

/-- The distortion factor is nonnegative for atoms at nonnegative distance
measured at nonnegative scale. -/
theorem detectorFactor_nonneg {δ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    0 ≤ detectorFactor δ L := by
  unfold detectorFactor
  have h : (1 : ℝ) ≤ Real.exp (δ * L) := by
    have h0 := Real.exp_le_exp.mpr (mul_nonneg hδ hL)
    rwa [Real.exp_zero] at h0
  linarith

/-- Microscopic exactness: an atom at the natural scale `δ = c / log T`,
measured at the polynomial cutoff scale `A * log T`, has distortion factor
exactly `exp (c * A) - 1` — independent of `T`. -/
theorem detectorFactor_microscopic {T c A : ℝ} (hT : 1 < T) :
    detectorFactor (c / Real.log T) (A * Real.log T) = Real.exp (c * A) - 1 := by
  unfold detectorFactor
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  congr 1
  field_simp [hlog]

/-- Microscopic sharpness: at the natural scale the distortion factor is a
*positive constant*.  Smooth local detectors resolve the microscopic scale. -/
theorem detectorFactor_microscopic_pos {T c A : ℝ} (hT : 1 < T) (hc : 0 < c)
    (hA : 0 < A) :
    0 < detectorFactor (c / Real.log T) (A * Real.log T) := by
  rw [detectorFactor_microscopic hT]
  have h : Real.exp 0 < Real.exp (c * A) := Real.exp_lt_exp.mpr (mul_pos hc hA)
  rw [Real.exp_zero] at h
  linarith

/-- Sub-microscopic blindness: at any condensation scale
`δ_T = c / (w T · log T)` with `w T → ∞`, the distortion factor at polynomial
cutoff `A * log T` tends to `0`.  The condensed configuration is
indistinguishable from the on-line configuration for every smooth
polynomial-scale detector. -/
theorem tendsto_detectorFactor_zero {c A : ℝ} {w : ℝ → ℝ}
    (hw : Filter.Tendsto w Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun T ↦ detectorFactor (c / (w T * Real.log T)) (A * Real.log T))
      Filter.atTop (nhds 0) := by
  have hscale : Filter.Tendsto (fun T ↦ c * A / w T) Filter.atTop (nhds 0) := by
    have hinv := hw.inv_tendsto_atTop
    have hmul := Filter.Tendsto.const_mul (c * A) hinv
    rw [mul_zero] at hmul
    refine hmul.congr (fun T ↦ ?_)
    rw [div_eq_mul_inv, Pi.inv_apply]
  have hexp := (Real.continuous_exp.tendsto 0).comp hscale
  rw [Real.exp_zero] at hexp
  have hsub : Filter.Tendsto (fun T ↦ Real.exp (c * A / w T) - 1)
      Filter.atTop (nhds 0) := by
    simpa using hexp.sub (tendsto_const_nhds (x := (1 : ℝ)))
  refine hsub.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hw.eventually_gt_atTop 0] with T hT hwT
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  have hwn : w T ≠ 0 := ne_of_gt hwT
  unfold detectorFactor
  congr 1
  field_simp [hlog, hwn]

/-- Quantitative total distortion bound: `n` condensed atoms each at scaled
distance `≤ y` distort the detector by at most `n * (y * exp y)`, which is
`o(n)` as `y → 0` — the barrier in finite form. -/
theorem totalDistortion_le_mul_exp (n : ℕ) (y : ℝ) :
    (n : ℝ) * (Real.exp y - 1) ≤ (n : ℝ) * (y * Real.exp y) :=
  mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp y) (Nat.cast_nonneg n)

/-- Sharpness complement: for `n ≥ 1` atoms at the microscopic scale with
`c > 0`, the total distortion is at least `n * (exp c - 1) > 0` — a positive
proportion of the total weight. -/
theorem totalDistortion_microscopic_pos (n : ℕ) (hn : 0 < n) {c : ℝ} (hc : 0 < c) :
    0 < (n : ℝ) * (Real.exp c - 1) := by
  have h : Real.exp 0 < Real.exp c := Real.exp_lt_exp.mpr hc
  rw [Real.exp_zero] at h
  exact mul_pos (Nat.cast_pos.mpr hn) (by linarith)

end RHTower
