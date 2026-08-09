import GaloisForLFunctions.RHTower.XiBesselWeight

/-!
# The Dunster weight is bounded across the removable singularity

The weight `B_s(r) = (X_s(r)² - 1)^{1/4} / (r^{1/2} (X_s(r)² - s)^{3/4})` looks singular at `r = 0`,
where the numerator vanishes and so does `r`.  Dunster removes the singularity through the analytic
expansion of the endpoint coordinate.  That expansion is not needed: the corpus's two-sided bracket

`sqrt(1-s) sqrt(x²-1) <= xi_s(x) <= sqrt(x²-1)`

pins the phase to the quarter power of `x² - 1` exactly tightly enough.  The upper bracket makes the
numerator's quarter root cancel against `r^{1/2}`, and the lower bracket does the same in reverse.

The result is a two-sided bound on the compact phase range with absolute constants, holding right up
to the endpoint.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

theorem sqrt_half_mul_self : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- **The weight is bounded above, uniformly across the removable singularity.**  The upper bound
uses only the lower half of the phase bracket. -/
theorem xiBesselWeight_le_two {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    xiBesselWeight s r ≤ 2 := by
  have hx1 : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hxi : xiEndpointPhase s (xiInverse s r) = r := xiEndpointPhase_xiInverse hs0 hs1 hr
  set x : ℝ := xiInverse s r with hxdef
  have hu : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hv : (1 : ℝ) / 2 ≤ x ^ 2 - s := by nlinarith
  have hvpos : (0 : ℝ) < x ^ 2 - s := by linarith
  have hlow : Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) ≤ r := by
    have h := (xiEndpointPhase_bounds hs0 (by linarith) (le_of_lt hx1)).1
    rwa [hxi] at h
  -- the quarter root of the bracket
  have hq : Real.sqrt (Real.sqrt (1 - s)) * Real.sqrt (Real.sqrt (x ^ 2 - 1))
      ≤ Real.sqrt r := by
    rw [← Real.sqrt_mul (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hlow
  set w : ℝ := Real.sqrt (Real.sqrt (1 / 2)) with hwdef
  have hwpos : 0 < w := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have hww : w * w = Real.sqrt (1 / 2) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hws : w ≤ Real.sqrt (Real.sqrt (1 - s)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by linarith))
  have hwv : w ≤ Real.sqrt (Real.sqrt (x ^ 2 - s)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hv)
  have hsv : Real.sqrt (1 / 2) ≤ Real.sqrt (x ^ 2 - s) := Real.sqrt_le_sqrt hv
  have hupos : (0 : ℝ) < Real.sqrt (Real.sqrt (x ^ 2 - 1)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu)
  -- the denominator is at least the quarter root of the numerator times one half
  have hden : Real.sqrt (Real.sqrt (x ^ 2 - 1)) * (1 / 2)
      ≤ Real.sqrt r * Real.sqrt (x ^ 2 - s) * Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
    have hstep : Real.sqrt (Real.sqrt (x ^ 2 - 1)) * (w * Real.sqrt (1 / 2) * w)
        ≤ Real.sqrt r * Real.sqrt (x ^ 2 - s) * Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
      have h1 : Real.sqrt (Real.sqrt (x ^ 2 - 1)) * w ≤ Real.sqrt r := by
        rw [mul_comm]
        exact le_trans (mul_le_mul_of_nonneg_right hws (le_of_lt hupos)) hq
      calc Real.sqrt (Real.sqrt (x ^ 2 - 1)) * (w * Real.sqrt (1 / 2) * w)
          = (Real.sqrt (Real.sqrt (x ^ 2 - 1)) * w) * Real.sqrt (1 / 2) * w := by ring
        _ ≤ Real.sqrt r * Real.sqrt (x ^ 2 - s) * Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
            gcongr
    have hval : w * Real.sqrt (1 / 2) * w = 1 / 2 := by
      calc w * Real.sqrt (1 / 2) * w = (w * w) * Real.sqrt (1 / 2) := by ring
        _ = Real.sqrt (1 / 2) * Real.sqrt (1 / 2) := by rw [hww]
        _ = 1 / 2 := sqrt_half_mul_self
    rwa [hval] at hstep
  rw [xiBesselWeight, ← hxdef, div_le_iff₀ (by positivity)]
  nlinarith [hden, hupos]

/-- **The weight is bounded below on a compact phase range.**  This bound uses only the upper half of
the phase bracket, and again holds right up to the endpoint. -/
theorem inv_le_xiBesselWeight {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r)
    (hxle : xiInverse s r ≤ 2) :
    1 / (2 * Real.sqrt 2) ≤ xiBesselWeight s r := by
  have hx1 : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  have hxi : xiEndpointPhase s (xiInverse s r) = r := xiEndpointPhase_xiInverse hs0 hs1 hr
  set x : ℝ := xiInverse s r with hxdef
  have hu : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hvpos : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hv4 : x ^ 2 - s ≤ 4 := by nlinarith
  have hhigh : r ≤ Real.sqrt (x ^ 2 - 1) := by
    have h := (xiEndpointPhase_bounds hs0 (by linarith) (le_of_lt hx1)).2
    rwa [hxi] at h
  have hq : Real.sqrt r ≤ Real.sqrt (Real.sqrt (x ^ 2 - 1)) := Real.sqrt_le_sqrt hhigh
  have hupos : (0 : ℝ) < Real.sqrt (Real.sqrt (x ^ 2 - 1)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu)
  have hsv : Real.sqrt (x ^ 2 - s) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hv4
  have hssv : Real.sqrt (Real.sqrt (x ^ 2 - s)) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hsv
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : Real.sqrt r * Real.sqrt (x ^ 2 - s) * Real.sqrt (Real.sqrt (x ^ 2 - s))
      ≤ Real.sqrt (Real.sqrt (x ^ 2 - 1)) * (2 * Real.sqrt 2) := by
    calc Real.sqrt r * Real.sqrt (x ^ 2 - s) * Real.sqrt (Real.sqrt (x ^ 2 - s))
        ≤ Real.sqrt (Real.sqrt (x ^ 2 - 1)) * 2 * Real.sqrt 2 := by
          gcongr
      _ = Real.sqrt (Real.sqrt (x ^ 2 - 1)) * (2 * Real.sqrt 2) := by ring
  have hdpos : (0 : ℝ) < Real.sqrt r * Real.sqrt (x ^ 2 - s) * Real.sqrt (Real.sqrt (x ^ 2 - s)) :=
    by positivity
  rw [xiBesselWeight, ← hxdef, le_div_iff₀ hdpos, div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
  linarith [hden]

/-- The compact-range form of the lower bound. -/
theorem inv_le_xiBesselWeight_of_le {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r)
    (hrle : r ≤ xiEndpointPhase s 2) :
    1 / (2 * Real.sqrt 2) ≤ xiBesselWeight s r := by
  refine inv_le_xiBesselWeight hs0 hs1 hr ?_
  have h2 : (0 : ℝ) < xiEndpointPhase s 2 := by
    rw [← xiEndpointPhase_one s]
    exact strictMonoOn_xiEndpointPhase hs0 hs1 (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by norm_num))
      (by norm_num)
  have hinv : xiInverse s (xiEndpointPhase s 2) = 2 :=
    xiInverse_xiEndpointPhase hs0 hs1 (by norm_num)
  have := (strictMonoOn_xiInverse hs0 hs1).monotoneOn (mem_Ioi.mpr hr) (mem_Ioi.mpr h2) hrle
  rwa [hinv] at this


end GaloisForLFunctions.RHTower
