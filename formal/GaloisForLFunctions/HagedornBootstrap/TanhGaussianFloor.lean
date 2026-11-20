import GaloisForLFunctions.HTGeometry.TanhSelfBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A Gaussian floor for `tanh z / z`

The strip Blaschke factors of the bootstrap zero law compare `tanh` with its argument in the
Airy window of the slit tip. The comparison is two-sided:

  `−z²/3 ≤ log(|tanh z|/|z|) ≤ 0`  for every real `z ≠ 0`,

i.e. `|z| e^{−z²/3} ≤ |tanh z| ≤ |z|`. The constant `1/3` is sharp (it is the Taylor coefficient
`tanh z = z − z³/3 + …`). The lower bound follows from the elementary inequality
`sinh u (6 − u²) ≤ 6u` for `u ≥ 0` (three differentiations reduce it to
`6u sinh u + u² cosh u ≥ 0`), which makes `log(tanh z / z) + z²/3` nondecreasing on `(0, ∞)`,
and from the cubic floor `tanh z ≥ z − z³/3`, which pins its limit at `0⁺`.
-/

noncomputable section

open Real Set Filter Topology

namespace GaloisForLFunctions.HagedornBootstrap

/-- A function vanishing at `0` with nonnegative derivative on `(0, ∞)` is nonnegative there. -/
theorem nonneg_of_hasDerivAt_of_zero {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 < x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hf y).deriv]
      exact hd y hy
  have := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hx) hx
  linarith

/-- `sinh u (6 − u²) ≤ 6u` for `u ≥ 0`. -/
theorem sinh_mul_six_sub_sq_le {u : ℝ} (hu : 0 ≤ u) : Real.sinh u * (6 - u ^ 2) ≤ 6 * u := by
  -- third derivative `6u sinh u + u² cosh u ≥ 0`
  have d3 : ∀ x, HasDerivAt (fun x => -4 * Real.sinh x + 4 * x * Real.cosh x + x ^ 2 * Real.sinh x)
      (6 * x * Real.sinh x + x ^ 2 * Real.cosh x) x := by
    intro x
    refine ((((Real.hasDerivAt_sinh x).const_mul (-4)).add
      (((hasDerivAt_id x).const_mul 4).mul (Real.hasDerivAt_cosh x))).add
      ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_sinh x))).congr_deriv ?_
    simp only [id]
    push_cast; ring
  have d2 : ∀ x, HasDerivAt (fun x => 6 - 6 * Real.cosh x + 2 * x * Real.sinh x + x ^ 2 * Real.cosh x)
      (-4 * Real.sinh x + 4 * x * Real.cosh x + x ^ 2 * Real.sinh x) x := by
    intro x
    refine (((((hasDerivAt_const x (6 : ℝ)).sub ((Real.hasDerivAt_cosh x).const_mul 6)).add
      (((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_sinh x))).add
      ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_cosh x)))).congr_deriv ?_
    simp only [id]
    push_cast; ring
  have d1 : ∀ x, HasDerivAt (fun x => 6 * x - 6 * Real.sinh x + x ^ 2 * Real.sinh x)
      (6 - 6 * Real.cosh x + 2 * x * Real.sinh x + x ^ 2 * Real.cosh x) x := by
    intro x
    refine ((((hasDerivAt_id x).const_mul 6).sub ((Real.hasDerivAt_sinh x).const_mul 6)).add
      ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_sinh x))).congr_deriv ?_
    push_cast; ring
  have h3 : ∀ x, 0 < x → 0 ≤ 6 * x * Real.sinh x + x ^ 2 * Real.cosh x := by
    intro x hx
    have := Real.sinh_pos_iff.mpr hx
    have := Real.cosh_pos x
    positivity
  have h2 := fun x (hx : 0 < x) => nonneg_of_hasDerivAt_of_zero d3 (by simp) h3 hx.le
  have h1 := fun x (hx : 0 < x) => nonneg_of_hasDerivAt_of_zero d2 (by simp) h2 hx.le
  have h0 := nonneg_of_hasDerivAt_of_zero d1 (by simp) h1 hu
  linarith

/-- The cubic floor `z − z³/3 ≤ tanh z` for `z ≥ 0`. -/
theorem sub_cube_div_three_le_tanh {z : ℝ} (hz : 0 ≤ z) : z - z ^ 3 / 3 ≤ Real.tanh z := by
  have d : ∀ x, HasDerivAt (fun x => Real.sinh x - (x - x ^ 3 / 3) * Real.cosh x)
      (x * (x * Real.cosh x - Real.sinh x) + x ^ 3 / 3 * Real.sinh x) x := by
    intro x
    refine ((Real.hasDerivAt_sinh x).sub ((((hasDerivAt_id x).sub
      ((hasDerivAt_pow 3 x).div_const 3))).mul (Real.hasDerivAt_cosh x))).congr_deriv ?_
    simp only [id, Pi.sub_apply]
    push_cast; ring
  have hq := nonneg_of_hasDerivAt_of_zero d (by simp) (fun x hx => by
    have h1 := GaloisForLFunctions.HTGeometry.sinh_le_mul_cosh hx.le
    have h2 := Real.sinh_pos_iff.mpr hx
    have : 0 ≤ x * Real.cosh x - Real.sinh x := by linarith
    positivity) hz
  rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ (Real.cosh_pos z)]
  linarith

/-- `log(tanh z / z) + z²/3`, written with `sinh` and `cosh`. -/
def tanhGaussianDefect (z : ℝ) : ℝ :=
  Real.log (Real.sinh z) - Real.log (Real.cosh z) - Real.log z + z ^ 2 / 3

theorem hasDerivAt_tanhGaussianDefect {z : ℝ} (hz : 0 < z) :
    HasDerivAt tanhGaussianDefect
      (Real.cosh z / Real.sinh z - Real.sinh z / Real.cosh z - 1 / z + 2 * z / 3) z := by
  have hs : Real.sinh z ≠ 0 := (Real.sinh_pos_iff.mpr hz).ne'
  have hc : Real.cosh z ≠ 0 := (Real.cosh_pos z).ne'
  refine (((((Real.hasDerivAt_sinh z).log hs).sub ((Real.hasDerivAt_cosh z).log hc)).sub
    (Real.hasDerivAt_log hz.ne')).add ((hasDerivAt_pow 2 z).div_const 3)).congr_deriv ?_
  push_cast; ring

theorem tanhGaussianDefect_deriv_nonneg {z : ℝ} (hz : 0 < z) :
    0 ≤ Real.cosh z / Real.sinh z - Real.sinh z / Real.cosh z - 1 / z + 2 * z / 3 := by
  have hs := Real.sinh_pos_iff.mpr hz
  have hc := Real.cosh_pos z
  have key := sinh_mul_six_sub_sq_le (show 0 ≤ 2 * z by linarith)
  rw [Real.sinh_two_mul] at key
  have hid : Real.cosh z / Real.sinh z - Real.sinh z / Real.cosh z - 1 / z + 2 * z / 3 =
      (3 * z - Real.sinh z * Real.cosh z * (3 - 2 * z ^ 2)) / (3 * z * Real.sinh z * Real.cosh z) := by
    field_simp
    have := Real.cosh_sq_sub_sinh_sq z
    nlinarith [this]
  rw [hid]
  apply div_nonneg _ (by positivity)
  nlinarith

theorem tanhGaussianDefect_monotoneOn : MonotoneOn tanhGaussianDefect (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun y hy => (hasDerivAt_tanhGaussianDefect hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact (hasDerivAt_tanhGaussianDefect hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(hasDerivAt_tanhGaussianDefect hy).deriv]
    exact tanhGaussianDefect_deriv_nonneg hy

theorem tanhGaussianDefect_eq {z : ℝ} (hz : 0 < z) :
    tanhGaussianDefect z = Real.log (Real.tanh z / z) + z ^ 2 / 3 := by
  have hs := Real.sinh_pos_iff.mpr hz
  have hc := Real.cosh_pos z
  unfold tanhGaussianDefect
  rw [Real.tanh_eq_sinh_div_cosh, Real.log_div (by positivity) hz.ne',
    Real.log_div hs.ne' hc.ne']

/-- Near `0⁺` the defect is at least `log(1 − ε²/3)`. -/
theorem log_one_sub_le_tanhGaussianDefect {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log (1 - ε ^ 2 / 3) ≤ tanhGaussianDefect ε := by
  rw [tanhGaussianDefect_eq hε]
  have hcub := sub_cube_div_three_le_tanh hε.le
  have hpos : 0 < 1 - ε ^ 2 / 3 := by nlinarith
  have hle : 1 - ε ^ 2 / 3 ≤ Real.tanh ε / ε := by
    rw [le_div_iff₀ hε]; nlinarith
  have := Real.log_le_log hpos hle
  have : 0 ≤ ε ^ 2 / 3 := by positivity
  linarith

theorem tanhGaussianDefect_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ tanhGaussianDefect z := by
  have hlim : Tendsto (fun ε : ℝ => Real.log (1 - ε ^ 2 / 3)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => Real.log (1 - ε ^ 2 / 3)) 0 := by
      apply ContinuousAt.log (by fun_prop) (by norm_num)
    have := hc.tendsto
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
      Real.log_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min z 1 by positivity)] with ε hε
  have h1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have h2 : ε ≤ z := (lt_of_lt_of_le hε.2 (min_le_left _ _)).le
  exact (log_one_sub_le_tanhGaussianDefect hε.1 h1).trans
    (tanhGaussianDefect_monotoneOn hε.1 hz h2)

/-- **Gaussian floor:** `z e^{−z²/3} ≤ tanh z` for `z ≥ 0`. -/
theorem mul_exp_le_tanh {z : ℝ} (hz : 0 ≤ z) : z * Real.exp (-(z ^ 2 / 3)) ≤ Real.tanh z := by
  rcases hz.lt_or_eq with hz | rfl
  · have h := tanhGaussianDefect_nonneg hz
    rw [tanhGaussianDefect_eq hz] at h
    have htpos : 0 < Real.tanh z / z := by
      have : 0 < Real.tanh z := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_pos (Real.sinh_pos_iff.mpr hz) (Real.cosh_pos z)
      positivity
    have : Real.exp (-(z ^ 2 / 3)) ≤ Real.tanh z / z := by
      rw [← Real.exp_log htpos]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [le_div_iff₀ hz] at this
    linarith
  · simp

/-- **The window lemma, two-sided:** `−z²/3 ≤ log(|tanh z|/|z|) ≤ 0` for real `z ≠ 0`. -/
theorem log_abs_tanh_div_bounds {z : ℝ} (hz : z ≠ 0) :
    -(z ^ 2 / 3) ≤ Real.log (|Real.tanh z| / |z|) ∧ Real.log (|Real.tanh z| / |z|) ≤ 0 := by
  have hz' : 0 < |z| := abs_pos.mpr hz
  have habs : |Real.tanh z| = Real.tanh |z| := by
    rcases le_or_gt 0 z with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg]
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr h) (Real.cosh_pos z).le
    · rw [abs_of_neg h, Real.tanh_neg, abs_of_neg]
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr h) (Real.cosh_pos z)
  rw [habs]
  have hpos : 0 < Real.tanh |z| := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hz') (Real.cosh_pos _)
  have hlow := mul_exp_le_tanh hz'.le
  have hup := GaloisForLFunctions.HTGeometry.tanh_le_self hz'.le
  rw [sq_abs] at hlow
  constructor
  · rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hz']
    linarith
  · apply Real.log_nonpos (by positivity)
    rw [div_le_one hz']
    exact hup

end GaloisForLFunctions.HagedornBootstrap
