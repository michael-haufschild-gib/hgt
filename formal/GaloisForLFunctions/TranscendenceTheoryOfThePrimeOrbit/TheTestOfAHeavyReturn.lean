import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReciprocityOfReturns
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.ReturnBoundsAreLabelStatements
import GaloisForLFunctions.RHTower.JointAncestryPrimeSumOneLine
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The test of a heavy return

A fixed smooth bump `b`, equal to `1` on `[−log 8, −1/10]` and supported in
`(−log 8 − 1/20, −1/20)`, translated to `log y`, is the test `φ_y(u) = b(u − log y)` of the
reciprocity of returns. Its orbit polynomial is a smoothed sum over the prime powers in
`(y/9, y)`.

* **The test is admissible** (`contDiff_heavyTest`, `heavyTest_eq_zero_of_nonpos`,
  `heavyTest_support`): `C²`, compactly supported in `(0, log y]` for `y ≥ 9`, and its decay mass
  does not depend on `y` (`decayMass_heavyTest`).
* **The pole at `t = 0`** (`orbitPoly_heavyTest_zero_ge`). `P_{φ_y}(0) ≥ (9/50)√y` for large `y`:
  Chebyshev's `θ(x) ≥ 2x/5` on `(y/8, ye^{−1/10}]` against `θ(x) ≤ x log 4`.
* **A heavy return copies the pole** (`re_orbitPoly_heavyTest_ge`). At a `δ`-return of a
  `κ`-heavy subset of the primes `≤ y`,
  `Re P_{φ_y}(t) ≥ (1 − 2π²δ²) P_{φ_y}(0) − 2(κ(2y^{1/4} log y + 16√y) + 6 log y)`:
  the returned primes lose `2π²δ²` of their weight, the missing primes at most their weight, the
  prime powers `O(log y)` (`ψ − θ ≤ 2√y log y`).
-/

open Complex MeasureTheory Real Finset
open scoped Real

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)

/-! ## The window bump -/

theorem log_eight_gt : 2 < Real.log 8 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_gt_d9]

theorem log_eight_lt : Real.log 8 < 21 / 10 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_lt_d9]

/-- The window bump: `1` on `[−log 8, −1/10]`, supported in `(−log 8 − 1/20, −1/20)`. -/
def windowBump : ContDiffBump (-(Real.log 8 + 1 / 10) / 2 : ℝ) where
  rIn := (Real.log 8 - 1 / 10) / 2
  rOut := (Real.log 8 - 1 / 10) / 2 + 1 / 20
  rIn_pos := by linarith [log_eight_gt]
  rIn_lt_rOut := by linarith

theorem windowBump_eq_one {x : ℝ} (h1 : -Real.log 8 ≤ x) (h2 : x ≤ -(1 / 10)) :
    windowBump x = 1 := by
  apply windowBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  simp only [windowBump]
  constructor <;> linarith

theorem windowBump_support {x : ℝ} (h : windowBump x ≠ 0) :
    -Real.log 8 - 1 / 20 < x ∧ x < -(1 / 20) := by
  have hx : x ∈ Function.support windowBump := h
  rw [windowBump.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hx
  simp only [windowBump] at hx
  constructor <;> linarith [hx.1, hx.2]

/-! ## The test -/

/-- The heavy-return test at length `y`: `u ↦ b(u − log y)`. -/
def heavyTest (y : ℝ) : ℝ → ℂ := fun u => ((windowBump (u - Real.log y) : ℝ) : ℂ)

theorem contDiff_windowBump : ContDiff ℝ ⊤ (windowBump : ℝ → ℝ) := windowBump.contDiff

theorem contDiff_heavyTest (y : ℝ) : ContDiff ℝ 2 (heavyTest y) := by
  unfold heavyTest
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_windowBump.of_le le_top).comp (contDiff_id.sub contDiff_const))

theorem heavyTest_support {y : ℝ} (hy : 9 ≤ y) {u : ℝ} (h : heavyTest y u ≠ 0) :
    Real.log y - Real.log 8 - 1 / 20 < u ∧ u < Real.log y - 1 / 20 := by
  have h' : windowBump (u - Real.log y) ≠ 0 := by
    intro h0; apply h; simp [heavyTest, h0]
  have := windowBump_support h'
  constructor <;> linarith [this.1, this.2]

theorem log_nine_sub_log_eight : 1 / 20 < Real.log 9 - Real.log 8 := by
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  norm_num at h ⊢
  linarith

theorem heavyTest_eq_zero_of_nonpos {y : ℝ} (hy : 9 ≤ y) {u : ℝ} (hu : u ≤ 0) :
    heavyTest y u = 0 := by
  by_contra h
  have := (heavyTest_support hy h).1
  have h9 : Real.log 9 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  linarith [log_nine_sub_log_eight]

theorem heavyTest_abs_le {y : ℝ} (hy : 9 ≤ y) {u : ℝ} (h : heavyTest y u ≠ 0) :
    |u| ≤ Real.log y := by
  have hs := heavyTest_support hy h
  have h9 : Real.log 9 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl9 : Real.log 8 + 1 / 20 < 2 * Real.log y := by linarith [log_nine_sub_log_eight, log_eight_gt]
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

theorem hasCompactSupport_heavyTest {y : ℝ} (hy : 9 ≤ y) : HasCompactSupport (heavyTest y) :=
  hasCompactSupport_of_support_subset_abs fun u hu => heavyTest_abs_le hy hu

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
