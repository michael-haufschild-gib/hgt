import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimePowerGap
import Mathlib.Analysis.Convex.Deriv

/-!
# Eventual opposite ordinary curvatures of the actual Weil poles

The admitted square-root bound on the diagonal is dominated by the exact
exponential cross forcing beyond an explicit fixed radius. Odd chambers then
have negative ordinary second derivative, and even chambers positive second
derivative. Every Gamma fraction and the actual arithmetic diagonal are kept.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace RHTower

/-- Exact continuous forcing in the shifted pole diagonal equation. -/
def ccmWeilPoleDiagonalForcing (s : ℝ) : ℝ :=
  16*Real.cosh s-4*Real.exp (-s)-4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1)

/-- Exact continuous second derivative of the pole cross entry between entries. -/
def ccmWeilPoleCrossForcing (s : ℝ) : ℝ :=
  8*Real.cosh (2*s)+4-4/(Real.exp (2*s)-1)

/-- The literal even energy continued with one fixed arithmetic cutoff. -/
def ccmWeilEvenPoleChamber (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  2*(ccmWeilPoleChamberDiagonal a s+ccmWeilPoleChamberCross a s)

/-- A fixed explicit radius beyond which the two ordinary parity curvatures have opposite signs. -/
def ccmWeilPoleCurvatureThreshold : ℝ :=
  max 2 (Real.log (ccmWeilPoleUniformDiagonalBound+17))

/-- Elementary forcing bounds retain the exact Gamma fractions. -/
theorem ccmWeilPoleForcing_bounds {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ ccmWeilPoleDiagonalForcing s ∧
      ccmWeilPoleDiagonalForcing s ≤ 16*Real.exp s ∧
      4*Real.exp (2*s) ≤ ccmWeilPoleCrossForcing s := by
  have he4 : 9 ≤ Real.exp (4*s) := by linarith [Real.add_one_le_exp (4*s)]
  have he2 : 5 ≤ Real.exp (2*s) := by linarith [Real.add_one_le_exp (2*s)]
  have hm : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hmp := Real.exp_pos (-s)
  have hr : (1+Real.exp (4*s))/(Real.exp (4*s)-1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith : 0 < Real.exp (4*s)-1)]
    linarith
  have hg : 4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1) ≤ 8*Real.exp (-s) := by
    have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4*Real.exp (-s) by positivity)
    rw [← mul_div_assoc] at h
    nlinarith
  have hden : 0 < Real.exp (4*s)-1 := by linarith
  have hg0 : 0 ≤ 4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1) := by positivity
  have hc : Real.cosh s ≤ Real.exp s := by
    rw [Real.cosh_eq]
    have h := Real.exp_le_exp.mpr (show -s ≤ s by linarith)
    linarith
  have hfrac : 4/(Real.exp (2*s)-1) ≤ 4 := by
    rw [div_le_iff₀ (by linarith : 0 < Real.exp (2*s)-1)]
    linarith
  refine ⟨?_,?_,?_⟩
  · unfold ccmWeilPoleDiagonalForcing
    nlinarith [Real.one_le_cosh s]
  · unfold ccmWeilPoleDiagonalForcing
    nlinarith
  · unfold ccmWeilPoleCrossForcing
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(2*s))]

private theorem threshold_bounds {s : ℝ} (hs : ccmWeilPoleCurvatureThreshold ≤ s) :
    2 ≤ s ∧ ccmWeilPoleUniformDiagonalBound+17 ≤ Real.exp s := by
  have hK := ccmWeilPoleUniformDiagonalBound_pos
  have h2 := (le_max_left (2:ℝ) (Real.log (ccmWeilPoleUniformDiagonalBound+17))).trans hs
  have hl := (le_max_right (2:ℝ) (Real.log (ccmWeilPoleUniformDiagonalBound+17))).trans hs
  exact ⟨h2,(Real.log_le_iff_le_exp (by linarith)).mp hl⟩

/-- Exact ordinary second derivative of the moving odd chamber energy. -/
theorem deriv_deriv_ccmWeilOddPoleChamber_eq (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0 < s) :
    deriv (deriv (ccmWeilOddPoleChamber a)) s =
      2*(ccmWeilPoleChamberDiagonal a s+ccmWeilPoleDiagonalForcing s-ccmWeilPoleCrossForcing s) := by
  have h := deriv_deriv_ccmWeilOddPoleChamber_sub a hs
  unfold ccmWeilOddPoleChamber ccmWeilPoleDiagonalForcing ccmWeilPoleCrossForcing at *
  linarith

/-- The actual odd chamber has strictly negative ordinary curvature beyond a fixed explicit radius. -/
theorem ccmWeilOddPoleChamber_second_neg (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊)
    (hb : ccmWeilPoleCurvatureThreshold ≤ b.1) :
    deriv (deriv (ccmWeilOddPoleChamber a)) b.1 < 0 := by
  obtain ⟨hb2,hbe⟩ := threshold_bounds hb
  obtain ⟨hF0,hF,hC⟩ := ccmWeilPoleForcing_bounds hb2
  have hA := (abs_le.mp (abs_ccmWeilPoleDiagonal_le b)).2
  rw [deriv_deriv_ccmWeilOddPoleChamber_eq a b.2,
    ← ccmWeilPoleDiagonal_eq_chamber_of_floor_eq a b hf]
  have hexp : Real.exp (2*b.1) = Real.exp b.1^2 := by simpa using Real.exp_nat_mul b.1 2
  rw [hexp] at hC
  have hp := Real.exp_pos b.1
  have hm := mul_le_mul_of_nonneg_right hbe hp.le
  nlinarith [ccmWeilPoleUniformDiagonalBound_pos]

private theorem even_eq_odd_add_cross (a : SuzukiPositiveAperture) :
    ccmWeilEvenPoleChamber a = fun s => ccmWeilOddPoleChamber a s+4*ccmWeilPoleChamberCross a s := by
  funext s
  unfold ccmWeilEvenPoleChamber ccmWeilOddPoleChamber
  ring

/-- Differentiability of the complete even chamber expression at positive radii. -/
theorem differentiableAt_ccmWeilEvenPoleChamber (a : SuzukiPositiveAperture) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (ccmWeilEvenPoleChamber a) s := by
  rw [even_eq_odd_add_cross]
  exact (differentiableAt_ccmWeilOddPoleChamber a hs).add
    ((differentiableAt_ccmWeilPoleChamberCross a hs).const_mul 4)

/-- The even second derivative retains the opposite sign of the exact cross forcing. -/
theorem deriv_deriv_ccmWeilEvenPoleChamber_eq (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊)
    (hb : ccmWeilPoleCurvatureThreshold ≤ b.1) :
    deriv (deriv (ccmWeilEvenPoleChamber a)) b.1 =
      2*(ccmWeilPoleChamberDiagonal a b.1+ccmWeilPoleDiagonalForcing b.1+ccmWeilPoleCrossForcing b.1) := by
  have ho := ccmWeilOddPoleChamber_second_neg a b hf hb
  have hc : 0 < deriv (deriv (ccmWeilPoleChamberCross a)) b.1 := by
    rw [deriv_deriv_ccmWeilPoleChamberCross a b.2]
    exact lt_of_lt_of_le (by positivity) (ccmWeilPoleForcing_bounds (threshold_bounds hb).1).2.2
  have hdO := (differentiableAt_of_deriv_ne_zero ho.ne).hasDerivAt
  have hdC := (differentiableAt_of_deriv_ne_zero hc.ne').hasDerivAt
  have he : deriv (ccmWeilEvenPoleChamber a) =ᶠ[𝓝 b.1]
      (fun s => deriv (ccmWeilOddPoleChamber a) s+4*deriv (ccmWeilPoleChamberCross a) s) := by
    filter_upwards [eventually_gt_nhds b.2] with s hs
    rw [even_eq_odd_add_cross]
    exact (((differentiableAt_ccmWeilOddPoleChamber a hs).hasDerivAt).add
      (((differentiableAt_ccmWeilPoleChamberCross a hs).hasDerivAt).const_mul 4)).deriv
  rw [((hdO.add (hdC.const_mul 4)).congr_of_eventuallyEq he).deriv,
    deriv_deriv_ccmWeilOddPoleChamber_eq a b.2,deriv_deriv_ccmWeilPoleChamberCross a b.2]
  unfold ccmWeilPoleCrossForcing
  ring

/-- The actual even chamber has strictly positive ordinary curvature beyond the same radius. -/
theorem ccmWeilEvenPoleChamber_second_pos (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊)
    (hb : ccmWeilPoleCurvatureThreshold ≤ b.1) :
    0 < deriv (deriv (ccmWeilEvenPoleChamber a)) b.1 := by
  obtain ⟨hb2,hbe⟩ := threshold_bounds hb
  obtain ⟨hF0,hF,hC⟩ := ccmWeilPoleForcing_bounds hb2
  have hA := (abs_le.mp (abs_ccmWeilPoleDiagonal_le b)).1
  rw [deriv_deriv_ccmWeilEvenPoleChamber_eq a b hf hb,
    ← ccmWeilPoleDiagonal_eq_chamber_of_floor_eq a b hf]
  have hexp : Real.exp (2*b.1) = Real.exp b.1^2 := by simpa using Real.exp_nat_mul b.1 2
  rw [hexp] at hC
  have hp := Real.exp_pos b.1
  have hm := mul_le_mul_of_nonneg_right hbe hp.le
  nlinarith [ccmWeilPoleUniformDiagonalBound_pos]

end RHTower
