import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Sharp sublinear rigidity for cosh doubling

A positive value propagated by doubling cannot obey a strictly sublinear
power ceiling. Exponential normalization applies this to the exact
`4 cosh(x/2)` recurrence forced by three-translate polar positivity.

The explicit repeated-pole function `x sinh(x/2)` attains the recurrence
with positive values and a linear normalized ceiling. This audits the
abstract threshold; it is not an actual arithmetic separator or a WP02
counterexample. Source-level growth and recurrence are separate obligations.

Paper: docs/reports/weil-work/results/02-exposing-ray/ONE-POLE-SUBLOG-PROOF.md.
-/

open Filter Topology
noncomputable section
namespace RHTower.ExposingRayTransfer

/-- Positive doubling cannot coexist with a strictly sublinear power ceiling. -/
theorem nonpos_of_doubling_sublinear {g : ℝ → ℝ} {β C : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hg : ∀ x : ℝ, 0 < x → g x ≤ C*(1+x)^β)
    (hd : ∀ x : ℝ, 0 < x → 0 < g x → 2*g x ≤ g (2*x))
    {x : ℝ} (hx : 0 < x) : g x ≤ 0 := by
  by_contra hn
  have hp : 0 < g x := lt_of_not_ge hn
  have hlo (n : ℕ) : (2:ℝ)^n*g x ≤ g ((2:ℝ)^n*x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0 < g ((2:ℝ)^n*x) := lt_of_lt_of_le (by positivity) ih
      have hh := (mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤2)).trans
        (hd ((2:ℝ)^n*x) (by positivity) hpos)
      simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh
  let q := (2:ℝ)^β/2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hβ1
    rw [Real.rpow_one] at hh
    linarith
  have hpower (n : ℕ) : ((2:ℝ)^n)^β = ((2:ℝ)^β)^n := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,
      Real.rpow_mul_natCast (by norm_num)]
  have hupper (n : ℕ) : g x ≤ (C*(1+x)^β)*q^n := by
    have ht : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    have he : 1+(2:ℝ)^n*x ≤ (2:ℝ)^n*(1+x) := by nlinarith only [ht]
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 1+(2:ℝ)^n*x) he hβ
    have hh := (hlo n).trans ((hg ((2:ℝ)^n*x) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hr hC))
    rw [Real.mul_rpow (by positivity) (by positivity), hpower] at hh
    have hscale : C*(((2:ℝ)^β)^n*(1+x)^β) =
        (2:ℝ)^n*((C*(1+x)^β)*q^n) := by
      dsimp [q]
      rw [div_pow]
      field_simp
    rw [hscale] at hh
    exact (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<(2:ℝ)^n)).mp hh
  have ht : Tendsto (fun n : ℕ => (C*(1+x)^β)*q^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C*(1+x)^β)
  have hh : g x ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hupper)
  exact (not_lt_of_ge hh) hp

/-- The exact cosh doubling law has no positive sublinear-exponential solution. -/
theorem nonpos_of_cosh_doubling_sublinear {d : ℝ → ℝ} {β C : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hg : ∀ x : ℝ, 0 < x → Real.exp (-x/2)*d x ≤ C*(1+x)^β)
    (hd : ∀ x : ℝ, 0 < x → 4*Real.cosh (x/2)*d x ≤ d (2*x))
    {x : ℝ} (hx : 0 < x) : d x ≤ 0 := by
  let g : ℝ → ℝ := fun x => Real.exp (-x/2)*d x
  have hgd (y : ℝ) (hy : 0 < y) (hgy : 0 < g y) : 2*g y ≤ g (2*y) := by
    have he : Real.exp (-y)*Real.exp (y/2) = Real.exp (-y/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcosh : Real.exp (-y)*(4*Real.cosh (y/2)) =
        2*Real.exp (-y/2)*(1+Real.exp (-y)) := by
      rw [Real.cosh_eq]
      rw [show -(y/2) = -y/2 by ring]
      nlinarith only [he]
    have hh := mul_le_mul_of_nonneg_left (hd y hy) (Real.exp_pos (-y)).le
    rw [← mul_assoc,hcosh] at hh
    have harg : -(2*y)/2 = -y := by ring
    dsimp [g] at hgy ⊢
    rw [harg]
    have hextra := mul_nonneg (Real.exp_pos (-y)).le hgy.le
    nlinarith only [hh,hextra]
  have hh := nonpos_of_doubling_sublinear hβ hβ1 hC hg hgd hx
  have he := Real.exp_pos (-x/2)
  nlinarith only [hh,he]

/-- Exact repeated-pole defect: the sublinear threshold cannot be replaced
by a linear ceiling for abstract cosh-doubling kernels. This is not an
arithmetic separator or an actual WP02 counterexample. -/
theorem exists_positive_linear_cosh_doubling :
    ∃ d : ℝ → ℝ,
      (∀ x : ℝ, d (2*x) = 4*Real.cosh (x/2)*d x) ∧
      (∀ x : ℝ, 0 < x → 0 < d x) ∧
      (∀ x : ℝ, 0 ≤ x → Real.exp (-x/2)*d x ≤ 1+x) := by
  refine ⟨fun x => x*Real.sinh (x/2),?_,?_,?_⟩
  · intro x
    dsimp only
    rw [show (2*x)/2=2*(x/2) by ring,Real.sinh_two_mul]
    ring
  · intro x hx
    exact mul_pos hx (Real.sinh_pos_iff.mpr (by linarith))
  · intro x hx
    dsimp only
    have he : Real.exp (-x/2)*Real.exp (x/2) = 1 := by
      rw [← Real.exp_add,show -x/2+x/2=0 by ring,Real.exp_zero]
    have hsq := sq_nonneg (Real.exp (-x/2))
    rw [Real.sinh_eq,show -(x/2) = -x/2 by ring]
    have hh : Real.exp (-x/2)*((Real.exp (x/2)-Real.exp (-x/2))/2) ≤ 1 := by
      nlinarith only [he,hsq]
    have hm := mul_le_mul_of_nonneg_left hh hx
    nlinarith only [hm]

end RHTower.ExposingRayTransfer
