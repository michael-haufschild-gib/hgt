import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The half-unit seam costs a square-root power to any scalar linear extrapolator

A scalar linear extrapolator built from nonnegative shifts `ω j ≥ 0` evaluates the damped atoms
`exp (-ω j h)`, each of modulus at most one.  If some finite combination of them reproduces the
half-unit atom `exp (h/2)`, the triangle inequality forces the coefficient mass to be at least
`exp (h/2)`:

```text
∑ a j * exp (-ω j h) = exp (h/2)   ⟹   ∑ ‖a j‖ ≥ exp (h/2).
```

The bound is uniform in the number of nodes and in their placement, so growing the interpolation
order with `h` cannot help: extra nodes redistribute coefficient mass but cannot reduce it.  In the
multiplicative aperture `n = exp h` the cost is exactly `√n`.

The module also records that the estimate is **sharp** — a single node at shift zero attains it — so
the no-go is not vacuous, and that the cost is unbounded in `h`, which is the statement that no
uniform condition number exists.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology

variable {ι : Type*}

/-! ## The exact-reproduction cost -/

theorem exp_neg_shift_le_one {ω h : ℝ} (hω : 0 ≤ ω) (hh : 0 < h) :
    Real.exp (-(ω * h)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ω * h := mul_nonneg hω hh.le
  linarith

/-- The coefficient mass dominates the modulus of the reproduced value. -/
theorem norm_sum_shift_le_coefficient_mass {s : Finset ι} {ω : ι → ℝ} {a : ι → ℂ}
    (hω : ∀ j ∈ s, 0 ≤ ω j) {h : ℝ} (hh : 0 < h) :
    ‖∑ j ∈ s, a j * (Real.exp (-(ω j * h)) : ℂ)‖ ≤ ∑ j ∈ s, ‖a j‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  calc ‖a j‖ * Real.exp (-(ω j * h)) ≤ ‖a j‖ * 1 :=
        mul_le_mul_of_nonneg_left (exp_neg_shift_le_one (hω j hj) hh) (norm_nonneg _)
    _ = ‖a j‖ := mul_one _

/-- **Exact reproduction of the half-unit atom costs `exp (h/2)`.**  No dependence on the number of
nodes or on their placement. -/
theorem halfUnit_exact_cost {s : Finset ι} {ω : ι → ℝ} {a : ι → ℂ}
    (hω : ∀ j ∈ s, 0 ≤ ω j) {h : ℝ} (hh : 0 < h)
    (hrep : (∑ j ∈ s, a j * (Real.exp (-(ω j * h)) : ℂ)) = (Real.exp (h / 2) : ℂ)) :
    Real.exp (h / 2) ≤ ∑ j ∈ s, ‖a j‖ := by
  have hnorm : ‖(Real.exp (h / 2) : ℂ)‖ = Real.exp (h / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc Real.exp (h / 2) = ‖(Real.exp (h / 2) : ℂ)‖ := hnorm.symm
    _ = ‖∑ j ∈ s, a j * (Real.exp (-(ω j * h)) : ℂ)‖ := by rw [hrep]
    _ ≤ ∑ j ∈ s, ‖a j‖ := norm_sum_shift_le_coefficient_mass hω hh

/-- **Approximate reproduction costs `(1 - η) exp (h/2)`.** -/
theorem halfUnit_approx_cost {s : Finset ι} {ω : ι → ℝ} {a : ι → ℂ}
    (hω : ∀ j ∈ s, 0 ≤ ω j) {h η : ℝ} (hh : 0 < h)
    (herr : ‖(∑ j ∈ s, a j * (Real.exp (-(ω j * h)) : ℂ)) - (Real.exp (h / 2) : ℂ)‖
      ≤ η * Real.exp (h / 2)) :
    (1 - η) * Real.exp (h / 2) ≤ ∑ j ∈ s, ‖a j‖ := by
  set S : ℂ := ∑ j ∈ s, a j * (Real.exp (-(ω j * h)) : ℂ) with hS
  set E : ℂ := (Real.exp (h / 2) : ℂ) with hE
  have hnormE : ‖E‖ = Real.exp (h / 2) := by
    rw [hE, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hsplit : ‖E‖ ≤ ‖S‖ + ‖E - S‖ := by
    calc ‖E‖ = ‖S + (E - S)‖ := by rw [add_sub_cancel]
      _ ≤ ‖S‖ + ‖E - S‖ := norm_add_le _ _
  have hrev : ‖E - S‖ = ‖S - E‖ := norm_sub_rev _ _
  have hmass : ‖S‖ ≤ ∑ j ∈ s, ‖a j‖ := by
    rw [hS]; exact norm_sum_shift_le_coefficient_mass hω hh
  rw [hnormE, hrev] at hsplit
  nlinarith [hmass, hsplit, herr]

/-! ## Sharpness -/

/-- **The bound is attained.**  A single node at shift zero reproduces the half-unit atom exactly
with coefficient mass exactly `exp (h/2)`, so the estimate is sharp and the no-go is not vacuous. -/
theorem halfUnit_cost_attained (h : ℝ) :
    ∃ (ω : Unit → ℝ) (a : Unit → ℂ), (∀ j ∈ (Finset.univ : Finset Unit), 0 ≤ ω j) ∧
      (∑ j ∈ (Finset.univ : Finset Unit), a j * (Real.exp (-(ω j * h)) : ℂ))
        = (Real.exp (h / 2) : ℂ) ∧
      (∑ j ∈ (Finset.univ : Finset Unit), ‖a j‖) = Real.exp (h / 2) := by
  refine ⟨fun _ => 0, fun _ => (Real.exp (h / 2) : ℂ), fun _ _ => le_rfl, ?_, ?_⟩
  · simp
  · rw [Finset.univ_unique, Finset.sum_singleton, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]

/-! ## The multiplicative aperture form -/

theorem exp_log_div_two (n : ℝ) (hn : 0 < n) : Real.exp (Real.log n / 2) = Real.sqrt n := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
  congr 1
  ring

/-- **The square-root aperture cost.**  At multiplicative aperture `n = exp h > 1`, exact
reproduction of the half-unit atom forces coefficient mass at least `√n`. -/
theorem halfUnit_exact_cost_sqrt {s : Finset ι} {ω : ι → ℝ} {a : ι → ℂ}
    (hω : ∀ j ∈ s, 0 ≤ ω j) {n : ℝ} (hn : 1 < n)
    (hrep : (∑ j ∈ s, a j * (Real.exp (-(ω j * Real.log n)) : ℂ))
      = (Real.sqrt n : ℂ)) :
    Real.sqrt n ≤ ∑ j ∈ s, ‖a j‖ := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn
  have hsq : Real.exp (Real.log n / 2) = Real.sqrt n := exp_log_div_two n hnpos
  have hrep' : (∑ j ∈ s, a j * (Real.exp (-(ω j * Real.log n)) : ℂ))
      = (Real.exp (Real.log n / 2) : ℂ) := by rw [hrep, hsq]
  have := halfUnit_exact_cost hω hlog hrep'
  rwa [hsq] at this

/-! ## The cost is unbounded -/

/-- The half-unit cost grows without bound, so no scalar linear extrapolator has a condition number
uniform in the aperture. -/
theorem tendsto_halfUnit_cost_atTop :
    Tendsto (fun h : ℝ => Real.exp (h / 2)) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))

/-- Beyond any prescribed condition number there are apertures at which every exact scalar
extrapolator exceeds it. -/
theorem exists_aperture_halfUnit_cost_gt (C : ℝ) :
    ∀ᶠ h : ℝ in atTop, ∀ {ι : Type} (s : Finset ι) (ω : ι → ℝ) (a : ι → ℂ),
      (∀ j ∈ s, 0 ≤ ω j) → 0 < h →
      (∑ j ∈ s, a j * (Real.exp (-(ω j * h)) : ℂ)) = (Real.exp (h / 2) : ℂ) →
      C < ∑ j ∈ s, ‖a j‖ := by
  filter_upwards [tendsto_halfUnit_cost_atTop.eventually_gt_atTop C] with h hC
  intro ι s ω a hω hh hrep
  exact lt_of_lt_of_le hC (halfUnit_exact_cost hω hh hrep)

end GaloisForLFunctions.RHTower

end
