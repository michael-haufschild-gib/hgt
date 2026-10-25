import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Factorial control of every logarithmic order at one common threshold is
equivalent to a power saving. Summing the factorial bounds against a geometric
weight gives the exponential estimate; the exponential series gives the converse.
-/

open Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry
set_option autoImplicit false

/-- Summing factorial bounds against a geometric weight gives an exponential bound. -/
theorem abs_mul_exp_le_of_factorial_bounds {x t A C r : ℝ}
    (ht : 0 ≤ t) (hA : 0 < A) (hr : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ q : ℕ, |x| * t ^ q ≤ C * A ^ q * (q.factorial : ℝ)) :
    |x| * Real.exp (r * t / A) ≤ C / (1 - r) := by
  have hseries : HasSum (fun q : ℕ => (r * t / A) ^ q / (q.factorial : ℝ))
      (Real.exp (r * t / A)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (r * t / A)
  have hterm (q : ℕ) : |x| * ((r * t / A) ^ q / (q.factorial : ℝ)) ≤ C * r ^ q := by
    have hfac : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    calc
      _ = (|x| * t ^ q) * ((r / A) ^ q / (q.factorial : ℝ)) := by
        rw [div_pow, mul_pow, div_pow]
        ring
      _ ≤ (C * A ^ q * (q.factorial : ℝ)) * ((r / A) ^ q / (q.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (h q) (by positivity)
      _ = _ := by
        rw [div_pow]
        field_simp [hA.ne', hfac]
  have hsum := (hseries.mul_left |x|).norm_le_of_bounded
    ((hasSum_geometric_of_lt_one hr hr1).mul_left C) (fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ |x| * ((r * t / A) ^ q / (q.factorial : ℝ)))]
      exact hterm q)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ |x| * Real.exp (r * t / A)), div_eq_mul_inv] using hsum

/-- Factorial bounds give every exponential rate strictly inside their reciprocal scale. -/
theorem abs_le_exp_neg_of_factorial_bounds {x t A C r : ℝ}
    (ht : 0 ≤ t) (hA : 0 < A) (hr : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ q : ℕ, |x| * t ^ q ≤ C * A ^ q * (q.factorial : ℝ)) :
    |x| ≤ (C / (1 - r)) * Real.exp (-(r * t / A)) := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr
    (abs_mul_exp_le_of_factorial_bounds ht hA hr hr1 h)

/-- Common factorial control of logarithmic powers gives a pointwise power saving. -/
theorem abs_le_rpow_of_log_factorial_bounds {x n A C r : ℝ}
    (hn : 1 ≤ n) (hA : 0 < A) (hr : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ q : ℕ, |x| * Real.log n ^ q ≤ C * A ^ q * (q.factorial : ℝ)) :
    |x| ≤ (C / (1 - r)) * n ^ (-r / A) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have heq : Real.exp (-(r * Real.log n / A)) = n ^ (-r / A) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  simpa only [heq] using
    abs_le_exp_neg_of_factorial_bounds (Real.log_nonneg hn) hA hr hr1 h

/-- A pointwise power bound controls all logarithmic orders at one threshold. -/
theorem log_factorial_bound_of_abs_le_rpow {x n C η : ℝ}
    (hn : 1 ≤ n) (hC : 0 ≤ C) (hη : 0 < η)
    (hx : |x| ≤ C * n ^ (-η)) (q : ℕ) :
    |x| * Real.log n ^ q ≤ C * (1 / η) ^ q * (q.factorial : ℝ) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := by exact_mod_cast q.factorial_pos
  have hpow := (div_le_iff₀ hfac).mp
    (Real.pow_div_factorial_le_exp (η * Real.log n)
      (mul_nonneg hη.le (Real.log_nonneg hn)) q)
  rw [mul_pow] at hpow
  have hlog : Real.log n ^ q ≤ (1 / η) ^ q * (q.factorial : ℝ) * Real.exp (η * Real.log n) := by
    have hdiv : Real.log n ^ q ≤ (Real.exp (η * Real.log n) * (q.factorial : ℝ)) / η ^ q :=
      (le_div_iff₀ (pow_pos hη q)).mpr (by simpa only [mul_comm] using hpow)
    refine hdiv.trans_eq ?_
    rw [div_pow, one_pow]
    ring
  have hcancel : n ^ (-η) * Real.exp (η * Real.log n) = 1 := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add,
      show Real.log n * -η + η * Real.log n = 0 by ring, Real.exp_zero]
  calc
    _ ≤ (C * n ^ (-η)) *
        ((1 / η) ^ q * (q.factorial : ℝ) * Real.exp (η * Real.log n)) :=
      mul_le_mul hx hlog (pow_nonneg (Real.log_nonneg hn) q) (by positivity)
    _ = C * (1 / η) ^ q * (q.factorial : ℝ) *
        (n ^ (-η) * Real.exp (η * Real.log n)) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- A common-threshold factorial logarithmic envelope is equivalent to a uniform power bound. -/
theorem uniform_log_factorial_bounds_iff_power_bound {ι : Type*} (f : ι → ℕ → ℝ) :
    (∃ A C : ℝ, 0 < A ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ i : ι, ∀ q : ℕ,
      |f i n| * Real.log (n : ℝ) ^ q ≤ C * A ^ q * (q.factorial : ℝ)) ↔
    (∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ i : ι,
      |f i n| ≤ C * (n : ℝ) ^ (-η)) := by
  constructor
  · rintro ⟨A, C, hA, hC, h⟩
    refine ⟨1 / (2 * A), 2 * C, by positivity, by positivity, ?_⟩
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1 i
    have hbound := abs_le_rpow_of_log_factorial_bounds (by exact_mod_cast hn1)
      hA (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) (hn i)
    rw [show -(1 / 2 : ℝ) / A = -(1 / (2 * A)) by ring] at hbound
    exact hbound.trans_eq (by ring)
  · rintro ⟨η, C, hη, hC, h⟩
    refine ⟨1 / η, C, by positivity, hC, ?_⟩
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1 i q
    exact log_factorial_bound_of_abs_le_rpow (by exact_mod_cast hn1) hC hη (hn i) q

#print axioms abs_mul_exp_le_of_factorial_bounds
#print axioms abs_le_exp_neg_of_factorial_bounds
#print axioms abs_le_rpow_of_log_factorial_bounds
#print axioms log_factorial_bound_of_abs_le_rpow
#print axioms uniform_log_factorial_bounds_iff_power_bound
end GaloisForLFunctions.HTGeometry
