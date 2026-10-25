import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite geometric convolution bounds

A causal geometric average has a uniform square-sum bound at every finite horizon.
Weighted Cauchy–Schwarz supplies the local estimate; the exact recurrence telescopes
the remaining geometric weights without passing through an infinite convolution.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A finite causal convolution with powers of a real ratio. -/
def finiteGeometricConvolution (q : ℝ) (u : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ l ∈ range (M + 1), q ^ (M - l) * u l

theorem finiteGeometricConvolution_zero (q : ℝ) (u : ℕ → ℝ) :
    finiteGeometricConvolution q u 0 = u 0 := by simp [finiteGeometricConvolution]

theorem finiteGeometricConvolution_succ (q : ℝ) (u : ℕ → ℝ) (M : ℕ) :
    finiteGeometricConvolution q u (M + 1) =
      q * finiteGeometricConvolution q u M + u (M + 1) := by
  rw [finiteGeometricConvolution, sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [finiteGeometricConvolution, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  rw [show M + 1 - l = (M - l) + 1 by have := mem_range.mp hl; omega, pow_succ]
  ring

/-- The exact finite mass identity includes the surviving endpoint term. -/
theorem finiteGeometricConvolution_sum (q : ℝ) (u : ℕ → ℝ) (R : ℕ) :
    (1 - q) * (∑ M ∈ range (R + 1), finiteGeometricConvolution q u M) =
      (∑ M ∈ range (R + 1), u M) - q * finiteGeometricConvolution q u R := by
  induction R with
  | zero => simp [finiteGeometricConvolution]; ring
  | succ R ih =>
    rw [sum_range_succ (fun M => finiteGeometricConvolution q u M) (R + 1),
      sum_range_succ u (R + 1), mul_add, ih,
      finiteGeometricConvolution_succ]
    ring

private theorem finiteGeometricConvolution_mass_le (q : ℝ) (hq0 : 0 ≤ q)
    (M : ℕ) : (1 - q) * finiteGeometricConvolution q (fun _ => 1) M ≤ 1 := by
  induction M with
  | zero => rw [finiteGeometricConvolution_zero]; linarith only [hq0]
  | succ M ih =>
    rw [finiteGeometricConvolution_succ]
    have h := mul_le_mul_of_nonneg_left ih hq0
    nlinarith only [h]

/-- Weighted Cauchy–Schwarz bounds one finite geometric convolution. -/
theorem finiteGeometricConvolution_sq_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (u : ℕ → ℝ) (M : ℕ) :
    (1 - q) * finiteGeometricConvolution q u M ^ 2 ≤
      finiteGeometricConvolution q (fun l => u l ^ 2) M := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (range (M + 1))
    (r := fun l => q ^ (M - l) * u l)
    (f := fun l => q ^ (M - l))
    (g := fun l => q ^ (M - l) * u l ^ 2)
    (fun l _ => pow_nonneg hq0 _)
    (fun l _ => mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _))
    (fun l _ => le_of_eq (by ring))
  have he : (∑ l ∈ range (M + 1), q ^ (M - l)) =
      finiteGeometricConvolution q (fun _ => 1) M := by simp [finiteGeometricConvolution]
  change finiteGeometricConvolution q u M ^ 2 ≤ _ at hcs
  rw [he] at hcs
  change finiteGeometricConvolution q u M ^ 2 ≤
    finiteGeometricConvolution q (fun _ => 1) M *
      finiteGeometricConvolution q (fun l => u l ^ 2) M at hcs
  have hb : 0 ≤ finiteGeometricConvolution q (fun l => u l ^ 2) M :=
    sum_nonneg fun l _ => mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _)
  have hmass := finiteGeometricConvolution_mass_le q hq0 M
  have h1 := mul_le_mul_of_nonneg_left hcs (sub_nonneg.mpr hq1.le)
  have h2 := mul_le_mul_of_nonneg_right hmass hb
  exact h1.trans (by simpa only [mul_assoc, one_mul] using h2)

/-- The horizon-uniform finite Young bound retains the geometric operator constant. -/
theorem sum_sq_finiteGeometricConvolution_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (u : ℕ → ℝ) (R : ℕ) :
    (1 - q) ^ 2 * (∑ M ∈ range (R + 1), finiteGeometricConvolution q u M ^ 2) ≤
      ∑ M ∈ range (R + 1), u M ^ 2 := by
  have hlocal : (1 - q) *
      (∑ M ∈ range (R + 1), finiteGeometricConvolution q u M ^ 2) ≤
        ∑ M ∈ range (R + 1), finiteGeometricConvolution q (fun l => u l ^ 2) M := by
    rw [mul_sum]
    exact sum_le_sum fun M _ => finiteGeometricConvolution_sq_le q hq0 hq1 u M
  have htail : 0 ≤ q * finiteGeometricConvolution q (fun l => u l ^ 2) R :=
    mul_nonneg hq0 (sum_nonneg fun l _ => mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _))
  calc
    _ = (1 - q) * ((1 - q) *
        (∑ M ∈ range (R + 1), finiteGeometricConvolution q u M ^ 2)) := by ring
    _ ≤ (1 - q) *
        (∑ M ∈ range (R + 1), finiteGeometricConvolution q (fun l => u l ^ 2) M) :=
      mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hq1.le)
    _ = _ := finiteGeometricConvolution_sum q (fun l => u l ^ 2) R
    _ ≤ _ := sub_le_self _ htail

end GaloisForLFunctions.BiarithmeticGeometry
