import GaloisForLFunctions.RHTower.PutnamKernel

/-!
# The periodisation of Putnam's kernel

Putnam's kernel is dominated by `e^{-|x|/2}`, so its translates along the lattice `(2π/d)ℤ` are
summable at every point, and the periodisation

`D_a(x) = ∑_{k ∈ ℤ} C_a(x + 2πk/d)`

is a bounded `(2π/d)`-periodic function.  Its Fourier coefficients are the samples of the Fourier
transform of the kernel, hence exactly the normalised zeta values along the vertical progression.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- The period dual to a vertical step `d`. -/
def putnamPeriod (d : ℝ) : ℝ := 2 * Real.pi / d

theorem putnamPeriod_pos {d : ℝ} (hd : 0 < d) : 0 < putnamPeriod d := by
  rw [putnamPeriod]
  positivity

/-- Geometric summability of the lattice weights. -/
theorem summable_exp_neg_abs_int {r : ℝ} (hr : 0 < r) :
    Summable (fun k : ℤ => Real.exp (-(r * |(k : ℝ)|))) := by
  have hnat : Summable (fun k : ℕ => Real.exp (-(r * (k : ℝ)))) := by
    have hgeo : Summable (fun k : ℕ => (Real.exp (-r)) ^ k) := by
      refine summable_geometric_of_lt_one (Real.exp_pos _).le ?_
      rw [Real.exp_lt_one_iff]
      linarith
    refine hgeo.congr fun k => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun k => ?_
    congr 2
    simp
  · refine hnat.congr fun k => ?_
    congr 2
    simp

theorem summable_putnamKernel_translates {a d : ℝ} (hd : 0 < d) (x : ℝ) :
    Summable (fun k : ℤ => putnamKernel a (x + (k : ℝ) * putnamPeriod d)) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  refine Summable.of_norm_bounded
    (g := fun k : ℤ => Real.exp (|x| / 2) * Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|)))
    ((summable_exp_neg_abs_int (by positivity)).mul_left _) (fun k => ?_)
  refine le_trans (norm_putnamKernel_le a _) ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have habs : |(k : ℝ)| * putnamPeriod d - |x| ≤ |x + (k : ℝ) * putnamPeriod d| := by
    have h := abs_sub_abs_le_abs_sub ((k : ℝ) * putnamPeriod d) (-x)
    rw [abs_neg, sub_neg_eq_add] at h
    have h2 : |(k : ℝ) * putnamPeriod d| = |(k : ℝ)| * putnamPeriod d := by
      rw [abs_mul, abs_of_pos hP]
    rw [h2] at h
    calc |(k : ℝ)| * putnamPeriod d - |x| ≤ |(k : ℝ) * putnamPeriod d + x| := h
      _ = |x + (k : ℝ) * putnamPeriod d| := by rw [add_comm]
  have hnn : (0 : ℝ) ≤ putnamPeriod d := hP.le
  nlinarith [habs, abs_nonneg ((k : ℝ)), abs_nonneg x]

/-- The periodisation of Putnam's kernel. -/
def putnamPeriodization (a d : ℝ) (x : ℝ) : ℂ :=
  ∑' k : ℤ, putnamKernel a (x + (k : ℝ) * putnamPeriod d)

theorem putnamPeriodization_periodic (a d : ℝ) :
    Function.Periodic (putnamPeriodization a d) (putnamPeriod d) := by
  intro x
  rw [putnamPeriodization, putnamPeriodization]
  have hshift := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k : ℤ => putnamKernel a (x + (k : ℝ) * putnamPeriod d))
  rw [← hshift]
  refine tsum_congr fun k => ?_
  congr 1
  simp only [Equiv.coe_addRight]
  push_cast
  ring

end RHTower

end
