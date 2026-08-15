import GaloisForLFunctions.HTGeometry.WindowedSource

/-!
# The compact box of entire sources

Coefficient sequences bounded by `(n!)⁻¹` form a countable product of closed complex balls: a
compact metrizable — hence Baire — space, every point of which is the coefficient sequence of an
entire function.  The jet-weighted series at a fixed point is a continuous function of the
coefficient sequence, by the Weierstrass `M`-test, so any condition on finitely many jets is an open
condition on the box.

This is the parameter space of a genericity argument for a source: countably many conditions, each
open and dense, meet.
-/

open Polynomial Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The compact box of coefficient sequences with factorial decay. -/
abbrev sourceBox : Type := ∀ n : ℕ, Metric.closedBall (0 : ℂ) (((n.factorial : ℝ))⁻¹)

instance : Nonempty sourceBox :=
  ⟨fun n => ⟨0, by
    rw [Metric.mem_closedBall, dist_self]
    positivity⟩⟩

/-- The coefficient sequence of a point of the box. -/
def boxSeq (c : sourceBox) : ℕ → ℂ := fun n => ((c n : ℂ))

theorem boxSeq_bound (c : sourceBox) (n : ℕ) : ‖boxSeq c n‖ ≤ ((n.factorial : ℝ))⁻¹ := by
  have hmem := (c n).2
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  exact hmem

theorem continuous_boxSeq (n : ℕ) : Continuous fun c : sourceBox => boxSeq c n := by
  exact continuous_subtype_val.comp (continuous_apply n)

/-- The jet-weighted comparison series of the box bound. -/
theorem summable_factorialInv_jet (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n : ℕ => (n : ℝ) ^ r * (((n.factorial : ℝ))⁻¹ * R ^ n) := by
  have hc : ∀ n : ℕ, ‖((((n.factorial : ℝ))⁻¹ : ℝ) : ℂ)‖ ≤ ((n.factorial : ℝ))⁻¹ := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine (summable_pow_mul_of_factorial_decay hc r hR).congr fun n => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- **The jet-weighted series at a fixed point is continuous in the coefficient sequence.** -/
theorem continuous_jetSeriesFun_box (r : ℕ) (x : ℂ) :
    Continuous fun c : sourceBox => jetSeriesFun (boxSeq c) r x := by
  refine continuous_tsum (f := fun n : ℕ => fun c : sourceBox => (n : ℂ) ^ r * boxSeq c n * x ^ n)
    (u := fun n : ℕ => (n : ℝ) ^ r * (((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n)) ?_ ?_ ?_
  · intro n
    exact (continuous_const.mul (continuous_boxSeq n)).mul continuous_const
  · exact summable_factorialInv_jet r (norm_nonneg x)
  · intro n c
    exact norm_jet_term_le r n (le_refl ‖x‖) |>.trans
      (by
        have := boxSeq_bound c n
        have hx : (0 : ℝ) ≤ ‖x‖ ^ n := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hx) (by positivity))

end

end GaloisForLFunctions.HTGeometry
